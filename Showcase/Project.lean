/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase.Util

/-!
# The project and its packages

What the website says about the project as a whole, read from the file system and git: the
packages that the modules come from, their versions in `lake-manifest.json`, the repository and
the commit of the source, and the configuration and the report of `lake comparator`.
-/

open Lean

namespace Showcase

/-! ## Packages -/

/-- A package that provides imported modules. -/
structure Package where
  /-- The name of the package in `lake-manifest.json`, or `lean` for the Lean toolchain. -/
  name : String
  /-- The folder of the package. -/
  dir : System.FilePath
  /-- `lean` for the toolchain, `project` for the package of the presented module, `dep` for the
  others. -/
  kind : String
  url : Option String := none
  rev : Option String := none
  inputRev : Option String := none
  /-- Whether the project requires the package itself, rather than through another package. -/
  direct : Bool := false
  /-- The `description` of its Lake configuration. -/
  description : Option String := none
  deriving Inhabited

/-- The folder of the package of a search path entry: `<package>/.lake/build/lib/lean` gives
`<package>`. -/
def packageDirOf (entry : System.FilePath) : System.FilePath :=
  let cs := entry.normalize.components
  let n := cs.length
  if n ≥ 4 && cs.drop (n - 4) == [".lake", "build", "lib", "lean"] then
    System.mkFilePath (cs.take (n - 4))
  else entry

/-- The real path of `p`, or `p` itself if it does not exist. -/
def realPath (p : System.FilePath) : IO System.FilePath := do
  try IO.FS.realPath p catch _ => return p

/-- The `description` of the Lake configuration of a package, if any. -/
def lakeDescription (dir : System.FilePath) : IO (Option String) := do
  for f in ["lakefile.toml", "lakefile.lean"] do
    let some text ← readFile? (dir / f) | continue
    for line in linesOf text do
      let t := trim line
      if !t.startsWith "description" then continue
      -- `description = "..."` or `description := "..."`
      match t.splitOn "\"" with
      | _ :: d :: _ => return if trim d == "" then none else some (trim d)
      | _ => pure ()
  return none

/-- The packages of a project, read from its `lake-manifest.json`, with the folder of each. -/
def manifestPackages (root : System.FilePath) : IO (Array Package) := do
  let some m ← readJson? (root / "lake-manifest.json") | return #[]
  let packagesDir := root / ((m.getObjValAs? String "packagesDir").toOption.getD ".lake/packages")
  let pkgs := (m.getObjValAs? (Array Json) "packages").toOption.getD #[]
  pkgs.filterMapM fun p => do
    let str (k : String) := (p.getObjValAs? String k).toOption
    let some name := str "name" | return none
    let dir := match str "type", str "dir" with
      | some "path", some d => root / d
      | _, _ => packagesDir / name
    let dir ← realPath dir
    return some { name, dir, kind := "dep", url := str "url", rev := str "rev",
                  inputRev := str "inputRev",
                  direct := !((p.getObjValAs? Bool "inherited").toOption.getD false),
                  description := ← lakeDescription dir }

/-- The names of the packages that a package requires, directly or not, from its manifest. -/
def dependenciesOf (dir : System.FilePath) : IO (Array String) := do
  let some m ← readJson? (dir / "lake-manifest.json") | return #[]
  let pkgs := (m.getObjValAs? (Array Json) "packages").toOption.getD #[]
  return pkgs.filterMap fun p => (p.getObjValAs? String "name").toOption

/-- The packages of the imported modules, by root namespace (`Mathlib`, `Init`, ...).

Each root is found in one entry of the search path. The package of an entry is the one of
`lake-manifest.json` with the same folder, the Lean toolchain for the entries of `sysroot`, and
otherwise the folder name. -/
structure PackageIndex where
  packages : Array Package
  /-- The index in `packages` of the package of each root. -/
  byRoot : Std.HashMap Name Nat

/-- The index of the packages of the roots `roots`. `projectRoot` is the root of the presented
module, whose package is the project. -/
def PackageIndex.build (roots : Array Name) (projectRoot : Name) (sysroot : System.FilePath)
    (searchPath : SearchPath) : IO PackageIndex := do
  let sysroot ← realPath sysroot
  let mut packages : Array Package := #[]
  let mut byRoot : Std.HashMap Name Nat := {}
  let mut manifest : Option (Array Package) := none
  -- the package folder of each root, project first: its manifest names the other packages
  let mut dirs : Array (Name × System.FilePath) := #[]
  for r in #[projectRoot] ++ roots.filter (· != projectRoot) do
    let s := nameStr r
    let entry? ← searchPath.findM? fun e => do
      return (← (e / s).isDir) || (← (e / (s ++ ".olean")).pathExists)
    let some entry := entry? | continue
    dirs := dirs.push (r, ← realPath (packageDirOf entry))
  for (r, dir) in dirs do
    if let some i := packages.findIdx? (·.dir == dir) then
      byRoot := byRoot.insert r i
      continue
    let pkg : Package ←
      if dir.toString.startsWith sysroot.toString then
        pure { name := "lean", dir, kind := "lean" }
      else if r == projectRoot then do
        manifest := some (← manifestPackages dir)
        pure { name := (dir.fileName.getD "project"), dir, kind := "project",
               description := ← lakeDescription dir }
      else match (manifest.getD #[]).find? (·.dir == dir) with
        | some p => pure p
        | none => pure { name := dir.fileName.getD (nameStr r), dir, kind := "dep" }
    byRoot := byRoot.insert r packages.size
    packages := packages.push pkg
  -- the packages of the manifest that no imported module comes from
  for p in manifest.getD #[] do
    if !packages.any (·.dir == p.dir) then packages := packages.push p
  return { packages, byRoot }

/-- The package of a module, if known. -/
def PackageIndex.packageOf? (idx : PackageIndex) (mod : Name) : Option Nat :=
  idx.byRoot.get? mod.getRoot

/-- The `.lean` source of a module: from the source search path, or next to the build folder of
its `.olean`. -/
def findSource? (mod : Name) : IO (Option System.FilePath) := do
  -- `findWithExt` gives the path of the module in the first entry that has its root
  if let some p ← (← getSrcSearchPath).findWithExt "lean" mod then
    if ← p.pathExists then return some p
  try
    let olean ← findOLean mod
    match olean.toString.splitOn "/.lake/build/lib/lean/" with
    | [root, rest] =>
      let some rest := dropSuffix? rest ".olean" | return none
      let p : System.FilePath := root ++ "/" ++ rest ++ ".lean"
      return if ← p.pathExists then some p else none
    | _ => return none
  catch _ => return none

/-! ## Git -/

/-- The browsable URL of a git remote: `git@host:path.git` gives `https://host/path`. -/
def browsableRemote (url : String) : String :=
  let url := (dropSuffix? url ".git").getD url
  match dropPrefix? url "git@" with
  | some rest => match splitFirst rest ":" with
    | (host, some path) => s!"https://{host}/{path}"
    | _ => url
  | none => url

/-- What the website says about the source: where to read it, and at which commit. -/
structure GitInfo where
  repository : Option String := none
  rev : Option String := none
  /-- Whether tracked files differ from the commit `rev`. -/
  dirty : Bool := false
  /-- The root of the git repository, to which the paths of the source links are relative. -/
  top : Option System.FilePath := none

/-- The git information of the folder `dir`. The given `repository` and `rev` take precedence. -/
def gitInfo (dir : System.FilePath) (repository rev : Option String) : IO GitInfo := do
  let git (args : Array String) := runCmd? "git" (#["-C", dir.toString] ++ args)
  let top ← (← git #["rev-parse", "--show-toplevel"]).mapM fun t => realPath t
  let repository ← match repository with
    | some r => pure (some r)
    | none => pure ((← git #["remote", "get-url", "origin"]).map browsableRemote)
  let (rev, dirty) ← match rev with
    | some r => pure (some r, false)
    | none => do
      let r ← git #["rev-parse", "HEAD"]
      let status ← git #["status", "--porcelain", "--untracked-files=no"]
      pure (r, status.any (· != ""))
  return { repository, rev, dirty, top }

/-! ## Comparator -/

/-- The variables that `lake exe` sets, removed for the nested `lake comparator`, which must see
the project as its own workspace. -/
def lakeEnvVars : Array String :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_SYSROOT", "LEAN_AR", "LEAN_GITHASH",
    "LEAN_RECURSION_COUNT", "LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LAKE_CACHE_DIR",
    "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS", "LAKE_NO_CACHE", "ELAN_TOOLCHAIN"]

/-- Runs `lake comparator --json` in the project `root` and writes its report to `report`. -/
def runComparator (root report : System.FilePath) (paranoid noSandbox : Bool) : IO Unit := do
  let args := #["comparator", "--json"] ++ (if paranoid then #["--paranoid"] else #[]) ++
    (if noSandbox then #["--inadvisably-no-sandbox"] else #[])
  info s!"running `lake {" ".intercalate args.toList}` in {root}"
  let out ← IO.Process.output
    { cmd := "lake", args, cwd := root, env := lakeEnvVars.map (·, none) }
  if !out.stderr.isEmpty then IO.eprint out.stderr
  -- exit codes: 0 accepted, 1 rejected (with a report), 2 could not start
  match Json.parse (trim out.stdout) with
  | .ok j =>
    IO.FS.writeFile report (j.pretty ++ "\n")
    let verdict := (j.getObjValAs? String "judgement").toOption.getD "?"
    info s!"comparator: {verdict} (report written to {report})"
  | .error _ =>
    throw <| IO.userError s!"lake comparator failed (exit code {out.exitCode}) without a JSON \
      report:\n{out.stdout}"

/-- The modules that `mod` imports, read from its source. -/
def sourceImports? (mod : Name) : IO (Option (Array Name)) := do
  let some p ← findSource? mod | return none
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile p) p.toString
  return some (imports.map (·.module))

/-- The modules that `mod` imports, directly or not, or `none` if its source is not found. Every
kind of import counts. The imports of a module loaded in `env` are read there, the others from
their source. -/
def importClosure? (env : Environment) (mod : Name) : IO (Option NameSet) := do
  let some direct ← sourceImports? mod | return none
  let mut graph : Std.HashMap Name (Array Name) := {}
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    graph := graph.insert m (d.imports.map (·.module))
  let mut seen : NameSet := {}
  let mut todo := direct
  while todo.size > 0 do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let imports ← match graph.get? m with
      | some is => pure is
      | none => pure ((← sourceImports? m).getD #[])
    todo := todo ++ imports
  return some seen

end Showcase
