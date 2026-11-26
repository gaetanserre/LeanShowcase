/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Lean
import Showcase.Text
import Showcase.Extract

/-!
# Generation of the website

`Showcase.generate` reads `showcase.md`, imports the formalization, extracts its data
(`Showcase/Extract.lean`) and writes `index.html`, the template of `assets/` with the data embedded
as JSON, with the images that `showcase.md` shows and the favicon next to it.

## The `showcase.md` file

```markdown
---
title: The mean value theorem
module: MyProject.MeanValue         # the file presented
trusted: [MyProject.Defs]           # files whose definitions the reader must check
docgen: https://example.org/docs/   # the docgen of the project, for links
---

Prose in Markdown, then a result:

{{exists_deriv_eq_slope | Theorem 1}}
```

Only `module` is required. Without any `{{...}}` line, every declaration of `module` is shown, in
the order of the file, with its module docstrings.
-/

open Lean Meta Elab

namespace Showcase

/-- The JSON of a name. -/
def nameJson (n : Name) : Json := toJson (n.toString (escape := false))

/-- The JSON of an optional string, `null` when absent. -/
def optJson (s : Option String) : Json := match s with
  | some s => toJson s
  | none => Json.null

/-- The JSON of a declaration. -/
def DeclData.json (d : DeclData) (sourceUrl : Option String) (checked : Bool) : Json :=
  Json.mkObj [
    ("name", nameJson d.name), ("display", toJson d.display), ("kind", toJson d.kind),
    ("module", nameJson d.module), ("doc", optJson d.doc),
    ("signature", Json.arr (d.signature.map fun (s, c) =>
      match c with
      | some c => Json.arr #[toJson s, nameJson c]
      | none => toJson s)),
    ("source", toJson d.source), ("statement", toJson d.statement), ("body", toJson d.body),
    ("steps", Json.arr (d.steps.map fun s =>
      Json.mkObj [("depth", toJson s.depth), ("text", toJson s.text)])),
    ("axioms", Json.arr (d.axioms.map nameJson)),
    ("uses", Json.arr (d.uses.map nameJson)),
    ("aux", Json.arr (d.aux.map nameJson)),
    ("line", toJson d.line), ("endLine", toJson d.endLine),
    ("private", toJson d.isPrivate), ("checked", toJson checked),
    ("sourceUrl", optJson sourceUrl)]

/-- The docgen page of a module. -/
def docgenPath (mod : Name) : String :=
  "/".intercalate (mod.components.map (·.toString (escape := false))) ++ ".html"

/-- Reads a JSON file, or `none` if it is missing or malformed. -/
def readJson? (p : System.FilePath) : IO (Option Json) := do
  if !(← p.pathExists) then return none
  return (Json.parse (← IO.FS.readFile p)).toOption

/-- The authors of a file, from the `Authors:` line of its header. -/
def headerAuthors (lines : Array String) : Array String := Id.run do
  for line in lines.extract 0 12 do
    let t := strip line
    if hasPrefix t "Authors:" then
      let rest := strip (dropN t 8)
      let rest := if hasSuffix rest "." then takeN rest (rest.length - 1) else rest
      return ((replaceAll rest " and " ", ").splitOn ",").toArray.map strip |>.filter (· ≠ "")
  return #[]

/-- The title (first `#` heading) and the first paragraph after it of a Markdown text. -/
def titleAndLead (md : String) : Option String × Option String := Id.run do
  let lines := splitLines md
  let mut title := none
  let mut para : Array String := #[]
  for line in lines do
    let t := strip line
    if title.isNone then
      if hasPrefix t "# " then title := some (strip (dropN t 2))
      continue
    if t == "" then
      if !para.isEmpty then break
      continue
    if hasPrefix t "#" || hasPrefix t "* " || hasPrefix t "|" then
      if !para.isEmpty then break
      continue
    para := para.push t
  return (title, if para.isEmpty then none else some (" ".intercalate para.toList))

/-- The modules that `mod` imports, read from its source, or `none` if the source is not found. -/
def sourceImports? (mod : Name) : IO (Option (Array Name)) := do
  let some p ← (try findSource mod catch _ => pure none) | return none
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile p) p.toString
  return some (imports.map (·.module))

/-- The modules that `mod` imports, directly or transitively, or `none` if its source is not found.
Every import counts (`public`, private, `meta`), so this bounds what the statements of `mod` can
depend on. The imports of a module are those of `env` when it is loaded there, those of its source
otherwise. -/
def importClosure? (env : Environment) (mod : Name) : IO (Option NameSet) := do
  let some direct ← sourceImports? mod | return none
  let mut graph : Std.HashMap Name (Array Name) := {}
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    graph := graph.insert m (d.imports.map (·.module))
  let mut seen : NameSet := {}
  let mut todo := direct
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let imports ← match graph.get? m with
      | some imports => pure imports
      | none => pure ((← sourceImports? m).getD #[])
    todo := todo ++ imports
  return some seen

/-- Options of the command line. -/
structure Options where
  /-- The file `showcase.md` that describes the website. -/
  doc : System.FilePath := "showcase.md"
  /-- The output folder, instead of the key `output` of the front matter. -/
  out : Option System.FilePath := none
  /-- Run `lake comparator --json` in the project before generating the website. -/
  comparator : Bool := false
  /-- Pass `--paranoid` to comparator: also run the external checkers of the toolchain. -/
  paranoid : Bool := true
  /-- Pass `--inadvisably-no-sandbox` to comparator, e.g. on macOS where `bwrap` does not exist. -/
  noSandbox : Bool := false

/-- The variables that `lake exe` sets for the website, removed for the nested `lake comparator`,
which must see the project as its own workspace. -/
def lakeEnvVars : Array String :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_SYSROOT", "LEAN_AR", "LEAN_GITHASH",
    "LEAN_RECURSION_COUNT", "LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LAKE_CACHE_DIR",
    "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS", "LAKE_NO_CACHE", "ELAN_TOOLCHAIN"]

/-- Runs `lake comparator --json` in the project `root` and writes its report to `report`. -/
def runComparator (opts : Options) (root report : System.FilePath) : IO Unit := do
  let args := #["comparator", "--json"] ++ (if opts.paranoid then #["--paranoid"] else #[]) ++
    (if opts.noSandbox then #["--inadvisably-no-sandbox"] else #[])
  IO.println s!"showcase: running `lake {" ".intercalate args.toList}` in {root} \
    (this rebuilds the challenge and replays every proof, it can take a while)"
  let out ← IO.Process.output
    { cmd := "lake", args, cwd := root, env := lakeEnvVars.map (·, none) }
  if !out.stderr.isEmpty then IO.eprint out.stderr
  -- Exit codes: 0 accepted, 1 rejected (with a report), 2 could not start.
  match Json.parse (strip out.stdout) with
  | .ok j =>
    IO.FS.writeFile report (j.pretty ++ "\n")
    let verdict := (j.getObjValAs? String "judgement").toOption.getD "?"
    IO.println s!"showcase: comparator verdict: {verdict} (report written to {report})"
  | .error _ =>
    throw <| IO.userError s!"lake comparator failed (exit code {out.exitCode}) \
      without a JSON report:\n{out.stdout}"

/-- Copies the file `src` to `dst`, creating the folders of `dst`. -/
def copyFile (src dst : System.FilePath) : IO Unit := do
  if let some d := dst.parent then IO.FS.createDirAll d
  IO.FS.writeBinFile dst (← IO.FS.readBinFile src)

/-- The file of the path `p` of the file `docPath` (`showcase.md`). The path must be relative, stay
in the folder of `docPath` and name an existing file. -/
def localSource (docPath : System.FilePath) (p : String) : IO System.FilePath := do
  if hasPrefix p "/" || containsSub p "://" || (p.splitOn "/").contains ".." then
    throw <| IO.userError s!"{docPath}: `{p}` must be a path relative to the folder of this \
      file, inside it"
  let src := docPath.parent.getD "." / p
  unless ← src.pathExists do
    throw <| IO.userError s!"{docPath}: cannot find the file `{p}`"
  return src

/-- The width and height of an image, from the `viewBox` of an SVG file or the header of a PNG
file, or `none` for another format. The page reserves the space of an image before loading it. -/
def imageSize? (p : System.FilePath) : IO (Option (Nat × Nat)) := do
  match p.extension.map String.toLower with
  | some "png" =>
    let b ← IO.FS.readBinFile p
    -- the chunk `IHDR`, then the width and the height, on four bytes each
    if b.size < 24 || (b.extract 12 16).data != "IHDR".toUTF8.data then return none
    let word (i : Nat) : Nat :=
      (((b[i]!.toNat * 256 + b[i + 1]!.toNat) * 256 + b[i + 2]!.toNat) * 256) + b[i + 3]!.toNat
    return some (word 16, word 20)
  | some "svg" =>
    let cs := (← IO.FS.readFile p).toList.toArray
    let pat := "viewBox=\"".toList
    let some a := findSub cs pat | return none
    let some b := findSub cs ['"'] (a + pat.length) | return none
    let nums := ((replaceAll (slice cs (a + pat.length) b) "," " ").splitOn " ").filter (· ≠ "")
    -- the integer parts are enough for the ratio of the sides
    let int (x : String) : Option Nat := ((x.splitOn ".").headD x).toNat?
    match nums with
    | [_, _, w, h] => return ((·, ·) <$> int w <*> int h).filter fun (w, h) => 0 < w && 0 < h
    | _ => return none
  | _ => return none

/-- Copies the images `images`, pairs of their path in `showcase.md` and their file, to `outDir` at
the same paths. Returns their sizes, for the page. -/
def copyImages (images : Array (String × System.FilePath)) (outDir : System.FilePath) :
    IO (Array (String × Json)) :=
  images.mapM fun (p, src) => do
    copyFile src (outDir / p)
    let size ← imageSize? src
    return (p, match size with
      | some (w, h) => toJson #[w, h]
      | none => Json.null)

/-- Copies the favicon to `outDir` and returns its elements `<link>`: the image of the key
`favicon` of the front matter, or else the icon of Showcase, from `assets`. -/
def installFavicon (fm : FrontMatter) (docPath assets outDir : System.FilePath) : IO String := do
  let links : Array (Array (String × String)) ← match fm.str? "favicon" with
    | some p => do
      copyFile (← localSource docPath p) (outDir / p)
      pure #[#[("rel", "icon"), ("href", p)]]
    | none => do
      for f in ["favicon.svg", "favicon.png", "apple-touch-icon.png"] do
        copyFile (assets / f) (outDir / f)
      pure #[#[("rel", "icon"), ("href", "favicon.png"), ("sizes", "32x32")],
        #[("rel", "icon"), ("href", "favicon.svg"), ("type", "image/svg+xml")],
        #[("rel", "apple-touch-icon"), ("href", "apple-touch-icon.png")]]
  return "\n".intercalate (links.map fun a => (Html.element "link" a .empty).render).toList

/-- Generates the website described by the file `opts.doc`. -/
def generate (opts : Options) : IO Unit := do
  let docPath ← IO.FS.realPath opts.doc
  let baseDir := docPath.parent.getD "."
  let doc := parseDoc (← IO.FS.readFile docPath)
  let fm := doc.fm
  -- The images and the favicon, checked before the long steps.
  let images ← doc.imagePaths.mapM fun p => return (p, ← localSource docPath p)
  if let some p := fm.str? "favicon" then discard <| localSource docPath p
  let some mainStr := fm.str? "module"
    | throw <| IO.userError s!"{docPath}: the front matter has no `module` key"
  let mainModule := mainStr.toName
  let trustedModules := (fm.list "trusted").map String.toName
  let resolvePath (s : String) : System.FilePath :=
    if hasPrefix s "/" then s else baseDir / s
  let sysroot ← findSysroot
  initSearchPath sysroot
  let some mainSrc ← findSource mainModule
    | throw <| IO.userError s!"cannot find the source of {mainModule}; build the project first"
  let root ← match ← findPackageRoot (← IO.FS.realPath mainSrc) with
    | some r => pure r
    | none => pure baseDir
  -- Comparator, before anything else: its report is part of the website.
  let reportPath := resolvePath ((fm.str? "comparator_report").getD "comparator-report.json")
  if opts.comparator then runComparator opts root reportPath
  -- Import the formalization.
  unsafe enableInitializersExecution
  IO.println s!"showcase: importing {mainModule}"
  let imports := (#[mainModule] ++ trustedModules).map ({ module := · } : Name → Import)
  let env ← importModules imports {} (loadExts := true) (level := .private)
  -- Packages and sources.
  let libDir := (← getLibDir sysroot).toString
  let mut origins : Std.HashMap Name String := {}
  for m in env.header.moduleNames do
    let o ← try pure (originOf libDir (← findOLean m)) catch _ => pure "lean"
    origins := origins.insert m o
  let mainOrigin := origins.getD mainModule ""
  -- The project is the package of the main module.
  let projectOrigin (o : String) : String :=
    if o == mainOrigin then "" else if o == "" then "?" else o
  origins := origins.fold (init := {}) fun acc m o => acc.insert m (projectOrigin o)
  let mut sources : Std.HashMap Name (Array String) := {}
  for (m, o) in origins.toList do
    if o != "" then continue
    if let some p ← findSource m then
      sources := sources.insert m (splitLines (← IO.FS.readFile p))
  let mainLines := sources.getD mainModule #[]
  -- Namespaces to open when printing statements and resolving names in prose.
  let mut opens : Array Name := #[]
  let mut scopedNs : Array Name := #[]
  for m in #[mainModule] ++ trustedModules do
    let ls := sources.getD m #[]
    let (o, s) := topLevelOpens ls
    opens := opens ++ o
    scopedNs := scopedNs ++ s ++ o ++ fileNamespaces ls
  let namespaces := (opens ++ scopedNs).toList.eraseDups.toArray
  -- The sources of the displayed declarations of other packages (Mathlib, ...), for their proofs.
  for b in doc.blocks do
    if let .decl s _ := b then
      if let some m := (resolveIdent env namespaces s).bind (moduleOf? env) then
        if !sources.contains m then
          if let some p ← findSource m then
            sources := sources.insert m (splitLines (← IO.FS.readFile p))
  let inp : Input := { origins, sources, opens := opens.toList.eraseDups.toArray, mainModule }
  -- Comparator.
  let comparatorPath := match fm.str? "comparator" with
    | some p => resolvePath p
    | none => root / "comparator.json"
  let comparatorCfg ← readJson? comparatorPath
  let checkedNames : NameSet := match comparatorCfg with
    | some j => match j.getObjValAs? (Array String) "theorem_names" with
      | .ok ns => ns.foldl (fun s n => s.insert n.toName) {}
      | .error _ => {}
    | none => {}
  let report ← readJson? reportPath
  let reportTime ← if report.isSome then
      pure (some (← reportPath.metadata).modified.sec) else pure none
  -- Git.
  let repository ← match fm.str? "repository" with
    | some r => pure (some r)
    | none => pure ((← runCmd? "git" #["-C", root.toString, "remote", "get-url", "origin"]).map
        httpsRemote)
  let rev ← match fm.str? "rev" with
    | some r => pure (some r)
    | none => runCmd? "git" #["-C", root.toString, "rev-parse", "HEAD"]
  -- Whether tracked files differ from the commit `rev`: the website then says so.
  let dirty := (fm.str? "rev").isNone && ((← runCmd? "git"
    #["-C", root.toString, "status", "--porcelain", "--untracked-files=no"]).any (· != ""))
  let rootStr := root.toString ++ "/"
  let mut sourcePaths : Std.HashMap Name String := {}
  for m in sources.keys do
    if let some p ← findSource m then
      let p := (← IO.FS.realPath p).toString
      let rel := if hasPrefix p rootStr then dropN p rootStr.length else p
      sourcePaths := sourcePaths.insert m rel
  -- the links to the source, for the declarations of the project only
  let sourceUrl (d : DeclData) : Option String := do
    guard (origins.get? d.module == some "")
    let repo ← repository
    let r ← rev
    let path ← sourcePaths.get? d.module
    if d.line == 0 then none
    return s!"{repo}/blob/{r}/{path}#L{d.line}-L{d.endLine}"
  -- Docgen.
  let projectDocs := fm.str? "docgen"
  let externalDocs := (fm.str? "docgen_external").getD
    "https://leanprover-community.github.io/mathlib4_docs/"
  let packageDocs := fm.map "docgen_packages"
  let withSlash (s : String) := if hasSuffix s "/" then s else s ++ "/"
  let docUrl (n : Name) : Option String := do
    if isPrivateName n then none
    let m ← moduleOf? env n
    let base ← match origins.getD m "lean" with
      | "" => projectDocs
      | o => some ((packageDocs.find? (·.1 == o)).map (·.2) |>.getD externalDocs)
    return s!"{withSlash base}{docgenPath m}#{n}"
  -- Extract the declarations.
  let ppOpts := ({} : Lean.Options).setBool `pp.unicode.fun true
  let ctx : Core.Context :=
    { fileName := "<showcase>", fileMap := default, maxHeartbeats := 0, options := ppOpts }
  let cst : Core.State := { env }
  let action : MetaM Json := do
    for ns in namespaces do activateScoped ns
    let env ← getEnv
    -- The blocks of the paper.
    let hasDirectives := doc.blocks.any (· matches .decl ..)
    let mut blocks := doc.blocks
    if !hasDirectives then
      let decls ← moduleDecls inp mainModule (includePrivate := false)
      let mdocs := (getModuleDoc? env mainModule).getD #[]
      let mut items : Array (Nat × Block) := #[]
      for h : i in [1:mdocs.size] do
        -- the first module docstring gives the title and the abstract
        let md := mdocs[i]
        items := items.push (md.declarationRange.pos.line, .md md.doc)
      for (n, r) in decls do
        items := items.push (r.range.pos.line, .decl (n.toString (escape := false)) none)
      let sorted := items.qsort (·.1 < ·.1)
      blocks := blocks ++ sorted.map (·.2)
    -- Displayed declarations, and the private lemmas their proofs use.
    let mut decls : Std.HashMap Name DeclData := {}
    let mut shown : Array Name := #[]
    let mut blockJson : Array Json := #[]
    for b in blocks do
      match b with
      | .md t => blockJson := blockJson.push (Json.mkObj [("md", toJson t)])
      | .decl s label =>
        let some n := resolveIdent env namespaces s
          | IO.eprintln s!"showcase: warning: unknown declaration `{s}`, skipped"
        blockJson := blockJson.push
          (Json.mkObj [("decl", nameJson n), ("label", optJson label)])
        if !decls.contains n then
          decls := decls.insert n (← declData inp n)
          shown := shown.push n
    let mut auxNames : Array Name := #[]
    for n in shown do
      for a in (decls.get! n).aux do
        if !decls.contains a then
          decls := decls.insert a (← declData inp a)
          auxNames := auxNames.push a
    -- Trusted definitions: those the shown statements depend on, and those of `trusted`.
    let mut usedBy : Std.HashMap Name (Array Name) := {}
    for n in shown do
      for t in ← trustedDeps inp n do
        if t == n && (decls.get! n).kind == "theorem" then continue
        usedBy := usedBy.insert t ((usedBy.getD t #[]).push n)
    -- The definitions of the main module are part of the formalization: the reader reads them with
    -- the results, so they are not listed among the definitions to trust.
    let mut trusted : NameSet := usedBy.fold (init := {}) fun s n _ =>
      if moduleOf? env n == some mainModule then s else s.insert n
    -- The statements of the challenge of comparator count too, even without a card.
    let mut challengeDeps : NameSet := {}
    for n in checkedNames.toList do
      if env.contains n then
        for t in ← trustedDeps inp n do challengeDeps := challengeDeps.insert t
    -- A definition of `trusted` that no statement uses is only used in proofs: the reader does not
    -- need to check it.
    for m in trustedModules do
      for (n, _) in ← moduleDecls inp m (includePrivate := true) do
        if let some ci := env.find? n then
          if ci matches .thmInfo _ then continue
          if usedBy.contains n || challengeDeps.contains n then
            trusted := trusted.insert n
          else
            IO.eprintln s!"showcase: warning: `{n}`, in the trusted module {m}, is used by no \
              statement and is not listed"
    for n in trusted.toArray do
      if !decls.contains n then decls := decls.insert n (← declData inp n)
    -- The extracts are only right if the sources are those that were compiled.
    let outOfSync := (decls.toList.filter fun (_, d) => !d.inSync).map (·.2.module)
    if !outOfSync.isEmpty then
      throwError "these modules changed since they were compiled, run `lake build` in the project \
        first: {", ".intercalate (outOfSync.eraseDups.map toString)}"
    -- Group the trusted definitions by module, in source order.
    let trustedMods := (trusted.toArray.filterMap (moduleOf? env ·)).toList.eraseDups.toArray
    let modOrder (m : Name) : Nat :=
      if m == mainModule then 1000000
      else (trustedModules.findIdx? (· == m)).getD 1000
    let trustedMods := trustedMods.qsort fun a b =>
      modOrder a < modOrder b || (modOrder a == modOrder b && Name.quickLt a b)
    let mut trustedJson : Array Json := #[]
    for m in trustedMods do
      let items := (trusted.toArray.filter (moduleOf? env · == some m)).qsort fun a b =>
        (decls.get! a).line < (decls.get! b).line
      let notations := if trustedModules.contains m then
        sourceNotations (sources.getD m #[]) else #[]
      trustedJson := trustedJson.push <| Json.mkObj [
        ("module", nameJson m), ("path", optJson (sourcePaths.get? m)),
        ("listed", toJson (trustedModules.contains m)),
        ("items", Json.arr (items.map fun n => Json.mkObj [
          ("name", nameJson n),
          ("usedBy", Json.arr ((usedBy.getD n #[]).map nameJson))])),
        ("notations", Json.arr (notations.map fun nt => Json.mkObj [
          ("display", toJson nt.display), ("doc", optJson nt.doc),
          ("source", toJson nt.source), ("line", toJson nt.line)]))]
    -- Axioms.
    let mut axiomUsers : Std.HashMap Name (Array Name) := {}
    -- A definition can be both displayed and trusted: count each declaration once.
    let mut counted : NameSet := {}
    for n in shown ++ trusted.toArray do
      if counted.contains n then continue
      counted := counted.insert n
      for a in (decls.get! n).axioms do
        axiomUsers := axiomUsers.insert a ((axiomUsers.getD a #[]).push n)
    -- Each axiom is shown with its declaration: its source if it is in the project (an axiom the
    -- author added), its signature otherwise.
    for (a, _) in axiomUsers.toList do
      if !decls.contains a then decls := decls.insert a (← declData inp a)
    let axiomsJson := (axiomUsers.toArray.qsort (fun a b => Name.quickLt a.1 b.1)).map
      fun (a, users) => Json.mkObj [
        ("name", nameJson a), ("module", optJson ((moduleOf? env a).map toString)),
        ("project", toJson (inp.isProject env a)),
        ("url", optJson (docUrl a)), ("usedBy", Json.arr (users.map nameJson))]
    -- Names in prose.
    let mut texts : Array String := #[]
    for b in blocks do
      if let .md t := b then texts := texts.push t
    for (_, d) in decls.toList do
      if let some t := d.doc then texts := texts.push t
    -- the named blocks of `showcase.md` cite Lean names too
    texts := texts ++ doc.named.map (·.2.2)
    if let some mds := getModuleDoc? env mainModule then
      texts := texts ++ mds.map (·.doc)
    let mut refs : Std.HashMap String Name := {}
    for t in texts do
      for s in codeSpanIdents t do
        if refs.contains s then continue
        if let some n := resolveIdent env namespaces s then refs := refs.insert s n
    -- Link targets.
    let mut targets : NameSet := {}
    for (_, d) in decls.toList do
      for (_, c) in d.signature do
        if let some c := c then targets := targets.insert c
      for u in d.uses do targets := targets.insert u
    for (_, n) in refs.toList do targets := targets.insert n
    for (n, _) in decls.toList do targets := targets.insert n
    let mut constsJson : Array (String × Json) := #[]
    -- the module of each linked constant, so that the page can name its library
    let mut constModulesJson : Array (String × Json) := #[]
    for c in targets.toArray do
      if isGenerated env c && !decls.contains c then continue
      let url := docUrl c
      if url.isNone && !decls.contains c then continue
      let key := c.toString (escape := false)
      constsJson := constsJson.push (key, optJson url)
      constModulesJson := constModulesJson.push (key, match moduleOf? env c with
        | some m => nameJson m
        | none => Json.null)
    let declsJson := decls.toList.toArray.map fun (n, d) =>
      ((n.toString (escape := false)), d.json (sourceUrl d) (checkedNames.contains n))
    -- The named blocks, by full name (or as written, e.g. a notation).
    let byName (entries : Array (String × String)) : Array (String × Json) :=
      entries.map fun (n, t) =>
        ((match resolveIdent env namespaces n with
          | some c => c.toString (escape := false)
          | none => n), toJson t)
    let namedJson := namedKinds.toList.map fun (kind, key) =>
      (key, Json.mkObj (byName (doc.ofKind kind)).toList)
    let titlesJson := byName doc.titles
    -- The main results, `Name | Label` in the front matter, shown first on the overview.
    let mut mainJson : Array Json := #[]
    for item in fm.list "main" do
      let parts := item.splitOn "|"
      let s := strip (parts.headD item)
      let label := if parts.length > 1 then some (strip ("|".intercalate (parts.drop 1))) else none
      let some n := resolveIdent env namespaces s
        | IO.eprintln s!"showcase: warning: unknown main result `{s}`, skipped"
      unless shown.contains n do
        IO.eprintln s!"showcase: warning: the main result `{s}` has no card in the results"
      mainJson := mainJson.push (Json.mkObj [("name", nameJson n), ("label", optJson label)])
    -- Module docs of the main module: the title and the abstract.
    let headerDoc := ((getModuleDoc? env mainModule).bind (·[0]?)).map (·.doc)
    let (docTitle, docLead) := (headerDoc.map titleAndLead).getD (none, none)
    return Json.mkObj <| namedJson ++ [
      ("main", Json.arr mainJson),
      ("blocks", Json.arr blockJson),
      ("shown", Json.arr (shown.map nameJson)),
      ("aux", Json.arr (auxNames.map nameJson)),
      ("decls", Json.mkObj declsJson.toList),
      ("trusted", Json.arr trustedJson),
      ("axioms", Json.arr axiomsJson),
      ("refs", Json.mkObj (refs.toList.map fun (s, n) => (s, nameJson n))),
      ("consts", Json.mkObj constsJson.toList),
      ("constModules", Json.mkObj constModulesJson.toList),
      ("titles", Json.mkObj titlesJson.toList),
      ("docTitle", optJson docTitle), ("docLead", optJson docLead)]
  let (data, _) ← (action.run' {} {}).toIO ctx cst
  -- Libraries.
  let manifest ← readJson? (root / "lake-manifest.json")
  let mut moduleCounts : Std.HashMap String Nat := {}
  for (_, o) in origins.toList do
    moduleCounts := moduleCounts.insert o (moduleCounts.getD o 0 + 1)
  -- The modules that the challenge of comparator imports, by package. Comparator checks the
  -- statements of the formalization against those of the challenge and replays its proofs, so a
  -- library that only the proofs import is checked, not trusted.
  let challengeModule : Option Name := comparatorCfg.bind fun j =>
    (j.getObjValAs? String "challenge_module").toOption.map String.toName
  let challengeImports ← match challengeModule with
    | some c => do
      let r ← importClosure? env c
      if r.isNone then
        IO.eprintln s!"showcase: warning: cannot find the source of the challenge {c}, every \
          imported library is shown as trusted"
      pure r
    | none => pure none
  let challengeCounts ← challengeImports.mapM fun ms => do
    let mut counts : Std.HashMap String Nat := {}
    for m in ms.toArray do
      let o ← match origins.get? m with
        | some o => pure o
        | none => do
          let o ← try pure (originOf libDir (← findOLean m)) catch _ => pure "lean"
          pure (projectOrigin o)
      counts := counts.insert o (counts.getD o 0 + 1)
    return counts
  let challenge := if challengeCounts.isSome then challengeModule else none
  let descriptions := fm.map "libraries"
  -- The dependencies of Mathlib (Batteries, Aesop, ...) come with it: the website does not list
  -- them on their own.
  let packagesDir := root / ((manifest.bind fun m =>
    (m.getObjValAs? String "packagesDir").toOption).getD ".lake/packages")
  let mathlibManifest ← readJson? (packagesDir / "mathlib" / "lake-manifest.json")
  let mathlibPkgs : Array Json := match mathlibManifest with
    | some j => (j.getObjValAs? (Array Json) "packages").toOption.getD #[]
    | none => #[]
  let mathlibDeps : Array String :=
    mathlibPkgs.filterMap fun p => (p.getObjValAs? String "name").toOption
  let mut libs : Array Json := #[]
  if let some man := manifest then
    if let .ok pkgs := man.getObjValAs? (Array Json) "packages" then
      for p in pkgs do
        let name := (p.getObjValAs? String "name").toOption.getD "?"
        libs := libs.push <| Json.mkObj [
          ("partOf", if name != "mathlib" && mathlibDeps.contains name then toJson "mathlib"
            else Json.null),
          ("name", toJson name),
          ("url", optJson (p.getObjValAs? String "url").toOption),
          ("rev", optJson (p.getObjValAs? String "rev").toOption),
          ("inputRev", optJson (p.getObjValAs? String "inputRev").toOption),
          ("direct", toJson !((p.getObjValAs? Bool "inherited").toOption.getD false)),
          ("modules", toJson (moduleCounts.getD name 0)),
          ("challengeModules", toJson (challengeCounts.map (·.getD name 0))),
          ("description", optJson ((descriptions.find? (·.1 == name)).map (·.2)))]
  let toolchain ← do
    let p := root / "lean-toolchain"
    if ← p.pathExists then pure (some (strip (← IO.FS.readFile p))) else pure none
  -- Bibliography.
  let bib ← match fm.str? "bibliography" with
    | some p => do
      let p := resolvePath p
      if ← p.pathExists then pure (some (← IO.FS.readFile p)) else pure none
    | none => pure none
  let docTitle := (data.getObjValAs? String "docTitle").toOption
  let docLead := (data.getObjValAs? String "docLead").toOption
  let authors := if (fm.list "authors").isEmpty then headerAuthors mainLines else fm.list "authors"
  let metaJson := Json.mkObj [
    ("title", optJson ((fm.str? "title").orElse fun _ => docTitle)),
    ("subtitle", optJson (fm.str? "subtitle")),
    ("authors", toJson authors),
    ("abstract", optJson ((fm.str? "abstract").orElse fun _ => docLead)),
    ("paper", optJson (fm.str? "paper")), ("paperUrl", optJson (fm.str? "paper_url")),
    ("repository", optJson repository), ("rev", optJson rev), ("dirty", toJson dirty),
    ("module", nameJson mainModule), ("modulePath", optJson (sourcePaths.get? mainModule)),
    ("docgen", optJson projectDocs),
    ("lean", toJson Lean.versionString), ("toolchain", optJson toolchain),
    ("coreModules", toJson (moduleCounts.getD "lean" 0)),
    ("projectModules", toJson (moduleCounts.getD "" 0)),
    ("challenge", match challenge with | some c => nameJson c | none => Json.null),
    ("challengeCoreModules", toJson (challengeCounts.map (·.getD "lean" 0))),
    ("challengeProjectModules", toJson (challengeCounts.map (·.getD "" 0))),
    ("links", Json.mkObj ((fm.map "links").toList.map fun (k, v) => (k, toJson v))),
    ("axiomDocs", Json.mkObj ((fm.map "axioms").toList.map fun (k, v) => (k, toJson v)))]
  let comparatorJson := Json.mkObj [
    ("config", comparatorCfg.getD Json.null),
    ("report", report.getD Json.null),
    ("reportTime", match reportTime with | some t => toJson t | none => Json.null)]
  let assets ← match ← IO.getEnv "SHOWCASE_ASSETS" with
    | some a => pure (System.FilePath.mk a)
    | none => do
      let app ← IO.appPath
      -- `<package>/.lake/build/bin/showcase`
      pure ((app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)).getD "." /
        "assets")
  let outDir := opts.out.getD (resolvePath ((fm.str? "output").getD "_site"))
  IO.FS.createDirAll outDir
  -- The files of the page, next to it: the images and the favicon.
  let media ← copyImages images outDir
  let favicon ← installFavicon fm docPath assets outDir
  let site := data.mergeObj (Json.mkObj [
    ("meta", metaJson), ("libraries", Json.arr libs), ("comparator", comparatorJson),
    ("bibliography", optJson bib), ("media", Json.mkObj media.toList)])
  -- Write the page.
  let template ← IO.FS.readFile (assets / "template.html")
  let style ← IO.FS.readFile (assets / "style.css")
  let script ← IO.FS.readFile (assets / "app.js")
  let title := ((fm.str? "title").orElse fun _ => docTitle).getD (toString mainModule)
  let dataStr := replaceAll site.compress "</" "<\\/"
  let html := template
    |> (replaceAll · "{{TITLE}}" title)
    |> (replaceAll · "{{FAVICON}}" favicon)
    |> (replaceAll · "/*{{STYLE}}*/" style)
    |> (replaceAll · "/*{{SCRIPT}}*/" script)
    |> (replaceAll · "{{DATA}}" dataStr)
  IO.FS.writeFile (outDir / "index.html") html
  IO.println s!"showcase: wrote {outDir / "index.html"} ({(html.utf8ByteSize + 512) / 1024} KiB)"

end Showcase
