/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase.Collect

/-!
# Generation of the website

`Showcase.generate` reads `showcase.md`, imports the formalization, collects what the website shows
and writes `index.html`: the page of `assets/` with the data embedded as JSON, and the images and
the favicon next to it.

The JSON has a table of the modules and a table of the linked constants, and refers to them by
index, so that each name and each URL is written once.
-/

open Lean Meta

namespace Showcase

/-- The options of the command line. -/
structure Options where
  /-- The file that describes the website. -/
  doc : System.FilePath := "showcase.md"
  /-- The output folder, instead of the key `output`. -/
  out : Option System.FilePath := none
  /-- The module to present, instead of the key `module`. -/
  module : Option String := none
  /-- Run `lake comparator` first. -/
  comparator : Bool := false
  /-- Pass `--paranoid` to comparator. -/
  paranoid : Bool := true
  /-- Pass `--inadvisably-no-sandbox` to comparator, e.g. on macOS. -/
  noSandbox : Bool := false

/-! ## Inputs -/

/-- The file of a path written in `showcase.md`: relative, inside the folder of `showcase.md`, and
existing. -/
def localFile (baseDir : System.FilePath) (p : String) : IO System.FilePath := do
  if p.startsWith "/" || p.contains "://" || (p.splitOn "/").contains ".." then
    throw <| IO.userError s!"`{p}` must be a path relative to the folder of showcase.md, inside it"
  let f := baseDir / p
  unless ← f.pathExists do
    throw <| IO.userError s!"cannot find the file `{p}` (relative to {baseDir})"
  return f

/-- The width and the height of an SVG or PNG image, so that the page keeps its place while it
loads. -/
def imageSize? (p : System.FilePath) : IO (Option (Nat × Nat)) := do
  match p.extension.map String.toLower with
  | some "png" =>
    let b ← IO.FS.readBinFile p
    -- the chunk `IHDR`, then the width and the height, on four bytes each
    if b.size < 24 then return none
    let word (i : Nat) : Nat := (List.range 4).foldl (fun acc k => acc * 256 + b[i + k]!.toNat) 0
    return some (word 16, word 20)
  | some "svg" =>
    let some rest := (splitFirst (← IO.FS.readFile p) "viewBox=\"").2 | return none
    let nums := (((splitFirst rest "\"").1.replace "," " ").splitOn " ").filter (· ≠ "")
    let int (x : String) : Option Nat := (splitFirst x ".").1.toNat?
    match nums with
    | [_, _, w, h] => return do
      let w ← int w
      let h ← int h
      guard (w > 0 && h > 0)
      return (w, h)
    | _ => return none
  | _ => return none

/-- The authors of a file, from the `Authors:` line of its header. -/
def headerAuthors (lines : Array String) : Array String := Id.run do
  for line in lines.extract 0 15 do
    if let some rest := dropPrefix? (trim line) "Authors:" then
      let rest := (dropSuffix? (trim rest) ".").getD (trim rest)
      return ((rest.replace " and " ", ").splitOn ",").toArray.map trim |>.filter (· ≠ "")
  return #[]

/-- The options of the pretty-printer: `pp.unicode.fun`, and the `pp` options of the
`[leanOptions]` of the project. -/
def projectOptions (root : System.FilePath) : IO Lean.Options := do
  let mut o : Lean.Options := ({} : Lean.Options).setBool `pp.unicode.fun true
  let some text ← readFile? (root / "lakefile.toml") | return o
  let mut inSection := false
  for line in linesOf text do
    let l := stripComment line
    if l.startsWith "[" then
      inSection := l == "[leanOptions]"
      continue
    let (k, some v) := splitFirst l "=" | continue
    let (k, v) := (trim k, trim v)
    if !inSection || !k.startsWith "pp." then continue
    if v == "true" || v == "false" then o := o.setBool k.toName (v == "true")
  return o

/-- The folder of the assets: `SHOWCASE_ASSETS`, or `assets` in the package of the executable,
`<package>/.lake/build/bin/showcase`. -/
def assetsDir : IO System.FilePath := do
  if let some a ← IO.getEnv "SHOWCASE_ASSETS" then return a
  let app ← IO.appPath
  let pkg := (app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)).getD "."
  return pkg / "assets"

/-- The scripts of the page, in order. They share one scope. -/
def scripts : List String := ["util.js", "markdown.js", "lean.js", "maps.js", "pages.js", "main.js"]

/-! ## JSON -/

/-- The tables of the modules and of the linked constants. -/
structure Tables where
  modules : Array Name := #[]
  moduleIdx : Std.HashMap Name Nat := {}
  consts : Array (Name × Option Nat) := #[]
  constIdx : Std.HashMap Name Nat := {}

/-- The index of a module in the tables. -/
def moduleRef (m : Name) : StateM Tables Nat := do
  if let some i := (← get).moduleIdx.get? m then return i
  modifyGet fun t =>
    (t.modules.size, { t with modules := t.modules.push m,
                              moduleIdx := t.moduleIdx.insert m t.modules.size })

/-- The index of a constant in the tables. -/
def constRef (env : Environment) (c : Name) : StateM Tables Json := do
  if let some i := (← get).constIdx.get? c then return toJson i
  let m ← (moduleOf? env c).mapM moduleRef
  modifyGet fun t =>
    (toJson t.consts.size, { t with consts := t.consts.push (c, m),
                                    constIdx := t.constIdx.insert c t.consts.size })

/-- The JSON of a list of names. -/
def namesJson (ns : Array Name) : Json := .arr (ns.map jsonName)

/-- The JSON of a declaration. -/
def declJson (env : Environment) (c : Collected) (checked : NameSet) (d : DeclData) :
    StateM Tables Json := do
  let sig ← d.signature.mapM fun (s, k) => match k with
    | some k => return Json.arr #[s, ← constRef env k]
    | none => return Json.str s
  let links ← d.links.mapM fun (id, k) => return (id, ← constRef env k)
  let list (ns : Array Name) : Json := if ns.isEmpty then .null else namesJson ns
  return jsonObj [
    ("kind", d.kind), ("mod", toJson (← moduleRef d.module)), ("doc", jsonOpt d.doc),
    ("display", if isPrivateName d.name then jsonName (userName d.name) else .null),
    ("sig", .arr sig), ("src", d.source), ("line", d.line), ("end", d.endLine),
    ("comments", if d.comments.isEmpty then .null else
      .arr (d.comments.map fun (k, t) => .arr #[toJson k, .str t])),
    ("links", if links.isEmpty then .null else Json.mkObj links.toList),
    ("axioms", list (c.axioms.getD d.name #[])),
    ("aux", list (c.aux.getD d.name #[])), ("uses", list (c.uses.getD d.name #[])),
    ("checked", if checked.contains d.name then true else .null)]

/-! ## Generation -/

/-- Generates the website described by `opts`. -/
def generate (opts : Options) : IO Unit := do
  let t0 ← IO.monoMsNow
  -- `showcase.md`, which only `--module` makes optional
  let docPath? ← if ← opts.doc.pathExists then some <$> IO.FS.realPath opts.doc else pure none
  if docPath?.isNone && opts.module.isNone then
    throw <| IO.userError s!"cannot find {opts.doc}; write it, or name the module to present \
      with --module"
  let doc ← match docPath? with
    | some p => pure (parseDoc (← IO.FS.readFile p))
    | none => pure {}
  let fm := doc.fm
  let baseDir ← match docPath?.bind (·.parent) with
    | some d => pure d
    | none => IO.currentDir
  let resolvePath (s : String) : System.FilePath := if s.startsWith "/" then s else baseDir / s
  let modules := (match opts.module with
    | some m => #[m]
    | none => fm.list "module").map String.toName
  if modules.isEmpty then
    throw <| IO.userError s!"{opts.doc}: the front matter has no `module` key"
  let trustedModules := (fm.list "trusted").map String.toName
  -- the images and the favicon, checked before the long steps
  let images ← doc.images.mapM fun p => return (p, ← localFile baseDir p)
  let favicon ← (fm.str? "favicon").mapM fun p => return (p, ← localFile baseDir p)
  -- The project, from the search path that `lake exe` sets.
  let sysroot ← findSysroot
  initSearchPath sysroot
  for m in modules do
    if (← findSource? m).isNone then
      throw <| IO.userError s!"cannot find the module {m}: check its name, and build the project \
        with `lake build`"
  let searchPath ← searchPathRef.get
  let projectEntry ← searchPath.findM? fun e => do
    let s := nameStr modules[0]!.getRoot
    return (← (e / s).isDir) || (← (e / (s ++ ".olean")).pathExists)
  let root ← realPath (packageDirOf (projectEntry.getD baseDir))
  -- Comparator, before the import: it rebuilds the project.
  let reportPath := resolvePath ((fm.str? "comparator_report").getD "comparator-report.json")
  if opts.comparator then runComparator root reportPath opts.paranoid opts.noSandbox
  let cmpConfig ← readJson? (match fm.str? "comparator" with
    | some p => resolvePath p
    | none => root / "comparator.json")
  let checked : NameSet := ((cmpConfig.bind fun j =>
    (j.getObjValAs? (Array String) "theorem_names").toOption).getD #[]).foldl
      (fun s n => s.insert n.toName) {}
  let report ← readJson? reportPath
  let reportTime ← if report.isSome then
    pure (some (← reportPath.metadata).modified.sec) else pure none
  -- The import.
  unsafe enableInitializersExecution
  info s!"importing {", ".intercalate (modules.map nameStr).toList}"
  -- `leakEnv` spares the reference counting of the environment, which lives until the end
  let env ← importModules ((modules ++ trustedModules).map ({ module := · })) {}
    (loadExts := true) (leakEnv := true)
  let roots := (env.header.moduleNames.foldl (·.insert ·.getRoot) ({} : NameSet)).toArray
  let index ← PackageIndex.build roots modules[0]!.getRoot sysroot searchPath
  let some project := index.packages.findIdx? (·.kind == "project")
    | throw <| IO.userError "cannot find the package of the project"
  -- reviewed: Lean, Mathlib and its dependencies, and the packages of the key `reviewed`
  let mathlibDeps ← match index.packages.find? (·.name == "mathlib") with
    | some p => dependenciesOf p.dir
    | none => pure #[]
  let reviewedNames := #["mathlib"] ++ mathlibDeps ++ fm.list "reviewed"
  let reviewed := (Array.range index.packages.size).filter fun i =>
    index.packages[i]!.kind == "lean" || reviewedNames.contains index.packages[i]!.name
  let ctx : Ctx := { packages := index, project, reviewed, lines := ← IO.mkRef {},
                     scopes := ← IO.mkRef {} }
  let coreCtx : Core.Context := { fileName := "<showcase>", fileMap := default,
                                  maxHeartbeats := 0, options := ← projectOptions root }
  let (c, _) ← ((collect ctx doc modules trustedModules checked).run' {} {}).toIO coreCtx { env }
  -- The source: its repository and its commit.
  let git ← gitInfo root (fm.str? "repository") (fm.str? "rev")
  let docsOf (p : Package) : Option String := do
    let withSlash (s : String) := if s.endsWith "/" then s else s ++ "/"
    if p.kind == "project" then return withSlash (← fm.str? "docgen")
    if let some (_, u) := (fm.map "docgen_packages").find? (·.1 == p.name) then
      return withSlash u
    if let some u := fm.str? "docgen_external" then return withSlash u
    guard (reviewed.any fun i => index.packages[i]!.name == p.name)
    return "https://leanprover-community.github.io/mathlib4_docs/"
  -- the browsable source of a module of the project, or of a package with a URL
  let sourceUrl (m : Name) : IO (Option String) := do
    let some pi := index.packageOf? m | return none
    let p := index.packages[pi]!
    let some file ← findSource? m | return none
    let file := (← realPath file).toString
    if p.kind == "project" then
      let (some repo, some rev) := (git.repository, git.rev) | return none
      let top := (git.top.getD root).toString ++ "/"
      return (dropPrefix? file top).map fun rel => s!"{repo}/blob/{rev}/{rel}"
    let (some url, some rev) := (p.url, p.rev) | return none
    if !url.startsWith "https://" then return none
    return (dropPrefix? file (p.dir.toString ++ "/")).map fun rel =>
      s!"{(dropSuffix? url ".git").getD url}/blob/{rev}/{rel}"
  -- Module counts, for the libraries: all the imported modules, and those of the challenge of
  -- comparator, which the statements import.
  let count (ms : Array Name) : Std.HashMap Nat Nat := ms.foldl (init := {}) fun acc m =>
    match index.packageOf? m with
    | some i => acc.insert i (acc.getD i 0 + 1)
    | none => acc
  let imported := count env.header.moduleNames
  let challenge := cmpConfig.bind fun j =>
    (j.getObjValAs? String "challenge_module").toOption.map String.toName
  let challengeImports ← match challenge with
    | some ch => do
      let r ← importClosure? env ch
      if r.isNone then warn s!"cannot find the source of the challenge {ch}: every library is \
        shown as used by the statements"
      pure (r.map fun s => count s.toArray)
    | none => pure none
  let descriptions := fm.map "libraries"
  let packagesJson := (Array.range index.packages.size).map fun i =>
    let p := index.packages[i]!
    let label := if p.kind == "lean" then "Lean" else
      -- the root namespace with the most modules, e.g. `Mathlib` for `mathlib`
      let rs := index.byRoot.toArray.filter (·.2 == i) |>.map (·.1)
      let byCount := rs.map fun r => (r, (env.header.moduleNames.filter (·.getRoot == r)).size)
      ((byCount.qsort (·.2 > ·.2))[0]?.map (nameStr ·.1)).getD p.name
    jsonObj [
      ("name", p.name), ("label", label),
      -- the dependencies of Mathlib come with it
      ("partOf", if p.name != "mathlib" && mathlibDeps.contains p.name then "mathlib" else .null),
      ("kind", if p.kind == "dep" && reviewed.contains i then "reviewed" else p.kind),
      ("url", jsonOpt ((p.url.map fun u => (dropSuffix? u ".git").getD u))),
      ("rev", jsonOpt p.rev), ("inputRev", jsonOpt p.inputRev), ("direct", p.direct),
      ("description", jsonOpt ((descriptions.find? (·.1 == p.name)).map (·.2))),
      ("lakeDescription", jsonOpt p.description),
      ("docs", jsonOpt (docsOf p)), ("modules", imported.getD i 0),
      ("statementModules", match challengeImports with
        | some cs => toJson (cs.getD i 0)
        | none => .null)]
  -- The declarations and the tables.
  let declsJson : StateM Tables (List (String × Json)) := c.decls.toList.mapM fun (n, d) =>
    return (nameStr n, ← declJson env c checked d)
  let rest : StateM Tables (Json × Json) := do
    let refs ← c.refs.mapM fun (s, n) => return (s, ← constRef env n)
    let trusted ← c.trusted.mapM fun (m, ns) =>
      return jsonObj [("mod", toJson (← moduleRef m)), ("items", namesJson ns)]
    let notations ← c.notations.mapM fun n => return jsonObj [
      ("pattern", jsonOpt n.pattern), ("doc", jsonOpt n.doc), ("src", n.source),
      ("mod", toJson (← moduleRef n.module)), ("line", n.line), ("end", n.endLine)]
    let axioms ← c.axiomUsers.mapM fun (a, users) => return jsonObj [
      ("name", jsonName a), ("const", ← constRef env a), ("users", namesJson users)]
    return (Json.mkObj refs.toList, jsonObj [("groups", .arr trusted),
      ("notations", .arr notations), ("axioms", .arr axioms)])
  let ((decls, refs, trust), tables) := (do
    let d ← declsJson
    let (r, t) ← rest
    return (d, r, t)).run {}
  let modulesJson ← tables.modules.mapM fun m => do
    return Json.arr #[jsonName m, (index.packageOf? m).map toJson |>.getD .null,
      jsonOpt (← sourceUrl m)]
  let constsJson := tables.consts.map fun (n, m) =>
    Json.arr #[jsonName n, (m.map toJson).getD .null]
  -- The notes, by full name.
  let notes := noteKinds.map fun k =>
    (k, Json.mkObj ((c.notes.filter (·.1.kind == k)).map fun (n, key) =>
      (key, Json.str n.text)).toList)
  let titles := c.notes.filterMap fun (n, key) => n.title.map (key, Json.str ·)
  -- The front page.
  let mainLines ← ctx.sourceLines modules[0]!
  let authors := if (fm.list "authors").isEmpty then headerAuthors mainLines else fm.list "authors"
  let title := ((fm.str? "title").orElse fun _ => c.title).getD (nameStr modules[0]!)
  let toolchain ← readFile? (root / "lean-toolchain")
  let bibliography ← (fm.str? "bibliography").bindM fun p => readFile? (resolvePath p)
  if (fm.str? "bibliography").isSome && bibliography.isNone then
    warn s!"cannot read the bibliography {(fm.str? "bibliography").getD ""}"
  let metaJson := jsonObj [
    ("title", title),
    ("subtitle", jsonOpt ((fm.str? "subtitle").orElse fun _ =>
      index.packages[project]!.description)),
    ("authors", toJson authors),
    ("abstract", jsonOpt ((fm.str? "abstract").orElse fun _ => c.lead)),
    ("paper", jsonOpt (fm.str? "paper")), ("paperUrl", jsonOpt (fm.str? "paper_url")),
    ("repository", jsonOpt git.repository), ("rev", jsonOpt git.rev), ("dirty", git.dirty),
    ("lean", Lean.versionString), ("toolchain", jsonOpt (toolchain.map trim)),
    ("docs", jsonOpt (fm.str? "docgen")),
    ("project", toJson project),
    ("presented", namesJson c.presented),
    ("links", Json.mkObj ((fm.map "links").toList.map fun (k, v) => (k, Json.str v))),
    ("axiomDocs", Json.mkObj ((fm.map "axioms").toList.map fun (k, v) => (k, Json.str v)))]
  -- The output folder, with the images and the favicon.
  let outDir := opts.out.getD (resolvePath ((fm.str? "output").getD "_site"))
  IO.FS.createDirAll outDir
  let media ← images.mapM fun (p, src) => do
    copyFile src (outDir / p)
    return (p, match ← imageSize? src with
      | some (w, h) => Json.arr #[w, h]
      | none => .null)
  let assets ← assetsDir
  let faviconLinks ← match favicon with
    | some (p, src) => do
      copyFile src (outDir / p)
      pure s!"<link rel=\"icon\" href=\"{p}\">"
    | none => do
      for f in ["favicon.svg", "favicon.png", "apple-touch-icon.png"] do
        copyFile (assets / f) (outDir / f)
      pure "<link rel=\"icon\" href=\"favicon.svg\" type=\"image/svg+xml\">\n\
        <link rel=\"icon\" href=\"favicon.png\" sizes=\"32x32\">\n\
        <link rel=\"apple-touch-icon\" href=\"apple-touch-icon.png\">"
  let data := jsonObj [
    ("meta", metaJson), ("packages", .arr packagesJson), ("modules", .arr modulesJson),
    ("consts", .arr constsJson), ("decls", Json.mkObj decls),
    ("blocks", .arr (c.blocks.map fun
      | .md t => jsonObj [("md", t)]
      | .decl n label => jsonObj [("decl", n), ("label", jsonOpt label)])),
    ("main", .arr (c.main.map fun (n, label) => jsonObj [("name", jsonName n),
      ("label", jsonOpt label)])),
    ("notes", Json.mkObj notes), ("titles", Json.mkObj titles.toList),
    ("refs", refs), ("trust", trust), ("keywords", toJson c.keywords),
    ("comparator", jsonObj [("config", cmpConfig.getD .null), ("report", report.getD .null),
      ("time", (reportTime.map toJson).getD .null)]),
    ("bibliography", jsonOpt bibliography), ("media", Json.mkObj media.toList)]
  -- The page.
  let template ← IO.FS.readFile (assets / "template.html")
  let style ← IO.FS.readFile (assets / "style.css")
  let script ← scripts.mapM fun (f : String) => IO.FS.readFile (assets / "js" / f)
  let escapeHtml (s : String) :=
    ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"
  let html := template
    |>.replace "{{TITLE}}" (escapeHtml title)
    |>.replace "{{FAVICON}}" faviconLinks
    |>.replace "/*{{STYLE}}*/" style
    |>.replace "/*{{SCRIPT}}*/" ("\n".intercalate script)
    -- `<` is escaped, so that the data cannot close its `<script>` element
    |>.replace "{{DATA}}" (data.compress.replace "<" "\\u003c")
  IO.FS.writeFile (outDir / "index.html") html
  let secs := ((← IO.monoMsNow) - t0 + 50) / 100
  let plural (n : Nat) (what : String) := s!"{n} {what}{if n == 1 then "" else "s"}"
  info s!"wrote {outDir / "index.html"} in {secs / 10}.{secs % 10} s \
    ({(html.utf8ByteSize + 512) / 1024} KiB, {plural c.shown.size "declaration"} shown, \
    {plural (c.trusted.foldl (· + ·.2.size) 0) "definition"} to trust)"

end Showcase
