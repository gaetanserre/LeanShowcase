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
(`Showcase/Extract.lean`) and writes a single self-contained `index.html`: the template of
`assets/` with the data embedded as JSON.

## The `showcase.md` file

```markdown
---
title: Mean-field SVGD on a compact domain
module: CompactSVGD.Paper           # the file presented
trusted: [CompactSVGD.Definitions]  # files whose definitions the reader must check
docgen: https://example.org/docs/   # the docgen of the project, for links
---

Prose in Markdown, then a result:

{{SVGD.weak_convergence | Theorem 3.1}}
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
  doc : System.FilePath := "showcase.md"
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

/-- Generates the website described by the file `opts.doc`. -/
def generate (opts : Options) : IO Unit := do
  let docPath ← IO.FS.realPath opts.doc
  let baseDir := docPath.parent.getD "."
  let doc := parseDoc (← IO.FS.readFile docPath)
  let fm := doc.fm
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
      sourcePaths := sourcePaths.insert m (if hasPrefix p rootStr then dropN p rootStr.length else p)
  let sourceUrl (d : DeclData) : Option String := do
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
    for m in trustedModules do
      for (n, _) in ← moduleDecls inp m (includePrivate := true) do
        if let some ci := env.find? n then
          if !(ci matches .thmInfo _) then trusted := trusted.insert n
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
    -- the mathematical statements and proofs of `showcase.md` cite Lean names too
    texts := texts ++ doc.informal.map (·.2) ++ doc.proofs.map (·.2)
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
    for c in targets.toArray do
      if isGenerated env c && !decls.contains c then continue
      let url := docUrl c
      if url.isNone && !decls.contains c then continue
      constsJson := constsJson.push ((c.toString (escape := false)), optJson url)
    let declsJson := decls.toList.toArray.map fun (n, d) =>
      ((n.toString (escape := false)), d.json (sourceUrl d) (checkedNames.contains n))
    -- The mathematical versions of declarations, by full name (or as written, e.g. a notation).
    let byName (entries : Array (String × String)) : Array (String × Json) :=
      entries.map fun (n, t) =>
        ((match resolveIdent env namespaces n with
          | some c => c.toString (escape := false)
          | none => n), toJson t)
    let informalJson := byName doc.informal
    let proofsJson := byName doc.proofs
    let titlesJson := byName doc.titles
    -- Module docs of the main module: the title and the abstract.
    let headerDoc := ((getModuleDoc? env mainModule).bind (·[0]?)).map (·.doc)
    let (docTitle, docLead) := (headerDoc.map titleAndLead).getD (none, none)
    return Json.mkObj [
      ("blocks", Json.arr blockJson),
      ("shown", Json.arr (shown.map nameJson)),
      ("aux", Json.arr (auxNames.map nameJson)),
      ("decls", Json.mkObj declsJson.toList),
      ("trusted", Json.arr trustedJson),
      ("axioms", Json.arr axiomsJson),
      ("refs", Json.mkObj (refs.toList.map fun (s, n) => (s, nameJson n))),
      ("consts", Json.mkObj constsJson.toList),
      ("informal", Json.mkObj informalJson.toList),
      ("proofs", Json.mkObj proofsJson.toList),
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
    ("reportTime", match reportTime with | some t => toJson t | none => Json.null),
    ("checkers", toJson (fm.list "checkers"))]
  let site := data.mergeObj (Json.mkObj [
    ("meta", metaJson), ("libraries", Json.arr libs), ("comparator", comparatorJson),
    ("bibliography", optJson bib)])
  -- Write the page.
  let assets ← match ← IO.getEnv "SHOWCASE_ASSETS" with
    | some a => pure (System.FilePath.mk a)
    | none => do
      let app ← IO.appPath
      -- `<package>/.lake/build/bin/showcase`
      pure ((app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)).getD "." /
        "assets")
  let template ← IO.FS.readFile (assets / "template.html")
  let style ← IO.FS.readFile (assets / "style.css")
  let script ← IO.FS.readFile (assets / "app.js")
  let title := ((fm.str? "title").orElse fun _ => docTitle).getD (toString mainModule)
  let dataStr := replaceAll site.compress "</" "<\\/"
  let html := template
    |> (replaceAll · "{{TITLE}}" title)
    |> (replaceAll · "/*{{STYLE}}*/" style)
    |> (replaceAll · "/*{{SCRIPT}}*/" script)
    |> (replaceAll · "{{DATA}}" dataStr)
  let outDir := opts.out.getD (resolvePath ((fm.str? "output").getD "_site"))
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "index.html") html
  IO.println s!"showcase: wrote {outDir / "index.html"} ({(html.utf8ByteSize + 512) / 1024} KiB)"

end Showcase
