/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase.Config
import Showcase.Extract

/-!
# What the website shows

`Showcase.collect` decides what the website shows, from `showcase.md` and the environment: the
blocks of the text and the declarations of its cards, the lemmas of their proofs, the definitions
and the notations that the statements rest on, the axioms, and the Lean names written in the text.

Without any `{{Name}}` line in `showcase.md`, the text is every declaration of the presented
modules and of the modules of the project that they import, in the order of the imports and of the
files, with their module docstrings.
-/

open Lean Meta

namespace Showcase

/-- The title (the first `#` heading) of a Markdown text, the first paragraph after it, and the
rest of the text. -/
def titleAndLead (md : String) : Option String × Option String × String := Id.run do
  let lines := linesOf md
  let some t := lines.findIdx? (trim · |>.startsWith "# ") | return (none, none, md)
  let title := trim (dropChars (trim lines[t]!) 2)
  let mut i := t + 1
  while i < lines.size && trim lines[i]! == "" do i := i + 1
  let start := i
  while i < lines.size && trim lines[i]! != "" && !(trim lines[i]!).startsWith "#" do i := i + 1
  let lead := " ".intercalate ((lines.extract start i).toList.map trim)
  let rest := "\n".intercalate (lines.extract i lines.size).toList
  return (some title, if lead == "" then none else some lead, rest)

/-- The content of the code spans of a Markdown text. -/
def codeSpans (md : String) : Array String := Id.run do
  let parts := (md.splitOn "`").toArray
  let mut out := #[]
  for h : i in [0:parts.size] do
    if i % 2 == 1 then out := out.push parts[i]
  return out

/-- What the website shows. -/
structure Collected where
  /-- The title and the first paragraph of the first module docstring. -/
  title : Option String := none
  lead : Option String := none
  blocks : Array Block := #[]
  /-- The declarations shown as cards, in order. -/
  shown : Array Name := #[]
  main : Array (Name × Option String) := #[]
  decls : Std.HashMap Name DeclData := {}
  /-- The lemmas of each proof that have no card: the private ones. -/
  aux : Std.HashMap Name (Array Name) := {}
  /-- The results with a card that each proof uses. -/
  uses : Std.HashMap Name (Array Name) := {}
  /-- The axioms that each declaration depends on. -/
  axioms : Std.HashMap Name (Array Name) := {}
  /-- The axioms, with the declarations that depend on them. -/
  axiomUsers : Array (Name × Array Name) := #[]
  /-- The definitions to trust, by module. -/
  trusted : Array (Name × Array Name) := #[]
  notations : Array NotationData := #[]
  /-- The names written in code spans, with the constants they name. -/
  refs : Array (String × Name) := #[]
  /-- The notes of `showcase.md`, with the full name of their declaration. -/
  notes : Array (Note × String) := #[]
  /-- The identifiers of the sources that are keywords or tactics. -/
  keywords : Array String := #[]
  /-- The modules whose declarations the text presents: their definitions are read there, not
  among the definitions to trust. -/
  presented : Array Name := #[]
  deriving Inhabited

/-- The modules of the project that `modules` import, directly or not, themselves included, in the
order of the imports: a module comes after the modules it imports. -/
def projectModules (ctx : Ctx) (modules : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := modules
  while todo.size > 0 do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m || ctx.packages.packageOf? m != some ctx.project then continue
    seen := seen.insert m
    if let some idx := env.getModuleIdx? m then
      todo := todo ++ env.header.moduleData[idx.toNat]!.imports.map (·.module)
  return env.header.moduleNames.filter seen.contains

/-- Every declaration of the modules, in the order of their files, with their module docstrings.
The title and the first paragraph of `titleModule` are left out: they are the title and the
abstract of the website. -/
def autoBlocks (ctx : Ctx) (modules : Array Name) (titleModule : Name) :
    MetaM (Array Block) := do
  let env ← getEnv
  let mut blocks : Array Block := #[]
  for mod in modules do
    let docs := (getModuleDoc? env mod).getD #[]
    let decls ← moduleDecls ctx mod false
    if decls.isEmpty && docs.isEmpty then continue
    let mut items : Array (Nat × Block) := #[]
    -- a file without a title is a section named after it
    if modules.size > 1 && !docs.any (·.doc.startsWith "# ") then
      let last := match mod with
        | .str _ s => s
        | _ => nameStr mod
      items := items.push (0, .md s!"# {last}\n\n`{mod}`")
    for h : i in [0:docs.size] do
      let d := docs[i]
      let text := if mod == titleModule && i == 0 then (titleAndLead d.doc).2.2 else d.doc
      if trim text != "" then items := items.push (d.declarationRange.pos.line, .md text)
    for (n, r) in decls do
      items := items.push (r.range.pos.line, .decl (toString n) none)
    blocks := blocks ++ (items.qsort (·.1 < ·.1)).map (·.2)
  return blocks

/-- The lemmas of a proof that have no card: the private theorems of the project that it uses,
directly or through internal declarations, and the results with a card that it uses. -/
def proofLemmas (ctx : Ctx) (shown : NameSet) (n : Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let mut aux : Array Name := #[]
  let mut uses : Array Name := #[]
  let mut todo := ((env.find? n).map valueConsts).getD #[]
  let mut seen : NameSet := {}
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c || c == n then continue
    seen := seen.insert c
    if shown.contains c then
      uses := uses.push c
      continue
    if !ctx.isProject env c then continue
    let some ci := env.find? c | continue
    if isPrivateName c && ci matches .thmInfo _ && !isGenerated env c then
      aux := aux.push c
      todo := todo ++ valueConsts ci
    else if (userName c).isInternalDetail then
      todo := todo ++ valueConsts ci
  return (aux, uses)

/-- Collects what the website shows. `modules` are the presented modules, `trustedModules` those
whose definitions are all listed, and `checked` the theorems that comparator checks. -/
def collect (ctx : Ctx) (doc : Doc) (modules trustedModules : Array Name) (checked : NameSet) :
    MetaM Collected := do
  let env ← getEnv
  -- The scopes of the presented files: their scoped notations are activated for the
  -- pretty-printer, and their `open` commands resolve the names written in the text.
  let mut opens : Array OpenDecl := #[]
  let mut namespaces : Array Name := #[.anonymous]
  let mut scopedNs : Array (Name × Name) := #[]
  for m in modules ++ trustedModules do
    let scopes ← ctx.scopesOf m
    for sc in scopes do
      for ns in sc.scopedNs do
        if !scopedNs.contains (sc.ns, ns) then scopedNs := scopedNs.push (sc.ns, ns)
      if !namespaces.contains sc.ns then namespaces := namespaces.push sc.ns
    if let some sc := scopes.back? then opens := opens ++ (resolveOpens env sc).toArray
  for (cur, ns) in scopedNs do
    for r in (ResolveName.resolveNamespace env cur [] ns).toArray.push ns do activateScoped r
  let env ← getEnv
  -- the constants of the project, by the last component of their name
  let mut bySuffix : Std.HashMap String (Array Name) := {}
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    if ctx.packages.packageOf? m != some ctx.project then continue
    for n in d.constNames do
      if isGenerated env n || isPrivateName n then continue
      let key := match n with
        | .str _ s => s
        | _ => ""
      bySuffix := bySuffix.insert key ((bySuffix.getD key #[]).push n)
  -- A name written in the text: as it is, in the namespaces and with the `open` commands of the
  -- files, or else the only constant of the project whose name ends with it.
  let resolve (s : String) : Option Name :=
    let n := s.toName
    if env.contains n && !isGenerated env n then some n
    else if n.isAnonymous || s.length ≤ 1 then none
    else match namespaces.findSome? (resolveIdent? env · opens.toList s) with
      | some c => some c
      | none =>
        let last := match n with
          | .str _ l => l
          | _ => ""
        match (bySuffix.getD last #[]).filter (nameStr · |>.endsWith ("." ++ s)) with
        | #[c] => some c
        | _ => none
  let mut out : Collected := {}
  if let some d := (getModuleDoc? env modules[0]!).bind (·[0]?) then
    let (title, lead, _) := titleAndLead d.doc
    out := { out with title, lead }
  -- The blocks, and the declarations of the cards.
  let mut blocks := doc.blocks
  let mut presented := modules
  if !blocks.any (· matches .decl ..) then
    presented ← projectModules ctx modules
    blocks := blocks ++ (← autoBlocks ctx presented modules[0]!)
  out := { out with presented }
  for b in blocks do
    match b with
    | .md _ => out := { out with blocks := out.blocks.push b }
    | .decl s label =>
      let some n := resolve s | warn s!"unknown declaration `{s}`, skipped"
      out := { out with blocks := out.blocks.push (.decl (nameStr n) label) }
      if !out.shown.contains n then out := { out with shown := out.shown.push n }
  for item in doc.fm.list "main" do
    let (s, label) := splitBar item
    let some n := resolve s | warn s!"unknown main result `{s}`, skipped"
    if !out.shown.contains n then warn s!"the main result `{s}` has no card in the text"
    out := { out with main := out.main.push (n, label) }
  let mut decls : Std.HashMap Name DeclData := {}
  for n in out.shown ++ out.main.map (·.1) do
    if !decls.contains n then decls := decls.insert n (← declData ctx n)
  -- The lemmas of the proofs.
  let shownSet := out.shown.foldl (·.insert ·) ({} : NameSet)
  for n in out.shown do
    if (decls.get! n).kind != "theorem" then continue
    let (aux, uses) ← proofLemmas ctx shownSet n
    out := { out with aux := out.aux.insert n aux,
                      uses := out.uses.insert n (out.shown.filter uses.contains) }
    for a in aux do
      if !decls.contains a then decls := decls.insert a (← declData ctx a)
  -- What the statements rest on: the definitions outside the reviewed libraries and the presented
  -- modules, by module, the trusted modules first, then in the order of the imports.
  -- The roots are the statements: those of the presented modules, and those shown elsewhere. A
  -- definition of another module has a card iff a statement depends on it, directly or through
  -- the definitions of the presented modules.
  let mut stated : Array Name := #[]
  for m in presented do
    stated := stated ++ (← moduleDecls ctx m false).map (·.1)
  let results := (stated ++ out.shown ++ out.main.map (·.1) ++ checked.toArray).filter fun n =>
    (env.find? n).any (· matches .thmInfo _)
  let cone ← trustedDefs ctx results
  let coneSet := cone.foldl (·.insert ·) ({} : NameSet)
  for m in trustedModules do
    for (n, _) in ← moduleDecls ctx m true do
      if (env.find? n).any (· matches .thmInfo _) || coneSet.contains n then continue
      warn s!"`{n}`, in the trusted module {m}, is used by no statement: it is not listed"
  for n in cone do
    if !decls.contains n then decls := decls.insert n (← declData ctx n)
  let rank (m : Name) : Nat := match trustedModules.findIdx? (· == m) with
    | some i => i
    | none => trustedModules.size + ((env.getModuleIdx? m).map (·.toNat)).getD 0
  -- the definitions of the presented modules are read in the text, with the results
  let byModule := cone.foldl (init := ({} : Std.HashMap Name (Array Name))) fun acc n =>
    let m := (moduleOf? env n).getD .anonymous
    if presented.contains m && !trustedModules.contains m then acc
    else acc.insert m ((acc.getD m #[]).push n)
  let groups := (byModule.toArray.qsort fun a b => rank a.1 < rank b.1).map fun (m, ns) =>
    (m, ns.qsort fun a b => (decls.get! a).line < (decls.get! b).line)
  let notationModules := (groups.map (·.1) ++ trustedModules).toList.eraseDups.toArray.filter
    fun m => !ctx.moduleReviewed m
  out := { out with trusted := groups, notations := ← notationsOf ctx notationModules }
  -- The axioms, computed once for every constant.
  let mut st : AxiomState := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  let declared := out.shown ++ out.main.map (·.1) ++ cone ++ out.aux.toArray.flatMap (·.2)
  for n in declared.toList.eraseDups do
    let (m, st') := (axiomMask env n).run st
    st := st'
    let axs := st.axiomsOf m
    out := { out with axioms := out.axioms.insert n axs }
    for a in axs do users := users.insert a ((users.getD a #[]).push n)
  out := { out with axiomUsers := users.toArray.qsort fun a b => Name.lt a.1 b.1 }
  -- an axiom of the project is shown with its source
  for (a, _) in out.axiomUsers do
    if ctx.isProject env a && !decls.contains a then decls := decls.insert a (← declData ctx a)
  -- The names written in code spans: in the text, the notes and the docstrings.
  let texts := out.blocks.filterMap (fun | .md t => some t | _ => none) ++
    doc.notes.map (·.text) ++ (doc.fm.str? "abstract").toArray ++ out.lead.toArray ++
    decls.toArray.filterMap (·.2.doc)
  let mut refs : Std.HashMap String Name := {}
  for t in texts do
    for span in codeSpans t do
      for id in identifiers span do
        if !refs.contains id then
          if let some c := resolve id then refs := refs.insert id c
  -- The keywords: the identifiers of the sources and the statements that are tokens.
  let tokens := (Parser.getTokenTable env).values.foldl (·.insert ·) ({} : Std.HashSet String)
  let mut words : Std.HashSet String := {}
  for (_, d) in decls.toList do
    for id in identifiers d.source ++ d.signature.flatMap (identifiers ·.1) do
      words := words.insert id
  for n in out.notations do
    for id in identifiers n.source do words := words.insert id
  return { out with
    decls, refs := refs.toArray,
    notes := doc.notes.map fun note =>
      (note, ((resolve note.name).map nameStr).getD note.name),
    -- the tokens of notations, such as `ℝ`, are not keywords
    keywords := (words.toArray.filter fun w =>
      tokens.contains w && w.toList.head?.any Char.isAlpha).qsort (· < ·) }

end Showcase
