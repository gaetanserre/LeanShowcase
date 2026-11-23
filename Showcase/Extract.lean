/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Lean
import Showcase.Text

/-!
# Extraction of the data of the website

Everything the website shows is read from the compiled environment of the formalization and from
its source files:

* the declarations to display, with their docstring (the informal statement), their pretty-printed
  signature with a link for every constant, their source split into statement and proof, and the
  comments of the proof (the informal proof);
* the definitions of the project that the displayed statements depend on, which a reader has to
  trust since no checker can verify that they mean what they should;
* the axioms used by the displayed results;
* the libraries of `lake-manifest.json`, with the number of their modules that are imported.
-/

open Lean Meta Elab

namespace Showcase

/-! ## Files and packages -/

/-- Where a module comes from: `""` for the project, `"lean"` for the Lean core library, and the
package name for the dependencies of `lake-manifest.json`. -/
def originOf (sysroot : System.FilePath) (olean : System.FilePath) : String :=
  let p := olean.toString
  let comps := p.splitOn "/.lake/packages/"
  if comps.length ≥ 2 then
    ((comps.getLast!.splitOn "/").headD "")
  else if hasPrefix p sysroot.toString then "lean"
  else ""

/-- The `.lean` source of a module: from `LEAN_SRC_PATH`, or next to the build directory of its
`.olean`. -/
def findSource (mod : Name) : IO (Option System.FilePath) := do
  let sp ← getSrcSearchPath
  if let some p ← sp.findWithExt "lean" mod then return some p
  let olean ← findOLean mod
  let s := olean.toString
  match s.splitOn "/.lake/build/lib/lean/" with
  | [root, rest] =>
    let p : System.FilePath := root ++ "/" ++ takeN rest (rest.length - ".olean".length) ++ ".lean"
    return if ← p.pathExists then some p else none
  | _ => return none

/-- The closest ancestor directory of `p` containing a Lake configuration file. -/
partial def findPackageRoot (p : System.FilePath) : IO (Option System.FilePath) := do
  let some dir := p.parent | return none
  if (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) then
    return some dir
  if dir.toString == "/" || dir.toString == "" then return none
  findPackageRoot dir

/-- The output of a command, or `none` if it fails. -/
def runCmd? (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    return if out.exitCode == 0 then some (strip out.stdout) else none
  catch _ => return none

/-- The browsable URL of a git remote. -/
def httpsRemote (url : String) : String :=
  let url := if hasSuffix url ".git" then takeN url (url.length - 4) else url
  if hasPrefix url "git@" then
    match (dropN url 4).splitOn ":" with
    | [host, path] => s!"https://{host}/{path}"
    | _ => url
  else url

/-! ## Declarations -/

/-- The data of a declaration shown on the website. -/
structure DeclData where
  name : Name
  display : String
  kind : String
  module : Name
  doc : Option String
  signature : Array (String × Option Name)
  source : String
  statement : String
  body : String
  steps : Array ProofStep
  axioms : Array Name
  uses : Array Name
  aux : Array Name
  line : Nat
  endLine : Nat
  isPrivate : Bool
  /-- Whether the source file has the declared name where the compiled file says it is. If not,
  the source changed since it was compiled, and the extracts would be shifted. -/
  inSync : Bool := true
  deriving Inhabited

/-- The fixed inputs of the extraction. -/
structure Input where
  /-- The package of every imported module (see `originOf`). -/
  origins : Std.HashMap Name String
  /-- The lines of the source files of the project modules. -/
  sources : Std.HashMap Name (Array String)
  /-- The namespaces to consider open when printing and resolving names. -/
  opens : Array Name
  /-- The main module, whose declarations are displayed. -/
  mainModule : Name

/-- The module of a constant. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether a constant belongs to the project. -/
def Input.isProject (inp : Input) (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => inp.origins.getD m "lean" == ""
  | none => false

/-- The kind of a declaration, as a reader would call it. -/
def kindOf (ci : ConstantInfo) : MetaM String := do
  let env ← getEnv
  match ci with
  | .thmInfo _ => return "theorem"
  | .defnInfo d =>
    if ← isInstance ci.name then return "instance"
    if d.hints matches .abbrev then return "abbrev"
    return "def"
  | .opaqueInfo _ => return "opaque"
  | .axiomInfo _ => return "axiom"
  | .inductInfo _ =>
    if isClass env ci.name then return "class"
    if isStructure env ci.name then return "structure"
    return "inductive"
  | .ctorInfo _ => return "constructor"
  | .recInfo _ => return "recursor"
  | .quotInfo _ => return "quotient"

/-- The constant whose pretty-printed form an `Info` annotates, if it is the head of an
application or a constant. -/
def infoConst? : Elab.Info → Option Name
  | .ofTermInfo ti => ti.expr.consumeMData.getAppFn.constName?
  | .ofDelabTermInfo ti => ti.expr.consumeMData.getAppFn.constName?
  | _ => none

/-- Flattens a tagged pretty-printed text into pieces of text, each with the constant of the
innermost annotation around it. -/
partial def flattenTagged (infos : PrettyPrinter.InfoPerPos) :
    Widget.TaggedText (Nat × Nat) → Option Name → Array (String × Option Name) →
      Array (String × Option Name)
  | .text s, cur, acc => acc.push (s, cur)
  | .append ts, cur, acc => ts.foldl (fun acc t => flattenTagged infos t cur acc) acc
  | .tag (n, _) t, _, acc => flattenTagged infos t ((infos.get? n).bind infoConst?) acc

/-- Merges consecutive pieces with the same constant. -/
def mergePieces (ps : Array (String × Option Name)) : Array (String × Option Name) :=
  ps.foldl (init := #[]) fun acc (s, c) =>
    match acc.back? with
    | some (s', c') => if c' == c then acc.pop.push (s' ++ s, c) else acc.push (s, c)
    | none => acc.push (s, c)

/-- The pretty-printed signature of a declaration, as pieces of text linked to constants. -/
def signatureOf (n : Name) (width : Nat := 90) : MetaM (Array (String × Option Name)) := do
  try
    let fwi ← PrettyPrinter.ppSignature n
    let tt := Widget.TaggedText.prettyTagged fwi.fmt (w := width)
    return mergePieces (flattenTagged fwi.infos tt none #[])
  catch _ => return #[(toString n, none)]

/-- The constants used by the type and the value of a declaration. -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  let val := match ci with
    | .thmInfo v => v.value.getUsedConstants
    | .defnInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | _ => #[]
  let all := ci.type.getUsedConstants ++ val
  (all.foldl (fun (s : NameSet) n => s.insert n) {}).toArray.qsort Name.quickLt

/-- The name of a declaration as written in the source. -/
def userName (n : Name) : Name := privateToUserName n

/-- Whether a constant is generated by Lean rather than written by the user. -/
def isGenerated (env : Environment) (n : Name) : Bool :=
  (userName n).isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    match env.find? n with
    | some (.ctorInfo _) | some (.recInfo _) => true
    | some ci => ci.type.getAppFn.constName?.any (·.getRoot == `Lean)
    | none => true

/-- The declarations written in a module, in source order. A declaration is kept if its declared
name is written at its selection range and it is not inside another kept declaration (which drops
the fields of structures, `@[simps]` lemmas, ...). -/
def moduleDecls (inp : Input) (mod : Name) (includePrivate : Bool) :
    MetaM (Array (Name × DeclarationRanges)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | return #[]
  let lines := inp.sources.getD mod #[]
  let mut found : Array (Name × DeclarationRanges) := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    if isGenerated env n || (isPrivateName n && !includePrivate) then continue
    let some r ← findDeclarationRanges? n | continue
    let sel := strip (sliceRange lines r.selectionRange)
    if sel == "" || !hasSuffix ((userName n).toString (escape := false)) sel then continue
    found := found.push (n, r)
  let sorted := found.qsort fun (_, a) (_, b) =>
    a.range.pos.line < b.range.pos.line ||
      (a.range.pos.line == b.range.pos.line && a.range.pos.column < b.range.pos.column)
  let mut kept : Array (Name × DeclarationRanges) := #[]
  for (n, r) in sorted do
    match kept.back? with
    | some (_, r') =>
      if r'.range.endPos.line > r.range.pos.line ||
          (r'.range.endPos.line == r.range.pos.line &&
            r'.range.endPos.column ≥ r.range.pos.column) then continue
    | none => pure ()
    kept := kept.push (n, r)
  return kept

/-- The lemmas of the main module that a proof relies on: the private theorems it uses, directly
or not, and the public theorems it uses directly. -/
partial def auxLemmas (inp : Input) (n : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := #[n]
  let mut out := #[]
  if let some ci := env.find? n then
    for u in usedConstants ci do
      if u != n && !isPrivateName u && moduleOf? env u == some inp.mainModule &&
          !isGenerated env u then
        if let some (.thmInfo _) := env.find? u then out := out.push u
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    let some ci := env.find? c | continue
    for u in usedConstants ci do
      if seen.contains u then continue
      seen := seen.insert u
      if isPrivateName u && moduleOf? env u == some inp.mainModule && !isGenerated env u then
        if let some (.thmInfo _) := env.find? u then
          out := out.push u
          todo := todo.push u
      else if (userName u).isInternalDetail && moduleOf? env u == some inp.mainModule then
        todo := todo.push u
  return out

/-- The data of a declaration. -/
def declData (inp : Input) (n : Name) : MetaM DeclData := do
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown declaration `{n}`"
  let module := (moduleOf? env n).getD .anonymous
  let ranges ← findDeclarationRanges? n
  let lines := inp.sources.getD module #[]
  let source := match ranges with
    | some r => if lines.isEmpty then "" else dropDocComment (sliceRange lines r.range)
    | none => ""
  let kind ← kindOf ci
  -- the name must be written at its selection range (an instance may have no written name)
  let inSync := match ranges with
    | some r =>
      lines.isEmpty || kind == "instance" ||
        let sel := strip (sliceRange lines r.selectionRange)
        sel != "" && hasSuffix ((userName n).toString (escape := false)) sel
    | none => true
  let (statement, body) :=
    if kind == "structure" || kind == "class" || kind == "inductive" then (source, "")
    else splitStatement source
  let steps := if kind == "theorem" then proofSteps body else #[]
  let doc ← findDocString? env n
  let axioms ← try collectAxioms n catch _ => pure #[]
  let aux ← if kind == "theorem" then auxLemmas inp n else pure #[]
  let ns := (userName n).getPrefix
  let sig ← withTheReader Core.Context
      (fun ctx => { ctx with currNamespace := ns,
                             openDecls := inp.opens.toList.map (.simple · []) }) do
    signatureOf n
  return {
    name := n, display := (userName n).toString (escape := false), kind, module, doc,
    signature := sig, source, statement, body, steps,
    axioms := axioms.qsort Name.quickLt, uses := usedConstants ci, aux,
    line := ranges.map (·.range.pos.line) |>.getD 0,
    endLine := ranges.map (·.range.endPos.line) |>.getD 0,
    isPrivate := isPrivateName n, inSync }

/-! ## Trusted definitions -/

/-- The declaration a reader sees for a generated constant: the structure of a projection or a
constructor, the inductive type of a recursor, and the constant itself otherwise. -/
def ownerOf (env : Environment) (n : Name) : Name :=
  if let some info := env.getProjectionFnInfo? n then info.ctorName.getPrefix
  else match env.find? n with
    | some (.ctorInfo c) => c.induct
    | some (.recInfo _) => n.getPrefix
    | _ => if isAuxRecursor env n || isNoConfusion env n then n.getPrefix else n

/-- The definitions of the project that the statement of `root` depends on, through the types and
the bodies of definitions. Theorems are not followed: their proofs are checked. -/
partial def trustedDeps (inp : Input) (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some rci := env.find? root | return #[]
  -- The statement of a theorem, or the whole of a definition.
  let start := if rci matches .thmInfo _ then rci.type.getUsedConstants else #[root]
  let mut seen : NameSet := {}
  let mut todo := start
  let mut out : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if !inp.isProject env c then continue
    let some ci := env.find? c | continue
    if ci matches .thmInfo _ then continue
    let owner := ownerOf env c
    if owner != c then
      todo := todo.push owner
      continue
    if !isGenerated env c then
      if (← findDeclarationRanges? c).isSome then out := out.insert c
    todo := todo ++ usedConstants ci
    if let .inductInfo v := ci then
      for ctor in v.ctors do
        if let some cci := env.find? ctor then todo := todo ++ cci.type.getUsedConstants
  return out.toArray.qsort Name.quickLt

/-! ## Names in prose -/

/-- The identifiers in the code spans (between backticks) of a Markdown text. -/
def codeSpanIdents (md : String) : Array String := Id.run do
  let spans := (md.splitOn "`").toArray
  let mut out := #[]
  for h : i in [0:spans.size] do
    if i % 2 == 0 then continue
    let cs := spans[i].toList.toArray
    let mut j := 0
    while j < cs.size do
      if isIdFirst cs[j]! then
        let mut k := j + 1
        while k < cs.size && (isIdRest cs[k]! || (cs[k]! == '.' && k + 1 < cs.size &&
            isIdFirst cs[k + 1]!)) do
          k := k + 1
        out := out.push (slice cs j k)
        j := k
      else
        j := j + 1
  return out

/-- Resolves an identifier of the prose against the environment, trying the open namespaces. -/
def resolveIdent (env : Environment) (namespaces : Array Name) (s : String) : Option Name :=
  if s.length ≤ 1 then none else
  let n := s.toName
  if n.isAnonymous then none
  else if env.contains n && !isGenerated env n then some n
  else namespaces.findSome? fun ns =>
    let m := ns ++ n
    if env.contains m && !isGenerated env m then some m else none

end Showcase
