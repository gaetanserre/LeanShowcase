/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Lean

/-!
# Text utilities

Small string helpers working on characters, and the analysis of Lean source text: splitting a
declaration into its statement and its proof, extracting the comments of a proof, reading the
`open` commands of a file and the notations it declares.

The file `showcase.md` is parsed into a `Doc`: its front matter, its body, its named blocks
```` ```kind Name ```` (mathematical statements, proofs, proof maps, figures) and the images it
shows.
-/

namespace Showcase

/-! ## Strings -/

/-- The string of a list of characters. -/
def ofChars (cs : List Char) : String := String.ofList cs

/-- The characters of `s` with indices in `[a, b)`. -/
def slice (cs : Array Char) (a b : Nat) : String := ofChars (cs.extract a b).toList

/-- `s` without leading whitespace. -/
def stripLeft (s : String) : String := ofChars (s.toList.dropWhile Char.isWhitespace)

/-- `s` without trailing whitespace. -/
def stripRight (s : String) : String :=
  ofChars (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- `s` without leading and trailing whitespace. -/
def strip (s : String) : String := stripRight (stripLeft s)

/-- Whether `pre` is a prefix of `s`. -/
def hasPrefix (s pre : String) : Bool := pre.toList.isPrefixOf s.toList

/-- Whether `suf` is a suffix of `s`. -/
def hasSuffix (s suf : String) : Bool := suf.toList.reverse.isPrefixOf s.toList.reverse

/-- `s` without its first `n` characters. -/
def dropN (s : String) (n : Nat) : String := ofChars (s.toList.drop n)

/-- The first `n` characters of `s`. -/
def takeN (s : String) (n : Nat) : String := ofChars (s.toList.take n)

/-- The lines of `s`. -/
def splitLines (s : String) : Array String := (s.splitOn "\n").toArray

/-- The number of leading spaces of `s`. -/
def indentOf (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

/-- The first index `≥ start` at which `pat` occurs in `cs`. -/
def findSub (cs : Array Char) (pat : List Char) (start : Nat := 0) : Option Nat := Id.run do
  let n := pat.length
  if n == 0 then return some start
  let mut i := start
  while i + n ≤ cs.size do
    if (cs.extract i (i + n)).toList == pat then return some i
    i := i + 1
  return none

/-- Whether `s` contains `pat`. -/
def containsSub (s pat : String) : Bool := (findSub s.toList.toArray pat.toList).isSome

/-- Replaces every occurrence of `pat` (nonempty) in `s` by `rep`. -/
def replaceAll (s pat rep : String) : String := Id.run do
  let cs := s.toList.toArray
  let p := pat.toList
  if p.isEmpty then return s
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if i + p.length ≤ cs.size && (cs.extract i (i + p.length)).toList == p then
      out := out ++ rep
      i := i + p.length
    else
      out := out.push cs[i]!
      i := i + 1
  return out

/-- `s` without surrounding single or double quotes. -/
def unquote (s : String) : String :=
  let s := strip s
  let cs := s.toList
  match cs.head?, cs.getLast? with
  | some '"', some '"' | some '\'', some '\'' =>
    if cs.length ≥ 2 then ofChars ((cs.drop 1).take (cs.length - 2)) else s
  | _, _ => s

/-! ## Source text -/

/-- The text of `lines` (the lines of a file) in the range `r`. Lines are `1`-based and columns
count codepoints from `0`. -/
def sliceRange (lines : Array String) (r : Lean.DeclarationRange) : String := Id.run do
  let l₀ := r.pos.line - 1
  let l₁ := r.endPos.line - 1
  let mut out : Array String := #[]
  for i in [l₀:l₁ + 1] do
    let mut line := lines[i]?.getD ""
    if i == l₁ then line := takeN line r.endPos.column
    if i == l₀ then line := dropN line r.pos.column
    out := out.push line
  return "\n".intercalate out.toList

/-- `src` without a leading doc comment `/-- ... -/`. -/
def dropDocComment (src : String) : String :=
  let t := stripLeft src
  if hasPrefix t "/--" then
    match findSub t.toList.toArray "-/".toList 3 with
    | some i => stripLeft (dropN t (i + 2))
    | none => t
  else t

/-- Whether `c` opens a bracket. -/
def isOpenBracket (c : Char) : Bool := "([{⟨⦃⟦".toList.contains c

/-- Whether `c` closes a bracket. -/
def isCloseBracket (c : Char) : Bool := ")]}⟩⦄⟧".toList.contains c

/-- Whether the word `w` starts at index `i` of `cs`, delimited by whitespace or the ends. -/
def wordAt (cs : Array Char) (i : Nat) (w : String) : Bool :=
  let n := w.length
  i + n ≤ cs.size && (cs.extract i (i + n)).toList == w.toList &&
    (i == 0 || cs[i - 1]!.isWhitespace) && (i + n == cs.size || cs[i + n]!.isWhitespace)

/-- Splits the source of a declaration into its statement and its body: at the first `:=`, `where`
or line starting with `|` outside brackets, comments and strings. The body is empty if there is
none. -/
def splitStatement (src : String) : String × String := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut depth : Int := 0
  let mut block : Nat := 0
  let mut i := 0
  while i < n do
    let c := cs[i]!
    let next := if i + 1 < n then cs[i + 1]! else ' '
    if block > 0 then
      if c == '-' && next == '/' then
        block := block - 1
        i := i + 2
      else if c == '/' && next == '-' then
        block := block + 1
        i := i + 2
      else
        i := i + 1
      continue
    if c == '-' && next == '-' then
      while i < n && cs[i]! != '\n' do
        i := i + 1
      continue
    if c == '/' && next == '-' then
      block := 1
      i := i + 2
      continue
    if c == '"' then
      i := i + 1
      while i < n && cs[i]! != '"' do
        if cs[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
      continue
    if isOpenBracket c then
      depth := depth + 1
    else if isCloseBracket c then
      depth := depth - 1
    else if depth == 0 then
      if c == ':' && next == '=' then
        return (stripRight (slice cs 0 i), strip (slice cs (i + 2) n))
      if wordAt cs i "where" then
        return (stripRight (slice cs 0 i), slice cs i n)
      if c == '\n' then
        let mut j := i + 1
        while j < n && cs[j]! == ' ' do
          j := j + 1
        if j < n && cs[j]! == '|' then
          return (stripRight (slice cs 0 i), slice cs (i + 1) n)
    i := i + 1
  return (stripRight src, "")

/-- A paragraph of the informal proof: the comments of a proof, with their nesting depth. -/
structure ProofStep where
  /-- The rank of the indentation of the comment, from `0`. -/
  depth : Nat
  /-- The text of the comment. -/
  text : String
  deriving Inhabited

/-- The comments of a proof, in order: consecutive comment lines with the same indentation form
one step, and the depth of a step is the rank of its indentation. -/
def proofSteps (proof : String) : Array ProofStep := Id.run do
  let mut raw : Array (Nat × String) := #[]
  let mut cur : Option (Nat × String) := none
  let mut inBlock := false
  for line in splitLines proof do
    let t := strip line
    let ind := indentOf line
    let piece? : Option String :=
      if inBlock then some t
      else if hasPrefix t "--" then some (strip (dropN t 2))
      else if hasPrefix t "/-" && !hasPrefix t "/--" then some (strip (dropN t 2))
      else none
    if hasPrefix t "/-" && !hasPrefix t "/--" && !containsSub t "-/" then inBlock := true
    else if inBlock && containsSub t "-/" then inBlock := false
    match piece? with
    | some p =>
      let p := strip (replaceAll p "-/" "")
      match cur with
      | some (i, s) =>
        if i == ind || inBlock then cur := some (i, s ++ " " ++ p)
        else
          raw := raw.push (i, s)
          cur := some (ind, p)
      | none => cur := some (ind, p)
    | none =>
      if let some c := cur then raw := raw.push c
      cur := none
  if let some c := cur then raw := raw.push c
  let indents := (raw.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
  return raw.filterMap fun (i, s) =>
    if strip s == "" then none
    else some { depth := indents.findIdx? (· == i) |>.getD 0, text := strip s }

/-- The namespaces opened at top level in a file (`open A B`), and those whose scoped notations only
are opened (`open scoped A B`). Local `open ... in` commands are ignored. -/
def topLevelOpens (lines : Array String) : Array Lean.Name × Array Lean.Name := Id.run do
  let mut simple : Array Lean.Name := #[]
  let mut scopedNs : Array Lean.Name := #[]
  for line in lines do
    if !hasPrefix line "open " || hasSuffix (stripRight line) " in" then continue
    let ws := ((dropN line 5).splitOn " ").filter (· ≠ "")
    let (isScoped, ws) := match ws with
      | "scoped" :: rest => (true, rest)
      | ws => (false, ws)
    for w in ws do
      if w.toList.any fun c => c == '(' || c == ')' then break
      if w == "hiding" || w == "renaming" then break
      let n := w.toName
      if isScoped then scopedNs := scopedNs.push n else simple := simple.push n
  return (simple, scopedNs)

/-- The namespaces a file enters with `namespace`. -/
def fileNamespaces (lines : Array String) : Array Lean.Name :=
  lines.filterMap fun line =>
    if hasPrefix line "namespace " then some (strip (dropN line 10)).toName else none

/-- A notation declared in a file, read from its source. -/
structure SourceNotation where
  /-- The notation as written by a reader, e.g. `𝓗[d, H₀]`. -/
  display : String
  /-- The docstring of the notation, if any. -/
  doc : Option String
  /-- The command that declares the notation. -/
  source : String
  /-- The line of the command in the file, from `1`. -/
  line : Nat
  deriving Inhabited

/-- The notation of a `notation` command, from its atoms and variables before `=>`. -/
def notationDisplay (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let some start := findSub cs "notation".toList | return src
  let stop := (findSub cs "=>".toList start).getD cs.size
  let mut i := start + "notation".length
  -- skip a precedence `:prec`
  while i < stop && cs[i]!.isWhitespace do
    i := i + 1
  if i < stop && cs[i]! == ':' then
    while i < stop && !cs[i]!.isWhitespace do
      i := i + 1
  let mut out := ""
  while i < stop do
    let c := cs[i]!
    if c == '"' then
      let mut j := i + 1
      while j < stop && cs[j]! != '"' do
        j := j + 1
      out := out ++ slice cs (i + 1) j
      i := j + 1
    else if c.isWhitespace then
      i := i + 1
    else
      let mut j := i
      while j < stop && !cs[j]!.isWhitespace && cs[j]! != '"' do
        j := j + 1
      -- drop the precedence of a variable, `x:65`
      let w := slice cs i j
      out := out ++ (w.splitOn ":").headD w
      i := j
  return strip out

/-- The doc comment ending on the line just above line `i` (`0`-based), if any. -/
def docAbove (lines : Array String) (i : Nat) : Option String := Id.run do
  if i == 0 then return none
  let last := stripRight (lines[i - 1]!)
  if !hasSuffix last "-/" then return none
  let mut j := i - 1
  while true do
    if hasPrefix (stripLeft lines[j]!) "/--" then
      let text := "\n".intercalate (lines.extract j i).toList
      let body := dropN (strip text) 3
      return some (strip (takeN body (body.length - 2)))
    if hasPrefix (stripLeft lines[j]!) "/-" || j == 0 then return none
    j := j - 1
  return none

/-- The notations declared at top level in a file (`notation`, `scoped notation`, ...). -/
def sourceNotations (lines : Array String) : Array SourceNotation := Id.run do
  let mut out : Array SourceNotation := #[]
  for h : i in [0:lines.size] do
    let line := lines[i]
    let t := stripLeft line
    let isNotation := ["notation", "scoped notation", "local notation", "notation3",
      "scoped notation3", "scoped[", "infix", "infixl", "infixr", "prefix", "postfix"].any
      (hasPrefix t ·)
    if indentOf line != 0 || !isNotation || !containsSub line "notation" then continue
    -- the command runs until the next blank line or the next unindented line
    let mut j := i + 1
    while j < lines.size && strip lines[j]! != "" && indentOf lines[j]! > 0 do
      j := j + 1
    let src := "\n".intercalate (lines.extract i j).toList
    let n : SourceNotation :=
      { display := notationDisplay src, doc := docAbove lines i, source := src, line := i + 1 }
    out := out.push n
  return out

/-! ## The `showcase.md` file -/

/-- A value of the front matter: a string, a list (`- item` lines) or a map (`key: value`
lines). -/
inductive Value where
  | str (s : String)
  | list (xs : Array String)
  | map (kvs : Array (String × String))
  deriving Inhabited

/-- The front matter of `showcase.md`, a small subset of YAML. -/
structure FrontMatter where
  /-- The keys and their values, in the order of the file. -/
  entries : Array (String × Value) := #[]
  deriving Inhabited

namespace FrontMatter

/-- The value of key `k`. -/
def get? (fm : FrontMatter) (k : String) : Option Value :=
  (fm.entries.find? (·.1 == k)).map (·.2)

/-- The string value of key `k`. -/
def str? (fm : FrontMatter) (k : String) : Option String :=
  match fm.get? k with
  | some (.str s) => if s == "" then none else some s
  | some (.list xs) => xs[0]?
  | _ => none

/-- The list value of key `k`; a string value is a one-element list. -/
def list (fm : FrontMatter) (k : String) : Array String :=
  match fm.get? k with
  | some (.str s) => if s == "" then #[] else #[s]
  | some (.list xs) => xs
  | _ => #[]

/-- The map value of key `k`. -/
def map (fm : FrontMatter) (k : String) : Array (String × String) :=
  match fm.get? k with
  | some (.map kvs) => kvs
  | _ => #[]

end FrontMatter

/-- Splits `key: value` at the first colon followed by a space or ending the line. -/
def splitKey (line : String) : Option (String × String) := Id.run do
  let cs := line.toList.toArray
  for h : i in [0:cs.size] do
    if cs[i] == ':' && (i + 1 == cs.size || cs[i + 1]! == ' ') then
      return some (strip (slice cs 0 i), strip (slice cs (i + 1) cs.size))
  return none

/-- Parses an inline list `[a, b, c]`. -/
def inlineList? (v : String) : Option (Array String) :=
  if hasPrefix v "[" && hasSuffix v "]" then
    some (((takeN (dropN v 1) (v.length - 2)).splitOn ",").toArray.map unquote
      |>.filter (· ≠ ""))
  else none

/-- Parses the lines of a front matter. -/
def parseFrontMatter (lines : Array String) : FrontMatter := Id.run do
  let mut entries : Array (String × Value) := #[]
  let mut cur : Option String := none
  let mut items : Array String := #[]
  let mut kvs : Array (String × String) := #[]
  -- a block scalar `key: |` (lines kept) or `key: >` (lines joined)
  let mut block : Option (String × Bool) := none
  let mut text : Array String := #[]
  for l in lines do
    let t := strip l
    if let some (k, keep) := block then
      if indentOf l > 0 || t == "" then
        text := text.push t
        continue
      let sep := if keep then "\n" else " "
      entries := entries.push (k, .str (strip (sep.intercalate text.toList)))
      block := none
      text := #[]
    if t == "" || hasPrefix t "#" then continue
    if indentOf l > 0 || hasPrefix t "- " then
      if cur.isSome then
        if hasPrefix t "- " then items := items.push (unquote (dropN t 2))
        else if let some (k, v) := splitKey t then kvs := kvs.push (unquote k, unquote v)
      continue
    if let some k := cur then
      entries := entries.push (k, if kvs.isEmpty then .list items else .map kvs)
      cur := none
      items := #[]
      kvs := #[]
    if let some (k, v) := splitKey t then
      if v == "" then cur := some k
      else if v == "|" || v == ">" then block := some (k, v == "|")
      else if let some xs := inlineList? v then entries := entries.push (k, .list xs)
      else entries := entries.push (k, .str (unquote v))
  if let some (k, keep) := block then
    let sep := if keep then "\n" else " "
    entries := entries.push (k, .str (strip (sep.intercalate text.toList)))
  if let some k := cur then
    entries := entries.push (k, if kvs.isEmpty then .list items else .map kvs)
  return { entries }

/-- A block of the body of `showcase.md`: Markdown text, or a declaration to display, written
`{{Name}}` or `{{Name | Label}}` alone on its line. -/
inductive Block where
  | md (text : String)
  | decl (name : String) (label : Option String)
  deriving Inhabited

/-- The kinds of the named blocks ```` ```kind Name ```` of `showcase.md`, with the key of their
texts in the data of the page. -/
def namedKinds : Array (String × String) :=
  #[("informal", "informal"), ("proof", "proofs"), ("diagram", "diagrams"), ("sketch", "sketches"),
    ("figure", "figures")]

/-- The parsed `showcase.md`. -/
structure Doc where
  /-- The front matter. -/
  fm : FrontMatter
  /-- The body, as Markdown text and declarations to display. -/
  blocks : Array Block
  /-- The named blocks ```` ```kind Name ````, as triples of the kind (see `namedKinds`), the name
  of a declaration (as written) and the text. The kinds are the following.
  * `informal`: the mathematical version of the declaration.
  * `proof`: the mathematical proof of a result, folded under its statement.
  * `diagram`: the proof map of a result, one node per line, parsed by the page.
  * `sketch`: the short proof of a result.
  * `figure`: a figure of a result, with one image per line, written `path` or `path | caption`,
    then the caption of the figure. -/
  named : Array (String × String × String) := #[]
  /-- The titles of declarations, from the blocks ```` ```informal Name | Title ````. They replace
  the titles of the docstrings. -/
  titles : Array (String × String) := #[]
  deriving Inhabited

/-- The named blocks of `doc` of kind `kind`, as pairs of the name and the text. -/
def Doc.ofKind (doc : Doc) (kind : String) : Array (String × String) :=
  doc.named.filterMap fun (k, n, t) => if k == kind then some (n, t) else none

/-- The directive `{{Name | Label}}` of a line, if any. -/
def directive? (line : String) : Option (String × Option String) :=
  let t := strip line
  if hasPrefix t "{{" && hasSuffix t "}}" then
    let inner := strip (takeN (dropN t 2) (t.length - 4))
    match inner.splitOn "|" with
    | [n] => some (strip n, none)
    | n :: rest => some (strip n, some (strip ("|".intercalate rest)))
    | [] => none
  else none

/-- Parses `showcase.md`: an optional front matter between `---` lines, then the body. -/
def parseDoc (content : String) : Doc := Id.run do
  let lines := splitLines content
  let mut fmLines : Array String := #[]
  let mut start := 0
  if lines.size > 0 && strip lines[0]! == "---" then
    let mut j := 1
    while j < lines.size && strip lines[j]! != "---" do
      fmLines := fmLines.push lines[j]!
      j := j + 1
    start := j + 1
  let mut blocks : Array Block := #[]
  let mut buf : Array String := #[]
  let mut inFence := false
  let mut named : Array (String × String × String) := #[]
  let mut titles : Array (String × String) := #[]
  -- the named block being read: its kind, the name and the lines
  let mut cur : Option (String × String × Array String) := none
  for line in lines.extract start lines.size do
    let t := strip line
    if let some (kind, n, ls) := cur then
      if hasPrefix t "```" then
        named := named.push (kind, n, "\n".intercalate ls.toList)
        cur := none
      else cur := some (kind, n, ls.push line)
      continue
    -- A block ```` ```figure ```` without a name stays in the text, where the page draws it.
    if !inFence then
      if let some (kind, _) := namedKinds.find? fun (k, _) => hasPrefix t ("```" ++ k ++ " ") then
        -- `Name`, or `Name | Title` for a block `informal`
        let header := strip (dropN t ("```" ++ kind ++ " ").length)
        let parts := header.splitOn "|"
        let n := strip (parts.headD header)
        if kind == "informal" && parts.length > 1 then
          titles := titles.push (n, strip ("|".intercalate (parts.drop 1)))
        cur := some (kind, n, #[])
        continue
    if hasPrefix t "```" then inFence := !inFence
    match (if inFence then none else directive? line) with
    | some (n, label) =>
      if buf.any (strip · != "") then blocks := blocks.push (.md ("\n".intercalate buf.toList))
      buf := #[]
      blocks := blocks.push (.decl n label)
    | none => buf := buf.push line
  if buf.any (strip · != "") then blocks := blocks.push (.md ("\n".intercalate buf.toList))
  return { fm := parseFrontMatter fmLines, blocks, named, titles }

/-- The extensions of the images that browsers display. -/
def imageExtensions : List String := ["svg", "png", "jpg", "jpeg", "gif", "webp", "avif"]

/-- Whether `s` is the path of an image that browsers display, without whitespace. -/
def isImagePath (s : String) : Bool :=
  !s.toList.any Char.isWhitespace &&
    ((System.FilePath.mk s).extension.map String.toLower).any imageExtensions.contains

/-- The image of a line of a figure block, written `path` or `path | caption`. -/
def figureImage? (line : String) : Option String :=
  let p := strip ((line.splitOn "|").headD "")
  if isImagePath p then some p else none

/-- The images that a Markdown text shows: those of its blocks ```` ```figure ````, and its images
`![alt](path)` or `![alt](path "title")` outside code blocks. -/
def markdownImages (md : String) : Array String := Id.run do
  let mut out : Array String := #[]
  -- the code block being read, if any, and whether it is a figure
  let mut fence : Option Bool := none
  for line in splitLines md do
    let t := strip line
    if hasPrefix t "```" then
      fence := if fence.isSome then none else some (t == "```figure" || hasPrefix t "```figure ")
      continue
    match fence with
    | some true => if let some p := figureImage? t then out := out.push p
    | some false => pure ()
    | none =>
      let cs := line.toList.toArray
      let mut i := 0
      while i < cs.size do
        let some a := findSub cs "![".toList i | break
        let some b := findSub cs "](".toList (a + 2) | break
        let some c := findSub cs [')'] (b + 2) | break
        let p := ((strip (slice cs (b + 2) c)).splitOn " ").headD ""
        if isImagePath p then out := out.push p
        i := c + 1
  return out

/-- The local images that `showcase.md` shows, without repetition: those of its text, of its
abstract and of its named blocks. The remote images, given by a URL, are left to the browser. -/
def Doc.imagePaths (doc : Doc) : Array String :=
  let texts := doc.blocks.filterMap (fun | .md t => some t | .decl .. => none) ++
    (doc.fm.str? "abstract").toList.toArray ++
    (doc.named.filter (·.1 != "figure")).map (·.2.2)
  let figures := (doc.ofKind "figure").flatMap fun (_, t) => (splitLines t).filterMap figureImage?
  ((texts.flatMap markdownImages ++ figures).toList.eraseDups.filter (!containsSub · "://")).toArray

end Showcase
