/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase.Util

/-!
# The file `showcase.md`

A front matter between `---` lines, in a small subset of YAML, then the text of the website in
Markdown. In the text:

* a line `{{Name}}` or `{{Name | Label}}` displays the declaration `Name`;
* a fenced block ```` ```kind Name ```` is a note on the declaration `Name`, where `kind` is
  `informal`, `proof`, `sketch`, `diagram` or `figure`. It is not shown where it is written but
  with the declaration. A block ```` ```informal Name | Title ```` also gives the title of `Name`.
-/

namespace Showcase

/-! ## Front matter -/

/-- A value of the front matter: a string, a list of `- item` lines or a map of `key: value`
lines. -/
inductive Value where
  | str (s : String)
  | list (xs : Array String)
  | map (kvs : Array (String × String))
  deriving Inhabited

/-- The front matter of `showcase.md`: its keys and their values, in order. -/
structure FrontMatter where
  entries : Array (String × Value) := #[]
  deriving Inhabited

namespace FrontMatter

/-- The value of the key `k`. -/
def get? (fm : FrontMatter) (k : String) : Option Value :=
  (fm.entries.find? (·.1 == k)).map (·.2)

/-- The string value of the key `k`, if it is not empty. -/
def str? (fm : FrontMatter) (k : String) : Option String :=
  match fm.get? k with
  | some (.str s) => if s == "" then none else some s
  | some (.list xs) => xs[0]?
  | _ => none

/-- The list value of the key `k`. A string is a list of one element. -/
def list (fm : FrontMatter) (k : String) : Array String :=
  match fm.get? k with
  | some (.str s) => if s == "" then #[] else #[s]
  | some (.list xs) => xs
  | _ => #[]

/-- The map value of the key `k`. -/
def map (fm : FrontMatter) (k : String) : Array (String × String) :=
  match fm.get? k with
  | some (.map kvs) => kvs
  | _ => #[]

end FrontMatter

/-- A scalar without its comment: the text from a `#` that follows a space. Quoted scalars are
kept as they are. -/
def stripComment (v : String) : String := Id.run do
  let v := trim v
  let cs := v.toList.toArray
  if let some q := cs[0]? then
    if q == '"' || q == '\'' then
      -- the quoted text, up to the closing quote
      for h : i in [1:cs.size] do
        if cs[i] == q then return slice cs 1 i
      return v
  for h : i in [0:cs.size] do
    if cs[i] == '#' && (i == 0 || cs[i - 1]!.isWhitespace) then return trim (slice cs 0 i)
  return v

/-- Splits `key: value` at the first colon that ends the line or is followed by a space. -/
def splitKey? (line : String) : Option (String × String) := Id.run do
  let cs := line.toList.toArray
  for h : i in [0:cs.size] do
    if cs[i] == ':' && (i + 1 == cs.size || cs[i + 1]! == ' ') then
      return some (unquote (slice cs 0 i), slice cs (i + 1) cs.size)
  return none

/-- Parses an inline list `[a, b, c]`. -/
def inlineList? (v : String) : Option (Array String) := do
  let inner ← (dropPrefix? v "[").bind (dropSuffix? · "]")
  return ((inner.splitOn ",").toArray.map unquote).filter (· ≠ "")

/-- Parses the lines of a front matter. -/
def parseFrontMatter (lines : Array String) : FrontMatter := Id.run do
  let mut entries : Array (String × Value) := #[]
  let mut i := 0
  while i < lines.size do
    let line := lines[i]!
    i := i + 1
    let t := trim line
    if t == "" || t.startsWith "#" || indentOf line > 0 then continue
    let some (k, v) := splitKey? t | continue
    let v := stripComment v
    if v.startsWith "|" || v.startsWith ">" then
      -- a block scalar: the more indented lines that follow
      let mut text : Array String := #[]
      while i < lines.size do
        if indentOf lines[i]! == 0 && trim lines[i]! != "" then break
        text := text.push (trim lines[i]!)
        i := i + 1
      let s := if v.startsWith "|" then "\n".intercalate text.toList
        else -- folded: lines joined, blank lines kept as paragraph breaks
          "\n\n".intercalate ((("\n".intercalate text.toList).splitOn "\n\n").map
            fun p => " ".intercalate ((p.splitOn "\n").map trim |>.filter (· ≠ "")))
      entries := entries.push (k, .str (trim s))
    else if v != "" then
      entries := entries.push (k, match inlineList? v with
        | some xs => .list xs
        | none => .str v)
    else
      -- a list of `- item` lines, or a map of `key: value` lines
      let mut items : Array String := #[]
      let mut kvs : Array (String × String) := #[]
      while i < lines.size do
        let l := lines[i]!
        let t := trim l
        if t != "" && indentOf l == 0 && !t.startsWith "- " then break
        i := i + 1
        if t == "" || t.startsWith "#" then continue
        if let some item := dropPrefix? t "- " then items := items.push (stripComment item)
        else if let some (k, v) := splitKey? t then kvs := kvs.push (k, stripComment v)
      entries := entries.push (k, if kvs.isEmpty then .list items else .map kvs)
  return { entries }

/-! ## Body -/

/-- A block of the text: Markdown, or a declaration to display. -/
inductive Block where
  | md (text : String)
  | decl (name : String) (label : Option String)
  deriving Inhabited

/-- A note on a declaration, written ```` ```kind Name ````. -/
structure Note where
  /-- `informal`, `proof`, `sketch`, `diagram` or `figure`. -/
  kind : String
  /-- The declaration, as written. -/
  name : String
  /-- The title after a bar, for a block `informal`. -/
  title : Option String := none
  text : String
  deriving Inhabited

/-- The kinds of notes. -/
def noteKinds : List String := ["informal", "proof", "sketch", "diagram", "figure"]

/-- The parsed `showcase.md`. -/
structure Doc where
  fm : FrontMatter := {}
  blocks : Array Block := #[]
  notes : Array Note := #[]
  deriving Inhabited

/-- A code fence: its character, its length and its info string. -/
def fence? (line : String) : Option (Char × Nat × String) := do
  let cs := (trim line).toList
  let c ← cs.head?
  guard (c == '`' || c == '~')
  let n := (cs.takeWhile (· == c)).length
  guard (n ≥ 3)
  return (c, n, trim (String.ofList (cs.drop n)))

/-- Whether `line` closes a code block opened by `n` characters `c`. -/
def closesFence (c : Char) (n : Nat) (line : String) : Bool :=
  match fence? line with
  | some (c', n', info) => c' == c && n' ≥ n && info == ""
  | none => false

/-- The directive `{{Name}}` or `{{Name | Label}}` of a line. -/
def directive? (line : String) : Option (String × Option String) := do
  let inner ← (dropPrefix? (trim line) "{{").bind (dropSuffix? · "}}")
  let (n, label) := splitBar inner
  guard (n != "")
  return (n, label)

/-- Parses `showcase.md`. -/
def parseDoc (content : String) : Doc := Id.run do
  let lines := linesOf content
  -- the front matter, if the file starts with `---` and it is closed
  let close := if lines[0]?.map trim == some "---" then
    (lines.extract 1 lines.size).findIdx? (trim · == "---") else none
  let (fm, start) := match close with
    | some j => (parseFrontMatter (lines.extract 1 (j + 1)), j + 2)
    | none => ({}, 0)
  let mut blocks : Array Block := #[]
  let mut notes : Array Note := #[]
  let mut buf : Array String := #[]
  let mut i := start
  while i < lines.size do
    let line := lines[i]!
    i := i + 1
    if let some (c, n, info) := fence? line then
      -- the block, up to its closing fence
      let mut body : Array String := #[]
      while i < lines.size do
        if closesFence c n lines[i]! then break
        body := body.push lines[i]!
        i := i + 1
      let closing := lines[i]?.getD ""
      i := i + 1
      let (kind, rest) := splitFirst info " "
      let (name, title) := splitBar (rest.getD "")
      if noteKinds.contains kind && name != "" then
        notes := notes.push { kind, name, title, text := "\n".intercalate body.toList }
      else
        buf := buf ++ #[line] ++ body ++ #[closing]
    else if let some (n, label) := directive? line then
      if buf.any (trim · != "") then blocks := blocks.push (.md ("\n".intercalate buf.toList))
      buf := #[]
      blocks := blocks.push (.decl n label)
    else
      buf := buf.push line
  if buf.any (trim · != "") then blocks := blocks.push (.md ("\n".intercalate buf.toList))
  return { fm, blocks, notes }

/-! ## Images -/

/-- The extensions of the images that browsers display. -/
def imageExtensions : List String := ["svg", "png", "jpg", "jpeg", "gif", "webp", "avif"]

/-- Whether `s` is the path of an image, without whitespace. -/
def isImagePath (s : String) : Bool :=
  s != "" && !s.toList.any Char.isWhitespace &&
    ((System.FilePath.mk s).extension.map String.toLower).any imageExtensions.contains

/-- The image of a line of a figure, written `path` or `path | caption`. -/
def figureImage? (line : String) : Option String :=
  let p := (splitBar line).1
  if isImagePath p then some p else none

/-- The images of the Markdown text `md`: those of its figures, and those written
`![alt](path)`. -/
def markdownImages (md : String) : Array String := Id.run do
  let mut out : Array String := #[]
  -- inside a code block: whether it is a figure
  let mut fence : Option (Char × Nat × Bool) := none
  for line in linesOf md do
    match fence with
    | some (c, n, fig) =>
      if closesFence c n line then fence := none
      else if fig then if let some p := figureImage? line then out := out.push p
    | none =>
      if let some (c, n, info) := fence? line then
        fence := some (c, n, (splitFirst info " ").1 == "figure")
        continue
      let cs := line.toList.toArray
      for h : i in [0:cs.size] do
        if cs[i] == '!' && cs[i + 1]? == some '[' then
          -- `](`, then the path up to a space or `)`
          let mut j := i + 2
          while j < cs.size && !matchAt cs j "](" do j := j + 1
          let mut k := j + 2
          while k < cs.size && cs[k]! != ')' && !cs[k]!.isWhitespace do k := k + 1
          if j < cs.size then
            let p := slice cs (j + 2) k
            if isImagePath p then out := out.push p
  return out

/-- The local images that the website shows, without repetition. The images given by a URL are left
to the browser. -/
def Doc.images (doc : Doc) : Array String :=
  let texts := doc.blocks.filterMap (fun | .md t => some t | .decl .. => none) ++
    (doc.fm.str? "abstract").toArray ++ (doc.notes.filter (·.kind != "figure")).map (·.text)
  let figures := (doc.notes.filter (·.kind == "figure")).flatMap fun n =>
    (linesOf n.text).filterMap figureImage?
  (texts.flatMap markdownImages ++ figures).toList.eraseDups.toArray.filter
    (!·.contains "://")

end Showcase
