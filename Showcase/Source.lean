/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase.Util

/-!
# Lean source text

The compiled files keep the position of each declaration but not its syntax. The website reads the
rest from the source: the split of a declaration into its statement and its proof, the comments of
the proof, the identifiers it writes and the `namespace` and `open` commands around it.
-/

open Lean

namespace Showcase

/-! ## Lexing -/

/-- A scanner over the characters of a text, that skips comments, strings and characters. -/
structure Scanner where
  cs : Array Char
  i : Nat := 0

namespace Scanner

/-- The character at offset `k` from the current position. -/
def peek (s : Scanner) (k : Nat := 0) : Char := s.cs[s.i + k]?.getD '\x00'

/-- Whether the scan is over. -/
def done (s : Scanner) : Bool := s.i ≥ s.cs.size

/-- Skips a comment, a string or a character literal at the current position, if there is one.
Returns `none` otherwise. -/
def skipLiteral? (s : Scanner) : Option Scanner := Id.run do
  let cs := s.cs
  let c := s.peek
  if c == '-' && s.peek 1 == '-' then
    let mut j := s.i
    while j < cs.size && cs[j]! != '\n' do j := j + 1
    return some { s with i := j }
  if c == '/' && s.peek 1 == '-' then
    -- nested block comments
    let mut depth := 0
    let mut j := s.i
    while j < cs.size do
      if matchAt cs j "/-" then
        depth := depth + 1
        j := j + 2
      else if matchAt cs j "-/" then
        depth := depth - 1
        j := j + 2
        if depth == 0 then break
      else j := j + 1
    return some { s with i := j }
  if c == '"' then
    let mut j := s.i + 1
    while j < cs.size && cs[j]! != '"' do
      j := j + (if cs[j]! == '\\' then 2 else 1)
    return some { s with i := j + 1 }
  -- a character literal `'a'` or `'\n'`, but not the prime of an identifier `f'`
  if c == '\'' && (s.i == 0 || !isIdRest cs[s.i - 1]!) then
    if s.peek 2 == '\'' && s.peek 1 != '\\' then return some { s with i := s.i + 3 }
    if s.peek 1 == '\\' && s.peek 3 == '\'' then return some { s with i := s.i + 4 }
  return none

/-- The end of the identifier starting at the current position, dotted parts included, if there is
one. -/
def identEnd? (s : Scanner) : Option Nat := Id.run do
  let cs := s.cs
  let part (j : Nat) : Option Nat := Id.run do
    if cs[j]? == some '«' then
      let mut k := j + 1
      while k < cs.size && cs[k]! != '»' do k := k + 1
      return if k < cs.size then some (k + 1) else none
    if !(cs[j]?.any isIdFirst) then return none
    let mut k := j + 1
    while k < cs.size && isIdRest cs[k]! do k := k + 1
    return some k
  if s.i > 0 && (isIdRest cs[s.i - 1]! || cs[s.i - 1]! == '.') then return none
  let some k := part s.i | return none
  let mut k := k
  while cs[k]? == some '.' do
    match part (k + 1) with
    | some k' => k := k'
    | none => break
  return some k

end Scanner

/-- The identifiers written in a Lean source text, outside comments and strings. -/
def identifiers (src : String) : Array String := Id.run do
  let mut s : Scanner := { cs := src.toList.toArray }
  let mut out : Array String := #[]
  while !s.done do
    if let some s' := s.skipLiteral? then
      s := s'
    else if let some k := s.identEnd? then
      out := out.push (slice s.cs s.i k)
      s := { s with i := k }
    else
      s := { s with i := s.i + 1 }
  return out

/-! ## Declarations -/

/-- `src` without a leading doc comment `/-- ... -/`. -/
def dropDocComment (src : String) : String := Id.run do
  let t := trim src
  if !t.startsWith "/--" then return t
  let s : Scanner := { cs := t.toList.toArray }
  match s.skipLiteral? with
  | some s' => return trim (slice s'.cs s'.i s'.cs.size)
  | none => return t

/-- Whether the word `w` is at index `i` of `cs`, delimited by non-identifier characters. -/
def wordAt (cs : Array Char) (i : Nat) (w : String) : Bool :=
  matchAt cs i w && (i == 0 || !isIdRest cs[i - 1]!) &&
    !(cs[i + w.length]?.any isIdRest)

/-- Splits the source of a declaration into its statement and its body, at the first `:=`, `where`
or line starting with `|` outside brackets, comments and strings. -/
def splitStatement (src : String) : String × String := Id.run do
  let mut s : Scanner := { cs := src.toList.toArray }
  let cs := s.cs
  let mut depth : Int := 0
  while !s.done do
    if let some s' := s.skipLiteral? then
      s := s'
      continue
    let c := s.peek
    if "([{⟨⦃⟦".toList.contains c then depth := depth + 1
    else if ")]}⟩⦄⟧".toList.contains c then depth := depth - 1
    else if depth == 0 then
      if c == ':' && s.peek 1 == '=' then
        return (trim (slice cs 0 s.i), trim (slice cs (s.i + 2) cs.size))
      if wordAt cs s.i "where" then
        return (trim (slice cs 0 s.i), slice cs s.i cs.size)
      if c == '\n' && (trim (slice cs (s.i + 1) cs.size)).startsWith "|" then
        return (trim (slice cs 0 s.i), slice cs (s.i + 1) cs.size)
    s := { s with i := s.i + 1 }
  return (trim src, "")

/-- The comments of a proof, in order, as an informal proof: consecutive comment lines with the
same indentation form one paragraph, and the depth of a paragraph is the rank of its indentation
among those of the proof. -/
def proofComments (body : String) : Array (Nat × String) := Id.run do
  let mut raw : Array (Nat × String) := #[]
  -- the paragraph being read: its indentation and its text
  let mut cur : Option (Nat × String) := none
  -- inside a block comment `/- ... -/`
  let mut inBlock := false
  for line in linesOf body do
    let t := trim line
    let wasIn := inBlock
    let opens := !wasIn && t.startsWith "/-" && !t.startsWith "/--"
    let piece? : Option String :=
      if wasIn then some t
      else if let some p := dropPrefix? t "--" then some p
      else if opens then dropPrefix? t "/-"
      else none
    if opens && !t.contains "-/" then inBlock := true
    else if wasIn && t.contains "-/" then inBlock := false
    match piece? with
    | none =>
      if let some c := cur then raw := raw.push c
      cur := none
    | some p =>
      let p := trim (p.replace "-/" "")
      let ind := indentOf line
      match cur with
      | some (i, s) =>
        if i == ind || wasIn then cur := some (i, s ++ " " ++ p)
        else
          raw := raw.push (i, s)
          cur := some (ind, p)
      | none => cur := some (ind, p)
  if let some c := cur then raw := raw.push c
  let indents := (raw.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
  return raw.filterMap fun (i, s) =>
    if trim s == "" then none else some ((indents.findIdx? (· == i)).getD 0, trim s)

/-! ## Scopes -/

/-- The scope of a command: the current namespace and the `open` commands in force. -/
structure Scope where
  /-- The namespace, as entered by `namespace` commands. -/
  ns : Name := .anonymous
  /-- The `open` commands, as written: the namespaces are not resolved yet. -/
  opens : Array OpenDecl := #[]
  /-- The namespaces whose scoped notations are opened, as written. -/
  scopedNs : Array Name := #[]
  deriving Inhabited

/-- The `open` declarations of the words of an `open` command, and the namespaces whose scoped
notations it opens. -/
def parseOpen (ws : List String) : Array OpenDecl × Array Name :=
  let ids (xs : List String) := xs.filterMap fun w =>
    let w := (w.replace "(" "").replace ")" "" |>.replace "," ""
    if w == "" || w == "→" then none else some w.toName
  match ws with
  | "scoped" :: rest => (#[], (ids rest).toArray)
  | ns :: rest =>
    let nsName := ns.toName
    if rest.head? == some "hiding" then
      (#[.simple nsName (ids rest.tail)], #[nsName])
    else if rest.head? == some "renaming" then
      -- `a → b, c → d`
      let rec pairs : List Name → Array OpenDecl
        | a :: b :: more => (pairs more).push (.explicit b (nsName ++ a))
        | _ => #[]
      (pairs (ids rest.tail), #[])
    else if rest.head?.any (·.startsWith "(") then
      ((ids rest).toArray.map fun x => .explicit x (nsName ++ x), #[])
    else
      let all := (ns :: rest).map String.toName
      (all.toArray.map (.simple · []), all.toArray)
  | [] => (#[], #[])

/-- The words of a command line, without its attributes `@[...]` and its modifiers. -/
def commandWords (line : String) : List String :=
  let t := trim line
  let t := if t.startsWith "@[" then trim ((splitFirst t "]").2.getD "") else t
  let modifiers := ["noncomputable", "public", "private", "protected", "meta", "unsafe", "partial"]
  ((t.splitOn " ").filter (· ≠ "")).dropWhile modifiers.contains

/-- The scopes of a file, for each of its lines: the scope at line `i` (from `1`) is that of a
command starting there. Only the commands at the start of a line, without indentation, are read.
An `open ... in` applies to the declaration that follows it. -/
def fileScopes (lines : Array String) : Array Scope := Id.run do
  -- the stack of `namespace`, `section` and `mutual` blocks, with the scope before each of them
  let mut stack : Array (Bool × Name × Scope) := #[]
  let mut cur : Scope := {}
  let mut pending : Array OpenDecl := #[]
  let mut pendingScoped : Array Name := #[]
  let mut out : Array Scope := #[{}]
  -- the nesting of block comments at the start of the line
  let mut comment : Int := 0
  for line in lines do
    out := out.push
      { cur with opens := cur.opens ++ pending, scopedNs := cur.scopedNs ++ pendingScoped }
    let inComment := comment > 0
    comment := comment + (((line.splitOn "/-").length - 1 : Nat) : Int) -
      (((line.splitOn "-/").length - 1 : Nat) : Int)
    if inComment || line.startsWith " " || line.startsWith "\t" || trim line == "" then continue
    let ws := commandWords line
    match ws with
    | "namespace" :: n :: _ =>
      stack := stack.push (true, n.toName, cur)
      cur := { cur with ns := cur.ns ++ n.toName }
    | "section" :: _ | "mutual" :: _ =>
      stack := stack.push (false, .anonymous, cur)
    | "end" :: _ =>
      if let some (_, _, s) := stack.back? then
        cur := s
        stack := stack.pop
    | "open" :: rest =>
      let isIn := rest.getLast? == some "in"
      let (decls, scopedOpen) := parseOpen (if isIn then rest.dropLast else rest)
      if isIn then
        pending := pending ++ decls
        pendingScoped := pendingScoped ++ scopedOpen
        continue
      cur := { cur with opens := cur.opens ++ decls, scopedNs := cur.scopedNs ++ scopedOpen }
    | _ => pure ()
    -- an `open ... in` applies until the next command, the one it prefixes
    if !(line.startsWith "/-" || line.startsWith "@[") then
      pending := #[]
      pendingScoped := #[]
  return out

/-! ## Notations -/

/-- The keyword of a notation command, after its attributes and modifiers: `notation`, `infixl`,
..., or `none` if the command declares no notation. -/
def notationKeyword? (src : String) : Option String :=
  let ws := (commandWords src).dropWhile fun w =>
    w == "scoped" || w == "local" || w.startsWith "scoped["
  ws.head?.bind fun w =>
    let w := (splitFirst w ":").1
    if ["notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix"].contains w
    then some w else none

/-- Whether a command declares a notation. -/
def isNotationCommand (src : String) : Bool := (notationKeyword? src).isSome

/-- The first string literal of a text. -/
def firstLiteral? (src : String) : Option String :=
  match src.splitOn "\"" with
  | _ :: s :: _ => some s
  | _ => none

/-- The notation of a command, as a reader writes it: for `notation`, its atoms and variables
before `=>`, without precedences; for `infix` and the like, the operator between `a` and `b`. -/
def notationPattern (src : String) : Option String := Id.run do
  match notationKeyword? src with
  | some "infix" | some "infixl" | some "infixr" =>
    return (firstLiteral? src).map fun op => s!"a {trim op} b"
  | some "prefix" => return (firstLiteral? src).map fun op => s!"{trim op}a"
  | some "postfix" => return (firstLiteral? src).map fun op => s!"a{trim op}"
  | _ => pure ()
  let cs := src.toList.toArray
  let mut i := 0
  while i < cs.size && !wordAt cs i "notation" && !wordAt cs i "notation3" do i := i + 1
  if i == cs.size then return none
  i := i + (if wordAt cs i "notation3" then 9 else 8)
  let mut out := ""
  while i < cs.size && !matchAt cs i "=>" do
    let c := cs[i]!
    if c == '"' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '"' do j := j + 1
      out := out ++ slice cs (i + 1) j
      i := j + 1
    else if c.isWhitespace then i := i + 1
    else
      let mut j := i
      while j < cs.size && !cs[j]!.isWhitespace && cs[j]! != '"' do j := j + 1
      let w := slice cs i j
      -- a precedence `:65`, the name of a notation `(name := foo)` or a variable `x:65`
      if !w.startsWith ":" && !w.startsWith "(" && !w.endsWith ")" then
        out := out ++ (splitFirst w ":").1
      i := j
  let pattern := trim out
  return if pattern == "" then none else some pattern

end Showcase
