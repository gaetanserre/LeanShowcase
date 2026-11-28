/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Lean

/-!
# Utilities

Small helpers on strings, names, JSON, files and processes. They only use the parts of the core
API that are stable across the Lean versions that Showcase supports (`v4.29` onwards), since the
website is compiled with the toolchain of the formalization it presents.
-/

open Lean

namespace Showcase

/-! ## Strings -/

/-- `s` without leading and trailing whitespace. -/
def trim (s : String) : String := s.trimAscii.toString

/-- `s` without its first `n` characters. -/
def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- The first `n` characters of `s`. -/
def takeChars (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

/-- `s` without the prefix `pre`, if `s` starts with it. -/
def dropPrefix? (s pre : String) : Option String :=
  if s.startsWith pre then some (dropChars s pre.length) else none

/-- `s` without the suffix `suf`, if `s` ends with it. -/
def dropSuffix? (s suf : String) : Option String :=
  if s.endsWith suf then some (takeChars s (s.length - suf.length)) else none

/-- The number of leading spaces of `s`. -/
def indentOf (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

/-- The lines of `s`, without carriage returns. -/
def linesOf (s : String) : Array String := ((s.replace "\r" "").splitOn "\n").toArray

/-- Splits `s` at the first occurrence of `sep`. -/
def splitFirst (s sep : String) : String × Option String :=
  match s.splitOn sep with
  | a :: b :: rest => (a, some (sep.intercalate (b :: rest)))
  | _ => (s, none)

/-- Splits `Name | Label` into its trimmed parts. -/
def splitBar (s : String) : String × Option String :=
  match splitFirst s "|" with
  | (a, some b) => (trim a, if trim b == "" then none else some (trim b))
  | (a, none) => (trim a, none)

/-- `s` without surrounding single or double quotes. -/
def unquote (s : String) : String :=
  let s := trim s
  if s.length ≥ 2 && ((s.startsWith "\"" && s.endsWith "\"") ||
      (s.startsWith "'" && s.endsWith "'")) then
    takeChars (dropChars s 1) (s.length - 2)
  else s

/-- The characters of `cs` with indices in `[a, b)`, as a string. -/
def slice (cs : Array Char) (a b : Nat) : String := String.ofList (cs.extract a b).toList

/-- Whether the characters of `pat` occur in `cs` at index `i`. -/
def matchAt (cs : Array Char) (i : Nat) (pat : String) : Bool := Id.run do
  let mut j := i
  for c in pat.toList do
    if cs[j]? != some c then return false
    j := j + 1
  return true

/-- The text of `lines` (the lines of a file) in the range `r`. Lines count from `1`, columns count
codepoints from `0`. -/
def sliceRange (lines : Array String) (r : DeclarationRange) : String := Id.run do
  let first := r.pos.line - 1
  let last := r.endPos.line - 1
  let mut out : Array String := #[]
  for i in [first:last + 1] do
    let mut line := lines[i]?.getD ""
    if i == last then line := takeChars line r.endPos.column
    if i == first then line := dropChars line r.pos.column
    out := out.push line
  return "\n".intercalate out.toList

/-! ## Names -/

/-- A name as written in Lean source, without `«»` escapes. -/
def nameStr (n : Name) : String := n.toString (escape := false)

/-- The name of a declaration as written by its author: without the `_private` prefix. -/
def userName (n : Name) : Name := privateToUserName n

/-! ## JSON -/

/-- The JSON of an optional string: `null` when absent. -/
def jsonOpt (s : Option String) : Json := (s.map Json.str).getD .null

/-- The JSON of a name. -/
def jsonName (n : Name) : Json := .str (nameStr n)

/-- The JSON object of a list of entries, without those whose value is `null`. -/
def jsonObj (kvs : List (String × Json)) : Json :=
  Json.mkObj (kvs.filter fun (_, v) => !(v matches .null))

/-! ## Files and processes -/

/-- The content of a file, or `none` if it cannot be read. -/
def readFile? (p : System.FilePath) : IO (Option String) := do
  try return some (← IO.FS.readFile p) catch _ => return none

/-- The JSON content of a file, or `none` if it is missing or malformed. -/
def readJson? (p : System.FilePath) : IO (Option Json) := do
  return (← readFile? p).bind fun s => (Json.parse s).toOption

/-- Copies `src` to `dst`, creating the folders of `dst`. -/
def copyFile (src dst : System.FilePath) : IO Unit := do
  if let some d := dst.parent then IO.FS.createDirAll d
  IO.FS.writeBinFile dst (← IO.FS.readBinFile src)

/-- The trimmed output of a command, or `none` if it fails. -/
def runCmd? (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    return if out.exitCode == 0 then some (trim out.stdout) else none
  catch _ => return none

/-- Prints a message. -/
def info (msg : String) : IO Unit := do
  IO.println s!"showcase: {msg}"
  (← IO.getStdout).flush

/-- Prints a warning. -/
def warn (msg : String) : IO Unit := IO.eprintln s!"showcase: warning: {msg}"

end Showcase
