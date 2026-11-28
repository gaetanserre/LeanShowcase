/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase

/-!
# `lake exe showcase`
-/

open Showcase

/-- The help of the command. -/
def usage : String :=
  "usage: lake exe showcase [FILE] [options]

Generates the website described by FILE (default: showcase.md).

  -o, --out DIR              the output folder (default: the key `output`, or _site)
  --module M                 the module to present, instead of the key `module`
                             (FILE is then optional)
  --comparator               run `lake comparator --json --paranoid` in the project first
  --no-paranoid              ... without the external checkers of the toolchain
  --inadvisably-no-sandbox   ... without the sandbox of comparator (macOS has no `bwrap`)"

/-- Parses the command line. -/
def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "-o" :: d :: rest, o | "--out" :: d :: rest, o => parseArgs rest { o with out := some d }
  | "--module" :: m :: rest, o => parseArgs rest { o with module := some m }
  | "--comparator" :: rest, o => parseArgs rest { o with comparator := true }
  | "--no-paranoid" :: rest, o => parseArgs rest { o with paranoid := false }
  | "--inadvisably-no-sandbox" :: rest, o => parseArgs rest { o with noSandbox := true }
  | "-h" :: _, _ | "--help" :: _, _ => .error ""
  | f :: rest, o =>
    if f.startsWith "-" then .error s!"unknown option {f}" else parseArgs rest { o with doc := f }

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg =>
    if msg != "" then IO.eprintln s!"showcase: {msg}"
    IO.println usage
    return if msg == "" then 0 else 1
  | .ok o =>
    try
      generate o
      return 0
    catch e =>
      IO.eprintln s!"showcase: error: {e}"
      return 1
