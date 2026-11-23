/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Showcase

/-!
# `lake exe showcase`

Usage: `lake exe showcase [showcase.md] [--out DIR] [--comparator [--no-paranoid]
[--inadvisably-no-sandbox]]`.
-/

open Showcase

/-- Parses the command line. -/
def parseArgs : List String → Showcase.Options → Except String Showcase.Options
  | [], o => .ok o
  | "--out" :: d :: rest, o => parseArgs rest { o with out := some d }
  | "-o" :: d :: rest, o => parseArgs rest { o with out := some d }
  | "--comparator" :: rest, o => parseArgs rest { o with comparator := true }
  | "--no-paranoid" :: rest, o => parseArgs rest { o with paranoid := false }
  | "--inadvisably-no-sandbox" :: rest, o => parseArgs rest { o with noSandbox := true }
  | ("--help" :: _), _ => .error "usage"
  | f :: rest, o => parseArgs rest { o with doc := f }

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error _ =>
    IO.println "usage: lake exe showcase [showcase.md] [--out DIR] \
      [--comparator [--no-paranoid] [--inadvisably-no-sandbox]]\n\n\
      --comparator               run `lake comparator --json --paranoid` in the project first\n\
                                 and show its report on the website\n\
      --no-paranoid              without the external checkers of the toolchain\n\
      --inadvisably-no-sandbox   without the sandbox of comparator (macOS has no `bwrap`)"
    return 1
  | .ok o =>
    try
      generate o
      return 0
    catch e =>
      IO.eprintln s!"showcase: error: {e}"
      return 1
