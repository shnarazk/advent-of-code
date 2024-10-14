/- This file is copied from lean-community/mathlib4/scripts/lint-style.lean -/
/- Then modified how to gather and handle module names -/
/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This files defines the `lint-style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.
-/

open System
open Cli Mathlib.Linter.TextBased

def broadImportsLinter' : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  -- All import statements must be placed "at the beginning" of the file:
  -- we can have any number of blank lines, imports and single or multi-line comments.
  -- Doc comments, however, are not allowed: there is no item they could document.
  let mut inDocComment : Bool := False
  let mut lineNumber := 1
  for line in lines do
    if inDocComment then
      if line.endsWith "-/" then
        inDocComment := False
    else
      -- If `line` is just a single-line comment (starts with "--"), we just continue.
      if line.startsWith "/-" then
        inDocComment := True
      else if let some (rest) := line.dropPrefix? "import " then
          -- If there is any in-line or beginning doc comment on that line, trim that.
          -- Small hack: just split the string on space, "/" and "-":
          -- none of these occur in module names, so this is safe.
          if let some name := ((toString rest).split (" /-".contains ·)).head? then
            if name == "Lake" || name.startsWith "Lake." then
              errors := errors.push (StyleError.broadImport BroadImports.Lake, lineNumber)
      lineNumber := lineNumber + 1
  return (errors, none)

/-- All text-based linters registered in this file. -/
def allLinters' : Array TextbasedLinter := #[
    -- copyrightHeaderLinter,
    adaptationNoteLinter, broadImportsLinter', duplicateImportsLinter
  ]

def lintFile' (path : FilePath) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext × Option (Array String)) := do
  let mut errors := #[]
  -- Whether any changes were made by auto-fixes.
  let mut changes_made := false
  -- Check for windows line endings first: as `FS.lines` treats Unix and Windows lines the same,
  -- we need to analyse the actual file contents.
  let contents ← IO.FS.readFile path
  let replaced := contents.crlfToLf
  if replaced != contents then
    changes_made := true
    errors := errors.push (ErrorContext.mk StyleError.windowsLineEnding 1 path)
  let lines := (replaced.splitOn "\n").toArray

  -- We don't need to run any further checks on imports-only files.
  if isImportsOnlyFile lines then
    return (errors, if changes_made then some lines else none)

  -- All further style errors raised in this file.
  let mut allOutput := #[]
  -- A working copy of the lines in this file, modified by applying the auto-fixes.
  let mut changed := lines

  for lint in allLinters' do
    let (err, changes) := lint changed
    allOutput := allOutput.append (Array.map (fun (e, n) ↦ #[(ErrorContext.mk e n path)]) err)
    if let some c := changes then
      changed := c
      changes_made := true
  -- This list is not sorted: for github, this is fine.
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return (errors, if changes_made then some changed else none)


def lintModules' (moduleNames : Array String) (style : ErrorFormat) (fix : Bool) : IO UInt32 := do
  -- Read the `nolints` file, with manual exceptions for the linter.
  let nolints ← IO.FS.lines ("scripts" / "nolints-style.txt")
  let styleExceptions := parseStyleExceptions nolints

  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := (mkFilePath (module.split (· == '.'))).addExtension "lean"

    let (errors, changed) := ← lintFile' path styleExceptions
    if let some c := changed then
      if fix then
        let _ := ← IO.FS.writeFile path ("\n".intercalate c.toList)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1

  formatErrors allUnexpectedErrors style
  if allUnexpectedErrors.size > 0 then
    IO.eprintln s!"error: found {allUnexpectedErrors.size} new style error(s)"
  return numberErrorFiles

/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let style : ErrorFormat := match args.hasFlag "github" with
    | true => ErrorFormat.github
    | false => ErrorFormat.humanReadable
  let fix := args.hasFlag "fix"
  -- Read all module names to lint.
  let mut allModules := #[]
  let key := "import "
  for s in ["AoC.lean", "Y2023.lean", "Y2024.lean"] do
    -- allModules := allModules.append ((← IO.FS.lines s).map (·.stripPrefix "import "))
    let lines := (← IO.FS.lines s).filterMap (
      fun l ↦ if l.startsWith key then some (l.stripPrefix key) else none)
    let modules := lines.map (·.toList.filter
      (fun c ↦ c != '«' && c != '»') |>.asString)
    allModules := allModules.append modules
  -- note: since we manually add "Batteries" to "Mathlib.lean", we remove it here manually
  -- allModules := allModules.erase "Batteries"
  allModules := ["Aesop", "Batteries", "Cli"].foldl (fun am s ↦ am.erase s) allModules
  let numberErrorFiles ← lintModules' allModules style fix
  -- If run with the `--fix` argument, return a zero exit code.
  -- Otherwise, make sure to return an exit code of at most 125,
  -- so this return value can be used further in shell scripts.
  if args.hasFlag "fix" then
    return 0
  else return min numberErrorFiles 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
-- so far, no help options or so: perhaps that is fine?
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    fix;        "Automatically fix the style error, if possible"
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
