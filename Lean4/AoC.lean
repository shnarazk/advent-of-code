-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
import Aesop
import Batteries
import Cli
import «AoC».Basic
import «AoC».Color
import «AoC».Combinator
import «Y2023»
import «Y2024»

open AoC
open Cli

def events
    : Batteries.AssocList Nat (Nat × (Nat → Option String → IO AocProblem))
  := Batteries.AssocList.nil
    |>.cons 2023 (Y2023.solvedDays, Y2023.solve)
    |>.cons 2024 (Y2024.solvedDays, Y2024.solve)
-- #check events.find? 2023

def formatFloat (f : Float) (precision : Nat) : String :=
  let factor := Float.pow 10.0 precision.toFloat
  let rounded := (f * factor).round / factor
  let digits := max 1 rounded.abs |>.log10 |>.floor |>(· + 1)
    |>.toUInt16 |>.toNat
  rounded.toString ++ s!"/{digits}"
    |>.take (digits + precision + if f < 0 then 2 else 1)

-- #eval formatFloat 123.456789 2  -- Outputs "123.46"
-- #eval formatFloat 123.456789 4  -- Outputs "-123.4568"
-- #eval formatFloat (-123.456789) 2  -- Outputs "123.46"
-- #eval formatFloat (-123.456789) 4  -- Outputs "-123.4568"

def String.up_to_depth (depth : Nat) (s : String) (sep : Char := '/') : String :=
  s.split (· == sep)
  |>.reverse
  |>.take depth
  |>.reverse
  |> (String.intercalate sep.toString)

-- #eval "/a_a_a/bab/ccc/dadd/eeee/ff.g".up_to_depth 3

def AocProblem.show (self : AocProblem) : IO Unit :=
  match self.answers, self.time with
    | some ans, time => do
      IO.println s!"{Color.blue}- {self.input_name.up_to_depth 4}{Color.reset}: {formatFloat time 2}{Color.reset} msec"
      IO.println s!"{Color.green}  => {ans.1}, {ans.2}{Color.reset}"
    | _, _ => do return

def run (year: Nat) (day : Nat) (extra : Option String) : IO (Option AocProblem) := do
  match events.find? year with
    | some (days, solver) =>
       if day ≤ days
        then
          let (res, time) ← Aesop.time <| solver day extra
          do pure (some { res with time := (Float.ofNat time.nanos) / 1000000.0 })
        else do pure none
    | none => do pure none

def aoc_driver (year : Nat) (days : Array Nat) (alt : Option String) : IO Unit := do
  let solved := events.find? year |>.map (·.fst) |>.getD 1
  let results ← match days.size with
    | 0 => (List.range solved |>.mapM (fun d ↦ run year (d + 1) alt))
    | _ => days.toList.mapM (fun day ↦ run year day alt)
  let _ ← results.filterMap (·) |>.mapM (·.show)
  return ()

def benchmark_driver (year : Nat) : IO Unit := do
  let solved := events.find? year |>.map (·.fst) |>.getD 1
  let results ← List.range solved |>.mapM (fun d ↦ run year (d + 1) none)
  let json := results.filterMap (·) |>.map (·.toJson)
  -- IO.println s!"{results.filterMap (·) |>.map (·.toJson)}"
  let filename := System.mkFilePath [s!"execution_time_{year}.json"]
  IO.FS.writeFile filename s!"{json}"
  IO.println s!"dumped to '{filename}'"
  return ()

def aocCmd (p : Parsed) : IO UInt32 := do
  let year : Nat := p.flag! "year" |>.as! Nat
  let benchmark : Bool := p.hasFlag "benchmark"
  let days : Array Nat := if benchmark then #[] else p.variableArgsAs! Nat
  let alt : Option String := if p.hasFlag "alt"
    then p.flag! "alt" |>.as! String |>(some ·)
    else none
  -- let _ ← IO.println s!"day:{days}, year:{year}, benchmark:{benchmark}, alt:{alt}"
  if benchmark then benchmark_driver year else aoc_driver year days alt
  return 0

def aoc : Cmd := `[Cli|
  aoc VIA aocCmd ; ["0.5.2"]
  "Run Advent-of-Code codes in Lean4"

  FLAGS:
    y, year : Nat   ; "Set target year"
    a, alt : String ; "Run on a file which name ends with '-ALT.txt'"
    b, benchmark    ; "Run in benchmark mode, that dumps a JSON file"

  ARGS:
    ...day : Nat    ; "Set target days"

  EXTENSIONS:
    author "Author: shnarazk";
    defaultValues! #[("year", "2024")]
]

-- def main (args : List String) : IO Unit := do aoc_driver args

def main (args : List String) : IO UInt32 := aoc.validate args

-- #eval main <| "--year 2024 5".splitOn " "
