module

-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
-- import Aesop
public import Batteries
public import Cli
public import «AoC».Basic
public import «AoC».Color
public import «AoC».Combinator
public import «Y2023»
public import «Y2024»
public import «Y2025»

@[expose] public section

open AoC
open Cli

universe u

/--
  Measures the execution time of a monadic computation.

  Given a monadic computation, this function returns both the result of the computation
  and the time it took to execute in nanoseconds.
-/
@[inline]
def elapsedTime {α : Type} {m : Type → Type u} [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Nat) := do
  let beg ← IO.monoNanosNow
  let val ← x
  let fin ← IO.monoNanosNow
  return (val, fin - beg)

/--
  Assoc List of year → day → part → solver function
-/
def events
    : Batteries.AssocList Nat (Nat × (Nat → Option String → IO AocProblem))
  := Batteries.AssocList.nil
    |>.cons 2023 (Y2023.solvedDays, Y2023.solve)
    |>.cons 2024 (Y2024.solvedDays, Y2024.solve)
    |>.cons 2025 (Y2025.solvedDays, Y2025.solve)
-- #check events.find? 2023

/--
  Format a `Float` with a fixed number of digits after the decimal point.

  The number is rounded to `precision` decimal places, and then converted to a `String`.
  The implementation additionally truncates the produced string to the expected width.

  Notes:
  * `precision = 0` produces an integer-like string (after rounding).
  * Extremely large/small floats may still render using scientific notation depending on
    `Float.toString`, in which case the truncation may not behave as desired.
-/
def formatFloat (f : Float) (precision : Nat) : String :=
  let factor := Float.pow 10.0 precision.toFloat
  let rounded := (f * factor).round / factor
  let digits := max 1 rounded.abs |>.log10 |>.floor |>(· + 1)
    |>.toUInt16 |>.toNat
  rounded.toString ++ s!"/{digits}"
    |>.take (digits + precision + if f < 0 then 2 else 1)
    |>.toString

#guard formatFloat 123.456789 2 == "123.46"
#guard formatFloat (-123.456789) 4 == "-123.4568"
#guard formatFloat (-123.456789) 2 == "-123.46"
#guard formatFloat (-123.456789) 4 == "-123.4568"

/--
  Truncate a path-like `String` to its last `depth` components.

  The string `s` is split on the separator character `sep` (default: `/`),
  then only the last `depth` components are kept and re-joined using `sep`.

  Examples:
  * `"/a/b/c/d".up_to_depth 2` returns `"c/d"`
  * `"a/b".up_to_depth 10` returns `"a/b"` (depth larger than the number of components)

  Notes:
  * Consecutive separators and leading/trailing separators produce empty components,
    following the behavior of `String.splitToList`.
-/
def String.up_to_depth (depth : Nat) (s : String) (sep : Char := '/') : String :=
  s.splitToList (· == sep)
  |>.reverse
  |>.take depth
  |>.reverse
  |> (String.intercalate sep.toString)

-- #eval "/a_a_a/bab/ccc/dadd/eeee/ff.g".up_to_depth 3

/-- Print the result to stout. -/
def AocProblem.show (self : AocProblem) : IO Unit :=
  match self.answers, self.time with
    | some ans, time => do
      IO.println s!"{Color.blue}- {self.input_name.up_to_depth 4}{Color.reset}: {formatFloat time 2}{Color.reset} msec"
      IO.println s!"{Color.green}  => {ans.1}, {ans.2}{Color.reset}"
    | _, _ => do return

/-- Solve the puzzle for year and day in IO monad and return the result as `Option AoCProblem`.
-/
def run (year: Nat) (day : Nat) (alt : Option String) : IO (Option AocProblem) := do
  match events.find? year with
    | some (days, solver) =>
       if day ≤ days
        then
          let (res, time) ← elapsedTime <| solver day alt
          do pure (some { res with time := time.toFloat  / 1000000.0 })
        else do
          IO.println s!"{Color.red}Y{year} day{day} has not been solved!{Color.reset}"
          pure none
    | none => do
       IO.println s!"{Color.red}Year {year} is not a valid year!{Color.reset}"
       pure none

/--
  Solve the puzzle of year and day like `run`. But This returns `IO Unit`.
-/
def aoc_driver (year : Nat) (days : Array Nat) (alt : Option String) : IO Unit := do
  let solved := events.find? year |>.map (·.fst) |>.getD 1
  let results ← match days.size with
    | 0 => (List.range solved |>.mapM (fun d ↦ run year (d + 1) alt))
    | _ => days.toList.mapM (fun day ↦ run year day alt)
  let _ ← results.filterMap (·) |>.mapM (·.show)
  return ()

/--
  Run all puzzles of `year` and dump the result to a JSON file.
-/
def benchmark_driver (year : Nat) : IO Unit := do
  let solved := events.find? year |>.map (·.fst) |>.getD 1
  let results ← List.range solved |>.mapM (fun d ↦ run year (d + 1) none)
  let json := results.filterMap (·) |>.map (·.toJson)
  -- IO.println s!"{results.filterMap (·) |>.map (·.toJson)}"
  let filename := System.mkFilePath ["misc", s!"{year}", "execution_time.json"]
  if let some dir := filename.parent then
    let dir_exists ← dir.pathExists
    if !dir_exists then IO.FS.createDir dir
  IO.FS.writeFile filename s!"{json}"
  IO.println s!"dumped to '{filename}'"
  return ()

/-- The entry point called by command line argument parser -/
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

/-- command line argument definition -/
def aoc : Cmd := `[Cli|
  aoc VIA aocCmd ; ["0.6.1"]
  "Run Advent-of-Code codes in Lean4"

  FLAGS:
    y, year : Nat   ; "Set target year"
    a, alt : String ; "Run on a file which name ends with '-ALT.txt'"
    b, benchmark    ; "Run in benchmark mode, that dumps a JSON file"

  ARGS:
    ...day : Nat    ; "Set target days"

  EXTENSIONS:
    author "Author: shnarazk";
    defaultValues! #[("year", "2025")]
]

-- def main (args : List String) : IO Unit := do aoc_driver args

/-- the entry point -/
def main (args : List String) : IO UInt32 := aoc.validate args

-- #eval main <| "--year 2025 1".splitOn " "
