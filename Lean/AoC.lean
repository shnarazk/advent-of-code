-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
import Aesop
import Batteries
import «AoC».Basic
import «AoC».Color
import «AoC».Combinator
import «Y2023»
import «Y2024»
open AoC

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
    |>.take (digits + if f < 0 then 4 else 3)

-- #eval formatFloat 123.456789 2  -- Outputs "123.46"

def String.up_to_depth (depth : Nat) (s : String) (sep : Char := '/') : String :=
  s.split (· == sep)
  |>.reverse
  |>.take depth
  |>.reverse
  |> (String.intercalate sep.toString)

-- #eval "/a_a_a/bab/ccc/dadd/eeee/ff.g".up_to_depth 3

def run (year: Nat) (day : Nat) (extra : Option String) : IO Unit := do
  let f ← dataFileName year day extra
  let ans ← match events.find? year with
    | some (days, solver) =>
       if day ≤ days
        then
          let (res, time) ← Aesop.time <| solver day extra
          do pure (some { res with time := (Float.ofNat time.nanos) / 1000000.0 })
        else do pure none
    | none => do pure none
  match ans with
    | some ans => match ans.answers, ans.time with
        | some ans, time =>
          IO.println s!"{Color.blue}- {f.up_to_depth 4}{Color.reset}: {formatFloat time 2}{Color.reset} msec"
          IO.println s!"{Color.green}  => {ans.1}, {ans.2}{Color.reset}"
        | _, _ => do return
    | none     => IO.println s!"Configuration error at AoC.run"

def aoc_driver (args : List String) : IO Unit := do
  let extra := args.get? 2
  if let some year := (args.get? 0).map (·.toNat!)
    then
      let solved := events.find? year |>.map (·.fst) |>.getD 1
      match (args.get? 1).map (·.toNat!) with
        | some day => run year day extra
        | none     => (List.range solved |>.mapM (fun d ↦ run year (d + 1) extra)) *> pure ()

def main (args : List String) : IO Unit := do aoc_driver args
