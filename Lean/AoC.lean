-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
-- import Mathlib.Data.Rat.Basic
-- import Mathlib.Data.Real.Basic
import Aesop
import Batteries
import «AoC».Basic
import «AoC».Color
import «AoC».Combinator
import «Y2023»
import «Y2024»
open AoC

def run (year: Nat) (day : Nat) (extra : Option String) : IO Unit := do
  let f ← dataFileName year day extra
  let ans ← match year with
    | 2023 =>
      if h : day - 1 < Y2023.solvedDays
        then
          let ans ← Aesop.time <| Y2023.solve day h extra
          pure (some (ans))
        else
          do pure none
    | 2024 =>
      if h : day - 1 < Y2024.solvedDays
        then
          let res ← Aesop.time <| Y2024.solve day h extra
          pure (some (res))
        else
          do pure none
    | _ => do pure none
  match ans with
    | some (results, time) => do
      IO.println s!"{Color.blue}- {f}{Color.reset}: {time.printAsMillis}{Color.reset}"
      IO.println s!"{Color.green}  => {results.fst}, {results.snd}{Color.reset}"
    | _ => do return

def aoc_driver (args : List String) : IO Unit := do
  let extra := args.get? 2
  match (args.get? 0).map (·.toNat!) with
  | some year => do
      let solved := match year with
        | 2023 => List.range Y2023.solvedDays
        | 2024 => List.range Y2024.solvedDays
        | _ => []
      match (args.get? 1).map (·.toNat!) with
        | some day => run year day extra
        | none     => let _ ← do (solved.mapM (run year · extra))
  | none => return

def main (args : List String) : IO Unit := do aoc_driver args
