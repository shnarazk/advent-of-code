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

def events
    : Batteries.AssocList Nat (Nat × (Nat → Option String → IO Answers))
  := Batteries.AssocList.nil
    |>.cons 2023 (Y2023.solvedDays, Y2023.solve)
    |>.cons 2024 (Y2024.solvedDays, Y2024.solve)
-- #check events.find? 2023

def run (year: Nat) (day : Nat) (extra : Option String) : IO Unit := do
  let f ← dataFileName year day extra
  let ans ← match events.find? year with
    | some (days, solver) =>
       if day ≤ days
        then pure $ some (← Aesop.time <| solver day extra)
        else do pure none
    | none => do pure none
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
        | none     => let _ ← do (solved.mapM (fun d ↦ run year (d + 1) extra))
  | none => return

def main (args : List String) : IO Unit := do aoc_driver args
