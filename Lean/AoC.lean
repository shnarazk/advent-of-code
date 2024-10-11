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
    : Batteries.AssocList Nat (Nat × (Nat → Option String → IO AocProblem))
  := Batteries.AssocList.nil
--    |>.cons 2023 (Y2023.solvedDays, Y2023.solve)
    |>.cons 2024 (Y2024.solvedDays, Y2024.solve)
-- #check events.find? 2023

def run (year: Nat) (day : Nat) (extra : Option String) : IO Unit := do
  let f ← dataFileName year day extra
  let ans ← match events.find? year with
    | some (days, solver) =>
       if day ≤ days
        then
          let (res, time) ← Aesop.time <| solver day extra
          do pure (some { res with time := (Float.ofNat time.nanos) / 1000.0 })
        else do pure none
    | none => do pure none
  match ans with
    | some ans => match ans.answers, ans.time with
        | some ans, time =>
          IO.println s!"{Color.blue}- {f}{Color.reset}: {time}{Color.reset}"
          IO.println s!"{Color.green}  => {ans.1}, {ans.2}{Color.reset}"
        | _, _ => do return
    | none     => IO.println s!"error"

def aoc_driver (args : List String) : IO Unit := do
  let extra := args.get? 2
  if let some year := (args.get? 0).map (·.toNat!)
    then
      let solved := events.find? year |>.map (·.fst) |>.getD 1
      match (args.get? 1).map (·.toNat!) with
        | some day => run year day extra
        | none     => (List.range solved |>.mapM (fun d ↦ run year (d + 1) extra)) *> pure ()

def main (args : List String) : IO Unit := do aoc_driver args
