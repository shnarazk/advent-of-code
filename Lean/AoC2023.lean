-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
-- import Mathlib.Data.Rat.Basic
-- import Mathlib.Data.Real.Basic
import Aesop
import Batteries
import «AoC».Combinator
import «AoC2023».Day01
import «AoC2023».Day02
import «AoC2023».Day03
import «AoC2023».Day04
import «AoC2023».Day05
import «AoC2023».Day06
import «AoC2023».Day07
import «AoC2023».Day08
import «AoC2023».Day09
import «AoC2023».Day10
import «AoC2023».Day11
import «AoC2023».Day12

def lastDay := 12

theorem DayIsNotZero: 12 > 0 := by simp

def solved : List (Fin 12) := List.range lastDay |>.map (Fin.ofNat' · DayIsNotZero)

def run (day : Fin 12) (extra : Option String) : IO Unit := do
  let f ← dataFileName 2023 (1 + day) extra
  let (results, time) ← match day with
    |  0 => Aesop.time <| day01 extra
    |  1 => Aesop.time <| day02 extra
    |  2 => Aesop.time <| day03 extra
    |  3 => Aesop.time <| day04 extra
    |  4 => Aesop.time <| day05 extra
    |  5 => Aesop.time <| day06 extra
    |  6 => Aesop.time <| day07 extra
    |  7 => Aesop.time <| day08 extra
    |  8 => Aesop.time <| day09 extra
    |  9 => Aesop.time <| day10 extra
    | 10 => Aesop.time <| day11 extra
    | 11 => Aesop.time <| day12 extra
  IO.println s!"{color.blue}- {f}{color.reset}: {time.printAsMillis}{color.reset}"
  IO.println s!"{color.green}  => {results.fst}, {results.snd}{color.reset}"
