-- This module serves as the root of the `AoC` library.
-- Import modules here that should be built as part of the library.
-- import Mathlib.Data.Rat.Basic
-- import Mathlib.Data.Real.Basic
import Std
import Aesop
import «AoC».Combinator
import «AoC».Day01
import «AoC».Day02
import «AoC».Day03
import «AoC».Day04
import «AoC».Day05
import «AoC».Day06
import «AoC».Day07
import «AoC».Day08
import «AoC».Day09
import «AoC».Day10
import «AoC».Day11
import «AoC».Day12

def solved : List Nat := List.iota 12 |>.reverse

#eval solved

def run (day : Nat) (extra : Option String) : IO Unit := do
  let f ← dataFileName 2023 day extra
  IO.println s!"{color.blue}- {f}{color.reset}"
  let result ← match day with
    |  1 => Aesop.time' <| day01 extra
    |  2 => Aesop.time' <| day02 extra
    |  3 => Aesop.time' <| day03 extra
    |  4 => Aesop.time' <| day04 extra
    |  5 => Aesop.time' <| day05 extra
    |  6 => Aesop.time' <| day06 extra
    |  7 => Aesop.time' <| day07 extra
    |  8 => Aesop.time' <| day08 extra
    |  9 => Aesop.time' <| day09 extra
    | 10 => Aesop.time' <| day10 extra
    | 11 => Aesop.time' <| day11 extra
    | 12 => Aesop.time' <| day12 extra
    | _  => Aesop.time' <| return ()
  IO.println s!"{color.green} => {result.printAsMillis}{color.reset}"
