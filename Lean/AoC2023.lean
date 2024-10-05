-- This module serves as the root of the `AoC` library.
import «AoC».Basic
import «AoC2023».Day01
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

namespace AoC2023

protected def solvers := [
  Y2023.Day01.solve,
  Y2023.Day02.solve,
  Y2023.Day03.solve,
  Y2023.Day04.solve,
  Y2023.Day05.solve,
  Y2023.Day06.solve,
  Y2023.Day07.solve,
  Y2023.Day08.solve,
  Y2023.Day09.solve,
  Y2023.Day10.solve,
  Y2023.Day11.solve,
  Y2023.Day12.solve,
]

def solvedDays : Nat := AoC2023.solvers.length

def solve (n: Nat) (h: (n - 1) < AoC2023.solvers.length) (options: Option String) : IO Answers :=
  do
    let solver := AoC2023.solvers.get (Fin.mk (n - 1) h) 
    solver options
