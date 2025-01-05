-- This module serves as the root of the `Y2023` library.
import «AoC».Basic
import «Y2023».Day01
import «Y2023».Day02
import «Y2023».Day03
import «Y2023».Day04
import «Y2023».Day05
import «Y2023».Day06
import «Y2023».Day07
import «Y2023».Day08
import «Y2023».Day09
import «Y2023».Day10
import «Y2023».Day11
import «Y2023».Day12
import «Y2023».Day13
import «Y2023».Day14
import «Y2023».Day15
import «Y2023».Day16
import «Y2023».Day17
import «Y2023».Day18
import «Y2023».Day19
import «Y2023».Day20

namespace Y2023

def solvers : List (Option String → IO AocProblem) := [
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
  Y2023.Day13.solve,
  Y2023.Day14.solve,
  Y2023.Day15.solve,
  Y2023.Day16.solve,
  Y2023.Day17.solve,
  Y2023.Day18.solve,
  Y2023.Day19.solve,
  Y2023.Day20.solve,
]

protected def solvedDays : Nat := solvers.length

protected def solve (n: Nat) (option: Option String) : IO AocProblem :=
  do
    let day := (min solvers.length n) - 1
    solvers.getD day (fun _ ↦ return AocProblem.new 2023 day) |> (· option)
