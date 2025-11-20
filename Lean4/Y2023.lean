module

-- This module serves as the root of the `Y2023` library.
public import «AoC».Basic
public import «Y2023».Day01
public import «Y2023».Day02
public import «Y2023».Day03
public import «Y2023».Day04
public import «Y2023».Day05
public import «Y2023».Day06
public import «Y2023».Day07
public import «Y2023».Day08
public import «Y2023».Day09
public import «Y2023».Day10
public import «Y2023».Day11
public import «Y2023».Day12
public import «Y2023».Day13
public import «Y2023».Day14
public import «Y2023».Day15
public import «Y2023».Day16
public import «Y2023».Day17
public import «Y2023».Day18
public import «Y2023».Day19
public import «Y2023».Day20

@[expose] public section

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
