module

public import «AoC».Basic
public import «Y2025».Day01
public import «Y2025».Day02
public import «Y2025».Day03
public import «Y2025».Day04
public import «Y2025».Day05
public import «Y2025».Day06
public import «Y2025».Day07
public import «Y2025».Day08
public import «Y2025».Day09
-- public import «Y2025».Day10
-- public import «Y2025».Day11
-- public import «Y2025».Day12

@[expose] public section

namespace Y2025

def solvers : List (Option String → IO AocProblem) := [
  Y2025.Day01.solve,
  Y2025.Day02.solve,
  Y2025.Day03.solve,
  Y2025.Day04.solve,
  Y2025.Day05.solve,
  Y2025.Day06.solve,
  Y2025.Day07.solve,
  Y2025.Day08.solve,
  Y2025.Day09.solve,
  -- Y2025.Day10.solve,
  -- Y2025.Day11.solve,
  -- Y2025.Day12.solve,
]

protected def solvedDays : Nat := solvers.length

protected def solve (n: Nat) (option: Option String) : IO AocProblem :=
  do
    let day := (min solvers.length n) - 1
    solvers.getD day (fun _ ↦ return AocProblem.new 2025 day) |> (· option)
