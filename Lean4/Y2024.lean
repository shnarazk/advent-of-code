module

public import «AoC».Basic
public import «Y2024».Day01
public import «Y2024».Day02
public import «Y2024».Day03
public import «Y2024».Day04
public import «Y2024».Day05
public import «Y2024».Day06
public import «Y2024».Day07
public import «Y2024».Day08
public import «Y2024».Day09
public import «Y2024».Day10
public import «Y2024».Day11
public import «Y2024».Day12

@[expose] public section

namespace Y2024

def solvers : List (Option String → IO AocProblem) := [
  Y2024.Day01.solve,
  Y2024.Day02.solve,
  Y2024.Day03.solve,
  Y2024.Day04.solve,
  Y2024.Day05.solve,
  Y2024.Day06.solve,
  Y2024.Day07.solve,
  Y2024.Day08.solve,
  Y2024.Day09.solve,
  Y2024.Day10.solve,
  Y2024.Day11.solve,
  Y2024.Day12.solve,
]

protected def solvedDays : Nat := solvers.length

protected def solve (n: Nat) (option: Option String) : IO AocProblem :=
  do
    let day := (min solvers.length n) - 1
    solvers.getD day (fun _ ↦ return AocProblem.new 2024 day) |> (· option)
