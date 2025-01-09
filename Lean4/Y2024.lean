import «AoC».Basic
import «Y2024».Day01
import «Y2024».Day02
import «Y2024».Day03
import «Y2024».Day04
import «Y2024».Day05
import «Y2024».Day06
import «Y2024».Day07
import «Y2024».Day08
import «Y2024».Day09
import «Y2024».Day10

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
]

protected def solvedDays : Nat := solvers.length

protected def solve (n: Nat) (option: Option String) : IO AocProblem :=
  do
    let day := (min solvers.length n) - 1
    solvers.getD day (fun _ ↦ return AocProblem.new 2024 day) |> (· option)
