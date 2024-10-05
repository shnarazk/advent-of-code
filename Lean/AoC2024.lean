import «AoC».Basic
import «AoC2024».Day01

namespace AoC2024

protected def solvers : List (Option String → IO Answers) := [
  Y2024.Day01.solve,
]

protected def solvedDays : Nat := AoC2024.solvers.length

protected def solve (n: Nat) (h: (n - 1) < AoC2024.solvers.length) (options: Option String) : IO Answers :=
  do
    let solver := AoC2024.solvers.get (Fin.mk (n - 1) h) 
    solver options
