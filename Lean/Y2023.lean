-- This module serves as the root of the `Y` library.
import «Y2023».Day01
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

namespace Y2023

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

def solvedDays : Nat := Y2023.solvers.length

def solve (n: Nat) (h: (n - 1) < Y2023.solvers.length) (options: Option String) : IO Answers :=
  do
    let solver := Y2023.solvers.get (Fin.mk (n - 1) h) 
    solver options
