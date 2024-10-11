-- This module serves as the root of the `Y` library.
import «AoC».Basic
import «Y2023».Day01
-- import «Y2023».Day01
-- import «Y2023».Day02
-- import «Y2023».Day03
-- import «Y2023».Day04
-- import «Y2023».Day05
-- import «Y2023».Day06
-- import «Y2023».Day07
-- import «Y2023».Day08
-- import «Y2023».Day09
-- import «Y2023».Day10
-- import «Y2023».Day11
-- import «Y2023».Day12

namespace Y2023

def solvers := [
  Y2023.Day01.solve,
  -- Y2023.Day02.solve,
  -- Y2023.Day03.solve,
  -- Y2023.Day04.solve,
  -- Y2023.Day05.solve,
  -- Y2023.Day06.solve,
  -- Y2023.Day07.solve,
  -- Y2023.Day08.solve,
  -- Y2023.Day09.solve,
  -- Y2023.Day10.solve,
  -- Y2023.Day11.solve,
  -- Y2023.Day12.solve,
]

def there_are_solvers : 0 < solvers.length := by
  have count : solvers.length = 1 := by exact rfl
  simp [count]

protected def solvedDays : Nat := solvers.length

protected def solve (n: Nat) (option: Option String) : IO AocProblem :=
  do
    let day := min solvers.length n
    have h : day - 1 < solvers.length := by
      have day_def : day = min solvers.length n := by exact rfl
      by_cases choice : solvers.length ≤ n
      {
          have : min solvers.length n = solvers.length := by
            exact Nat.min_eq_left choice
          rw [this] at day_def
          simp [day_def]
          exact there_are_solvers
      }
      {

        have H : solvers.length > n := by exact Nat.gt_of_not_le choice
        have H' : n ≤ solvers.length := by exact Nat.le_of_not_ge choice
        have : min solvers.length n = n := by exact Nat.min_eq_right H'
        simp [this] at day_def
        rw [day_def]
        by_cases n0 : n = 0
        { simp [n0] ; exact there_are_solvers }
        {
          have N1 : n - 1 < n := by exact Nat.sub_one_lt n0
          exact Nat.lt_trans N1 H
        }
      }
    solvers.get (Fin.mk (day - 1) h) |> (· option)
