import «AoC».Basic
import «Y2024».Day01
import «Y2024».Day02
import «Y2024».Day03

namespace Y2024

def solvers : List (Option String → IO AocProblem) := [
  Day01.solve,
  Day02.solve,
  Day03.solve,
]

def there_are_solvers : 0 < solvers.length := by
  have count : solvers.length = 3 := by exact rfl
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
          exact Nat.lt_add_one (solvers.length - 1) -- there_are_solvers
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
