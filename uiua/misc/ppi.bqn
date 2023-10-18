n‿chunk ← ⟨50×1000×1000,1000⟩
seed‿span ← ⟨3+4×↕chunk,4×chunk⟩
sum ← 0
Term ← {
  diff ← +´÷×⟜(¯2⊸+)𝕩+seed
  sum diff⊸+↩
  𝕩+span
}
Term⍟(n÷chunk)0
•Show pi ← 8×sum
