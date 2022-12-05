#!/usr/bin/env cbqn
⟨ParseInts, DataFile⟩ ← •Import "../lib.bqn"
lines ← •FLines "data/2022/input-day05.txt" DataFile •args 
head ← ⊑0⊐˜≠¨ lines
•Show head
•Show ParseInts¨ (1+head)↓ lines

# Part1 ← { ⟨a, b, x, y⟩ : ((a≤x) ∧ (y≤b)) ∨ ((x≤a) ∧ (b≤y)) }
# •Show +´ Part1¨ lines

# Part2 ← { ⟨a, b, x, y⟩ : (x≤b) ∧ (a≤y) }
# •Show +´ Part2¨ lines
