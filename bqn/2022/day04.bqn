#!/usr/bin/env cbqn
⟨ParseInts, DataFile⟩ ← •Import "../lib.bqn"
lines ← ParseInts¨ { '-':','; 𝕩 }¨¨ •FLines "data/2022/input-day04.txt" DataFile •args

Part1 ← { ⟨a, b, x, y⟩ : ((a≤x) ∧ (y≤b)) ∨ ((x≤a) ∧ (b≤y)) }
•Show +´ Part1¨ lines

Part2 ← { ⟨a, b, x, y⟩ : (x≤b) ∧ (a≤y) }
•Show +´ Part2¨ lines
