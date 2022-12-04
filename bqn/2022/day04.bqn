#!/usr/bin/env cbqn
⟨ParseInts⟩ ← •Import "../lib.bqn"
lines ← ParseInts¨ { '-':','; 𝕩 }¨¨ •FLines •wdpath∾ "/"∾ ⊑•args

Part1 ← { ⟨a, b, x, y⟩ : ((a≤x) ∧ (y≤b)) ∨ ((x≤a) ∧ (b≤y)) }
•Show +´ Part1¨ lines

Part2 ← { ⟨a, b, x, y⟩ : (x≤b) ∧ (a≤y) }
•Show +´ Part2¨ lines
