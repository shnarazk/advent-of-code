#!/usr/bin/env cbqn

Common ← { 𝕨(/⟜𝕨)∘(⌈´˘)∘(=⌜)𝕩 }
Point ← { 𝕩 < 'a' ? 27+𝕩-'A'; 1+𝕩-'a' }

Part1 ← { Point ⊑ (2÷˜≠)⊸{(𝕨↑𝕩) Common (𝕨↓𝕩)} 𝕩 }
•Show +´ Part1¨ •FLines ⊑•args

Part2 ← { ⟨a, b, c⟩ : Point ⊑ a Common b Common c }
•Show +´ Part2˘ ∘‿3 ⥊ •FLines ⊑•args
