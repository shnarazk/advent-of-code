#!/usr/bin/env cbqn
⟨DataFile⟩ ← •Import "../lib.bqn"
Common ← { 𝕨(/⟜𝕨)∘(⌈´˘)∘(=⌜)𝕩 }
Point ← { 𝕩 < 'a' ? 27+𝕩-'A'; 1+𝕩-'a' }

Part1 ← { Point ⊑ Common´ (2÷˜≠)⊸(↑⋈↓) 𝕩 }
•Show +´ Part1¨ •FLines "data/2022/input-day03.txt" DataFile •args

Part2 ← { Point ⊑ Common´ 𝕩 }
•Show +´ Part2˘ ∘‿3 ⥊ •FLines "data/2022/input-day03.txt" DataFile •args
