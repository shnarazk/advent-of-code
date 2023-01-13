#!/usr/bin/env cbqn
⟨DataFile⟩ ← •Import "../lib.bqn"
Common ← { 𝕨(/⟜𝕨)∘(⌈´˘)∘(=⌜)𝕩 }
Point ← <⟜'a'◶⟨'a'-˜1⊸+,'A'-˜27⊸+⟩

Part1 ← Point∘⊑∘Common´∘((2÷˜≠)⊸(↑⋈↓))
•Show +´ Part1¨ •FLines "data/2022/input-day03.txt" DataFile •args

Part2 ← Point∘⊑∘(Common´)
•Show +´ Part2˘ ∘‿3 ⥊ •FLines "data/2022/input-day03.txt" DataFile •args
