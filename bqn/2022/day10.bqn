#!/usr/bin/env cbqn
⟨DataFile, ParseInt⟩ ← •Import "../lib.bqn"
lines ← •FLines "data/2022/input-day10.txt" DataFile •args
Parser ← { F "noop": ⟨0⟩; ⟨0, •BQN 5↓𝕩⟩ }
instructions ← ∾Parser¨ lines
states ← ⟨0, 0⟩∾ 1 +` instructions
ss ← states ×¨ 0+↕≠states
•Show +´ ss⊸(⊑⊏˜)¨ ⟨20, 60, 100, 140, 180, 220⟩