#!/usr/bin/env cbqn
⟨DataFile, ParseInts⟩ ← •Import "../lib.bqn" # This file was created by a Rust program :-)
lines ← (⊑ParseInts)¨ •FLines "bqn/2022/input-day07.txt" DataFile •args
•Show +´(100000⊸≥)¨⊸/ lines
used ← ⌈´ lines
need ← used - 40000000 
•Show ∧(need⊸≤)¨⊸/ lines
