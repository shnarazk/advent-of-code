#!/usr/bin/env cbqn
⟨DataFile⟩ ← •Import "../lib.bqn"
lines ← •FLines "data/2022/input-day06.txt" DataFile •args
Solution ← {
	found ← (2>⌈´)˘(≠¨(<∘/˘≡⌜˜))˘𝕨↕𝕩
	𝕨+found⊐⟨1⟩
}
•Show +´ 4⊸Solution¨ lines
•Show +´ 14⊸Solution¨ lines
