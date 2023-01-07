#!/usr/bin/env cbqn
⟨color,ParseInts, DataFile⟩ ← •Import "../lib.bqn"
data ← •Flines "data/2022/input-day05.txt" DataFile •args
⟨header,lines⟩ ← ⟨⟨⟩⟩⊸(⊑⊐˜)⊸(↑⋈↓)data
•Out color.green color.Fmt init ← ⟨⟨⟩⟩∾(¯1⊸↓)¨(⟨⟩⊸≢)¨⊸/((' '⊸≠)¨⊸/)¨<˘ ⍉⟨≠header,∘⟩⥊∾{𝕩(⊑∊)" []" ? ' ';𝕩}¨¨header
•Out color.green color.Fmt 5↑actions ← ParseInts¨1↓lines
Part1 ← {
	⟨0,from,to⟩ F state: state;
	⟨amount,from,to⟩ F state: {
		stack1 ← from⊑state
		⟨val,dropped⟩ ← (⊑⋈(1⊸↓))stack1
		stack2 ← to⊑state
		pushed ← (<val)∾stack2
		state ← pushed˙⌾(to⊸⊑) dropped˙⌾(from⊸⊑) state
		⟨1-˜amount,from,to⟩ F state
	}
}
•Show(⊑¨1⊸↓)init Part1´ ⌽actions
Part2 ← { ⟨amount,from,to⟩ F state:
	⟨val,dropped⟩ ← amount(↑⋈↓)from⊑state
	(val⊸∾)⌾(to⊸⊑)dropped˙⌾(from⊸⊑)state
}
•Show(⊑¨1⊸↓)init Part2´⌽actions
