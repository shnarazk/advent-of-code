#!/usr/bin/env cbqn
⟨color,ParseInts, DataFile⟩ ← •Import "../lib.bqn"
⟨header,lines⟩ ← ⟨⟨⟩⟩⊸(⊑⊐˜)⊸(↑⋈↓)•Flines "data/2022/input-day05.txt" DataFile •args
•Out color.green color.Fmt init ← ⟨⟨⟩⟩∾(¯1⊸↓)¨(⟨⟩⊸≢)¨⊸/((' '⊸≠)¨⊸/)¨<˘ ⍉⟨≠header,∘⟩⥊∾{𝕩(⊑∊)" []" ? ' ';𝕩}¨¨header
•Out color.green color.Fmt 5↑actions ← ParseInts¨1↓lines
Part1 ← { ⟨amount,from,to⟩ F state:
  {⟨val,dropped⟩ ← (⊑⋈(1⊸↓))from⊑𝕩⋄ pushed ← (<val)∾to⊑𝕩⋄ pushed˙⌾(to⊸⊑)dropped˙⌾(from⊸⊑)𝕩}⍟amount state
}
•Show(⊑¨1⊸↓)init Part1´ ⌽actions
Part2 ← { ⟨amount,from,to⟩ F state: ⟨val,dropped⟩ ← amount(↑⋈↓)from⊑state⋄ (val⊸∾)⌾(to⊸⊑)dropped˙⌾(from⊸⊑)state }
•Show(⊑¨1⊸↓)init Part2´⌽actions
