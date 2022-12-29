#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lines ← •Flines "data/2022/input-day15.txt" lib.DataFile ⟨⟩ # •args
data ← (lib.ParseInts{∊⟜("-,:"∾'0'+¨↕10)}⊸/)¨ lines
Mdist ← { ⟨sx,sy⟩ 𝕊 ⟨bx,by⟩: (sx-bx)+○|(sy-by) }
Band ← { target_y 𝕊 ⟨sx,sy,bx,by⟩:
  d ← ⟨sx,sy⟩ Mdist ⟨bx,by⟩
  dx ← d-|target_y-sy
  { 0 ≤ dx ? ⟨sx-dx,sx+dx⟩; ⟨⟩ }
}
F ← { ⟨s, e⟩ 𝕊 ⟨total, start, end⟩ :
 { s ≤ end ? ⟨total, start, e⌈end⟩; ⟨total + end - start + 1, s, e⟩ } }
•Show ∘‿1⥊ b ← ∨(0<≠)¨⊸/ 2000000 (Band¨) data
•Show on_mark ← ≠⍷{⟨2⊑𝕩,3⊑𝕩⟩}¨((2000000⊸=)∘(3⊸⊑))¨⊸/ data
•Show on_mark + { 0⊑𝕩 + 2⊑𝕩 - 1⊑𝕩 + 1} ⟨0, 0⊑¯1⊑b, 1⊑¯1⊑b⟩F´b
