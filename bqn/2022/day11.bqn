#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
⟨data⟩ ⇐
lines ← •FLines "data/2022/input-day11.txt" lib.DataFile •args
{k ← 7-7|≠lines⋄ 0<k ? lines ↩ lines ∾ ⟨⟩˙¨↕k; @}
Convert ← { 𝕊 no‿items‿update‿test‿then‿else‿end:
  u ← 19↓update
  ⟨
    lib.ParseInts items,
    {2=+´("old"⊸(lib.StartsWith˜))¨↓u ? ¯1 ; lib.ParseInt u},
    ⊑"+"∊u,
    ⊑"*"∊u,
    lib.ParseInt test,
    lib.ParseInt then,
    lib.ParseInt else,
  ⟩
} 
•Show data ← Convert˘∘‿7 ⥊lines
