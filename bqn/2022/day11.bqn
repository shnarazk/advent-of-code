#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
⟨lines,init_status,monkeys⟩ ⇐
lines ← •FLines "data/2022/input-day11.txt" lib.DataFile •args
{k ← 7-7|≠lines⋄ 0<k ? lines ↩ lines∾⟨⟩˙¨↕k; @}
lines ↩ ∘‿7 ⥊lines
Convert ← { 𝕊 no‿items‿update‿test‿then‿else‿end:
  u ← 19↓update
  <⟨
    lib.ParseInt no,
    0 (+⟜(2⊸×))´ ("+*" ∊ u), # op-code
    {2=+´("old"⊸(lib.StartsWith˜))¨↓u ? ¯1 ; lib.ParseInt u}, # oprand
    lib.ParseInt test,
    lib.ParseInt then,
    lib.ParseInt else,
  ⟩
}
lib.color.blue lib.term.Println init_status ← ⥊(lib.ParseInts⊑)˘lines
lib.color.blue lib.term.Println monkeys ← ⥊Convert˘ lines
Updater ← { no‿op‿arg‿test‿then‿else 𝕊 status:
  s ← status
  (180‿180‿240 lib.color.RGB 10‿10‿30) lib.term.Outln "somothing"
  { 𝕊 item:
    item ↩ ⌊3÷˜op {1 𝕊 ¯1 : item×2; 1 𝕊  𝕩 : item+𝕩; 2 𝕊 ¯1 : item⋆2; 2 𝕊  𝕩 : item×𝕩} arg
    s ↩ ⟨∾⊸⟨item⟩⟩˙⌾({0=test|item ? then :else}⊸⊑) s
  }¨no⊑status
  s ↩ ⟨⟩˙⌾(no⊸⊑) s
}
lib.color.green lib.term.Println status ← init_status Updater´ ⌽monkeys

