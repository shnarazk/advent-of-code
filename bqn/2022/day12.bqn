#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
# ⟨lines,status,monkeys⟩ ⇐
lines ← •FLines "data/2022/input-day12.txt" lib.DataFile ⟨⟩ # •args
•Show lines ((≠⋈(≠⊑))⥊∾) ↩
IndexOf ← {⊑(𝕨⊸=⊑⟜𝕩)¨⊸/⥊↕·≢ 𝕩}
•Show 'S' IndexOf lines
•Show 'E' IndexOf lines

# {k ← 7-7|≠lines⋄ 0<k ? lines ↩ lines∾⟨⟩˙¨↕k; @}
# lines ↩ ∘‿7 ⥊lines
# Convert ← { 𝕊 no‿items‿update‿test‿then‿else‿end:
#   u ← 19↓update
#   <⟨
#     lib.ParseInt no,
#     0 (+⟜(2⊸×))´ ("+*" ∊ u), # op-code encoded to 1 or 2
#     {2=+´("old"⊸(lib.StartsWith˜))¨↓u ? ¯1 ; lib.ParseInt u}, # oprand
#     lib.ParseInt test,
#     lib.ParseInt then,
#     lib.ParseInt else,
#   ⟩
# }
# status ← (<·lib.ParseInts 1⊸⊑)˘lines
# inspects ← 0˙¨↕≠ monkeys ← ⥊Convert˘ lines
# limit ← •math.lcm´(3⊸⊑)¨monkeys
# Updater ← { no‿op‿arg‿test‿then‿else 𝕊 status‿ins‿part:
#   ⟨s,n⟩ ← ⟨status,≠no⊑status⟩
#   { 𝕊 item:
#     item ↩ part˙◶⟨⌊3⊸(÷˜),limit⊸|⟩op{1 𝕊 ¯1: item×2 ; 1 𝕊 𝕩: item+𝕩 ; 2 𝕊 ¯1: item⋆2; 2 𝕊 𝕩: item×𝕩} arg
#     s ↩ (∾⟜⟨item⟩)⌾(((0=test|item)⊑⟨else,then⟩)⊸⊑) s
#   }¨no⊑status
#   ⟨⟨⟩˙⌾(no⊸⊑) s,(n⊸+)⌾(no⊸⊑) ins, part⟩
# }
# •Show ×´2↑∨ 1⊑{𝕩 Updater´⌽monkeys}⍟20⟨status,inspects,0⟩
# •Show ×´2↑∨ 1⊑{𝕩 Updater´⌽monkeys}⍟10000⟨status,inspects,1⟩
