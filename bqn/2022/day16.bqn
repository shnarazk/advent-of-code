#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap⟩ ← •Import "../lib.bqn"
•Show data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile ⟨⟩ # •args
•Show nodes ← ∧⍷⊑¨data
ProductIndices ← {d←𝕩⋄({(((⊑𝕩)⊸⋈)⋈(⋈⟜(1⊑𝕩)))¨↕d}⋈)⌜˜↕𝕩}
Product ← {(+´((𝕩⊑˜1⊸⊑)×(𝕨⊑˜0⊸⊑))¨)⌜ ProductIndices ≠𝕨}
•Show pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
# ⟨next, prev⟩ ← ((1⊸+)(⋈○(n⊸|n⊸+))(¯1⊸+)) ↕n
# Shift ← { 𝕊 i: 
#   j ← i
#   step ← (¯1+n)||v ← i⊑data 
#   j ↩ {
#     1=×v ? {a←𝕩⊑next⋄{a=i?a⊑next;a}}⍟step j;
#     ¯1=×v? prev⊑˜{a←𝕩⊑prev⋄{a=i?a⊑prev;a}}⍟step j;
#     j
#   }
#   {
#     0=step ? @;
#     ⟨prev_i,next_i,next_j⟩ ← ⟨i⊑prev,i⊑next,j⊑next⟩
#     next ↩ next_j˙⌾(i⊸⊑) i˙⌾(j⊸⊑) next_i˙⌾(prev_i⊸⊑) next
#     prev ↩ prev_i˙⌾(next_i⊸⊑) j˙⌾(i⊸⊑) i˙⌾(next_j⊸⊑) prev
#   }
# }
# Trace ← { data⊑˜{𝕩⊑next}⍟𝕩 ⊑data ⊐ <0 }
# Shift¨ ↕n
# •Show +´Trace¨ 1000‿2000‿3000 

# data ↩ 811589153×¨ data
# ⟨next, prev⟩ ↩ ((1⊸+)(⋈○(n⊸|n⊸+))(¯1⊸+)) ↕n
# n {Shift¨ ↕𝕨}⍟10 0
# •Show +´Trace¨ 1000‿2000‿3000 
