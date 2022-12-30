#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
n ← ≠data ← ∾lib.parseInts¨ •Flines "data/2022/input-day20.txt" lib.DataFile ⟨⟩ # •args
⟨next, prev⟩ ← ((1⊸+)(⋈○(n⊸|n⊸+))(¯1⊸+)) ↕n
Shift ← { 𝕊 i: 
  j ← i
  step ← (¯1+n)||v ← i⊑data 
  j ↩ {
    1=×v ? {a←𝕩⊑next⋄{a=i?a⊑next;a}}⍟step j;
    ¯1=×v? prev⊑˜{a←𝕩⊑prev⋄{a=i?a⊑prev;a}}⍟step j;
    j
  }
  {
    0=step ? @;
    prev_i ← i⊑prev
    next_i ← i⊑next
    next_j ← j⊑next
    next ↩ next_i˙⌾(prev_i⊸⊑) next
    next ↩ i˙⌾(j⊸⊑) next
    next ↩ next_j˙⌾(i⊸⊑) next
    prev ↩ i˙⌾(next_j⊸⊑) prev
    prev ↩ j˙⌾(i⊸⊑) prev
    prev ↩ prev_i˙⌾(next_i⊸⊑) prev
  }
}
z ← ⊑data ⊐ <0
Trace ← { data⊑˜{𝕩⊑next}⍟𝕩 z }
Print ← {
  •Out "print"
  {•Show 𝕩⊑data⋄ 𝕩⊑next}⍟n 𝕩
  •Out "end"
  @
}
Shift¨ ↕n
# •Show Print z
•Show +´Trace¨ 1000‿2000‿3000 
