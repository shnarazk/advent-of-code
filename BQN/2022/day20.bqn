Shift ← {i 𝕊 data‿next‿prev :
  j‿step ← ⟨i,(¯1+≠data)||v ← i⊑data⟩
  j ↩ {
     1=×v ? {a←𝕩⊑next⋄{a=i?a⊑next;a}}⍟step j ;
    ¯1=×v ? prev⊑˜{a←𝕩⊑prev⋄{a=i?a⊑prev;a}}⍟step j ;
    j
  }
  {
    0=step ? data‿next‿prev
    ;
      ⟨prev_i,next_i,next_j⟩ ← ⟨i⊑prev,i⊑next,j⊑next⟩
      ⟨
        data
        next_j˙⌾(i⊸⊑) i˙⌾(j⊸⊑) next_i˙⌾(prev_i⊸⊑) next
        prev_i˙⌾(next_i⊸⊑) j˙⌾(i⊸⊑) i˙⌾(next_j⊸⊑) prev
      ⟩
  }
}

Solve ⇐ {env‿part 𝕊 rawdata :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  n ← ≠ data ← ∾lib.parseInts¨rawdata
  ⟨next,prev⟩ ← ((1⊸+)(⋈○(n⊸|n⊸+))(¯1⊸+))↕n
  data‿next‿· ↩ { 1=part ? data‿next‿prev Shift´⌽↕n ; {𝕩 Shift´⌽↕n}⍟10(811589153×data)‿next‿prev}
  +´{data⊑˜{𝕩⊑next}⍟𝕩⊑data⊐<0}¨1000‿2000‿3000
}
