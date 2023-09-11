Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ? ×´+´((2⊸=⋈○(0<+´)3⊸=)/⁼)¨-⟜'a'¨data ;
    l ← ≠⊑data
    ⊑(l=1+≠)¨⊸/⥊{(𝕨=𝕩)/𝕨}⌜˜data
  }
}
