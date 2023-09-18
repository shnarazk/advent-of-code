Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug players‿points ← util.ParseInts∘⊑ data
  {
    1=part ?
      ⌈´{scores‿followed‿i‿current :
        {𝕊 k :
          {
            19 :
              followed ∾⟜⟨i⟩ ↩
              ;
            23 :
              @
              ;
            𝕩  :
              p ← current⊑followed
              n ← p⊑followed
              followed i⊸↑ ↩
              followed (i⌾(p⊸⊑)n⌾(i⊸⊑)) ↩
          }i
           i+1}•_while_(23⊸≥)1
        𝕩
      }•_while_(6>⌈´∘⊑)⟨players↑0,⟨0⟩,0,0⟩;
    0
  }
}
