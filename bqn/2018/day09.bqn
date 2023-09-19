Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  players‿points ← util.ParseInts∘⊑ data
  Trace ← {n 𝕊 v :
    2⊑{c‿h‿l : ⟨c+1,h⊑v,l∾⟨h⟩⟩}•_while_(n≥⊑)0‿0‿⟨⟩
  }
  {
    1=part ?
      ⌈´⊑{scores‿followed‿i‿current :
        v19 ← 0
        score ← i+23
        {𝕊 k :
          i 1⊸+ ↩
          n1 ← current⊑followed
          n2 ← n1⊑followed
          {
            19 :
              score n1⊸+ ↩
              v19 ↩ i
              followed (i⌾(current⊸⊑)n2⌾(i⊸⊑)) ↩
              current ↩ i
              ;
            23 :
              current ↩ v19
              ;
            𝕩  :
              followed (i⌾(n1⊸⊑)n2⌾(i⊸⊑)) ↩
              current ↩ i
          }k
          # i‿current util.Debug i Trace followed
          k+1
        }•_while_(23⊸≥)1
        scores score⊸+⌾((players|i)⊸⊑) ↩
        scores‿followed‿i‿current
      }•_while_((23(⊣×⌊∘(÷˜))points)>2⊸⊑)⟨players↑0,↕30+points,0,0⟩;
   23(⊣×⌊∘(÷˜))points # "not yet"
  }
}
