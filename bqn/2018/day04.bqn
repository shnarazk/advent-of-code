Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      "data" util.Debug ⍉≍data (∧(⋈⟜(2⊸↑util.Tokenize)´·"[]"⊸util.Tokenize '-'⊸=◶⟨⊢,' '⟩¨)¨) ↩
      # "data" util.Debug (⊑1⊸⊑)¨2↑ data
      "record" util.Debug 3↑record ← (+`("Guard"≡(⊑1⊸⊑))¨)⊸⊔ data
      2↑{⟨3↓util.ParseInts 𝕨,⟨⊑𝕩⟩∾util.ParseInts 1⊑𝕩⟩}´¨¨record
      ;
    0
  }
}
