Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug 3↑¨((¬×+`)⟨⟩⊸≡¨)⊸⊔50↑data
  {
    1=part ?
      0
    ;
      0
  }
}
