Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ((¬×+`)⟨⟩⊸≡¨)⊸⊔data
  ranges ← {<˘2‿2⥊util.ParseInt¨" or-" util.Split 1⊑":"util.Split 𝕩}¨(⟨⟩⊸≢)¨⊸/⊑data
  util.Debug cands ← util.ParseInts¨2⊑data
  {
    1=part ?
      util.Debug mask ← 0↑˜1+ (⌈´∾∾ranges) ⌈ ⌈´∾cands
      0
    ;
      0
  }
}
