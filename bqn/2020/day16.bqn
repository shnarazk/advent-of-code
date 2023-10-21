Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ((¬×+`)⟨⟩⊸≡¨)⊸⊔data
  ranges ← {<˘2‿2⥊util.ParseInt¨" or-" util.Split 1⊑":"util.Split 𝕩}¨(⟨⟩⊸≢)¨⊸/⊑data
  cands ← (⟨⟩⊸≢)¨⊸/util.ParseInts¨2⊑data
  MakeMask ← ⊣+↕∘(-˜)
  {
    1=part ?
      mask ← 0↑˜1+ (⌈´∾∾ranges) ⌈ ⌈´∾cands
      mask ↩ mask {r1‿r2 𝕊 m: 1¨⌾((MakeMask´r2)⊸⊏)1¨⌾((MakeMask´r1)⊸⊏)m}´ ranges
      +´{⟨⟩⊸≡◶⟨⊑,0⟩·∾(⊑⟜mask)◶⟨⋈⊢,⟨⟩⟩¨}¨cands
    ;
      0
  }
}
