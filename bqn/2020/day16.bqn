Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ((¬×+`)⟨⟩⊸≡¨)⊸⊔data
  ranges ← {<˘2‿2⥊util.ParseInt¨" or-" util.Split 1⊑":"util.Split 𝕩}¨(⟨⟩⊸≢)¨⊸/⊑data
  cands ← (⟨⟩⊸≢)¨⊸/util.ParseInts¨2⊑data
  "mine" util.Debug mine ← util.ParseInts 1⊑1⊑data
  MakeMask ← ⊣+↕∘(-˜)
  maskZ ← 0↑˜1+ (⌈´∾∾ranges) ⌈ ⌈´∾cands
  mask ← maskZ {r1‿r2 𝕊 m: 1¨⌾((MakeMask´r2)⊸⊏)1¨⌾((MakeMask´r1)⊸⊏)m}´ ranges
  {
    1=part ?
      +´{⟨⟩⊸≡◶⟨⊑,0⟩·∾(⊑⟜mask)◶⟨⋈⊢,⟨⟩⟩¨}¨cands
    ;
      fields ← ⍉valids ← ⟨mine⟩∾(∧´∘⊏⟜mask)¨⊸/cands
      ValueOfField ← {𝕊 𝕩:
        "departute"≡9↑⊑𝕩 ?
           name‿r1b‿r1e‿r2b‿r2e ← 𝕩
           mask ← 1¨⌾((r2b MakeMask r2e)⊸⊏)1¨⌾((r1b MakeMask´r1e)⊸⊏)maskZ
        ;
        0
      }
      ≢valids
  }
}
