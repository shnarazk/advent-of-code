Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨ "/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ((¬×+`)⟨⟩⊸≡¨)⊸⊔data
  ranges ← {<˘2‿2⥊util.ParseInt¨" or-" util.Split 1⊑":"util.Split 𝕩}¨(⟨⟩⊸≢)¨⊸/⊑data
  cands ← (⟨⟩⊸≢)¨⊸/util.ParseInts¨2⊑data
  mine ← util.ParseInts 1⊑1⊑data
  MakeMask ← ⊣+↕∘(¬˜)
  maskZ ← 0↑˜1+ (⌈´∾∾ranges) ⌈ ⌈´∾cands
  mask ← maskZ {r1‿r2 𝕊 m: 1¨⌾((MakeMask´r2)⊸⊏)1¨⌾((MakeMask´r1)⊸⊏)m}´ ranges
  {
    1=part ?
      +´{⟨⟩⊸≡◶⟨⊑,0⟩·∾(⊑⟜mask)◶⟨⋈⊢,⟨⟩⟩¨}¨cands
    ;
      specs ← {(⊣⋈(util.ParseInt¨" or-"⊸util.Split))´":"util.Split 𝕩}¨(⟨⟩⊸≢)¨⊸/⊑data
      fields ← ⍉>valids ← ⟨mine⟩∾(∧´∘⊏⟜mask)¨⊸/cands
      Determine ← {
        ⟨⟩    𝕊  ⟨⟩   : @ ;
        specs 𝕊 fields:
          Cands ← {𝕊 name‿range:
             r1b‿r1e‿r2b‿r2e ← range
             mask ← 1¨⌾((r2b MakeMask r2e)⊸⊏)1¨⌾((r1b MakeMask r1e)⊸⊏)maskZ
             {∧´𝕩⊏mask}˘fields
          }
          m ← >Cands¨specs
          map ← Hashmap˜⟨⟩
          D ← { 𝕊 m:
            uni ← (1=+´∘⊏⟜m)¨⊸/↕≠m
            ⟨⟩≢uni ?
              {j ← <⁼(𝕩⊏m)⊐1 ⋄ 𝕩 map.Set j ⋄ m ↩ (0¨⌾(j⊸⊏))⌾⍉m}¨uni
              D m
            ; @
          }
          D m
          map
      }
      map ← specs Determine fields
      targets ← map.Get¨("departure"≡(9⊸↑∘⊑⊑⟜specs))¨⊸/↕≠specs
      ×´targets⊏mine
  }
}
