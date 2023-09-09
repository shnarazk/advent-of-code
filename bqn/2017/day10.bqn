Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ring ← ↕256
  {
    1=part ?
      data util.ParseInts∘⊑ ↩
      ×´2↑2⊑⟨0,0,ring⟩{r 𝕊 pos‿skip‿ring :
        ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
        ⟨256|skip+r+pos,1+skip,ring⟩
      }´⌽data ;
    data ∾⟜17‿31‿73‿47‿23∘-⟜@∘⊑ ↩
    As16 ← {
      !256>𝕩
      h‿l ← (⌽2↑⟨⟩{l 𝕊 0 : l ; (𝕨∾16|𝕩) 𝕊 𝕩⌊∘÷16}𝕩)
      ⊑⟜"0123456789abcdef"¨h‿l
    }
    Xor ← {1‿16•bit._cast 1‿1•bit._xor´ ⟨16‿'u',1⟩•bit._cast∘⋈¨𝕩}
    ∾⥊As16¨Xor˘16‿16⥊2⊑{
      r ← 𝕩{r 𝕊 pos‿skip‿ring :
        ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
        pos ↩ (≠ring)|skip+r+pos
        ⟨pos,1+skip,ring⟩
      }´⌽data
      r
    }⍟64⟨0,0,ring⟩
  }
}
