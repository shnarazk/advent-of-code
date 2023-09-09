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
    "# salt" util.Debug data ∾⟜17‿31‿73‿47‿23∘-⟜@∘⊑ ↩
    # data ← 17‿31‿73‿47‿23
    As16 ← {
      !256>𝕩
      h‿l ← (⌽2↑⟨⟩{l 𝕊 0 : l ; (𝕨∾16|𝕩) 𝕊 𝕩⌊∘÷16}𝕩)
      ⊑⟜"0123456789abcdef"¨h‿l
    }
    "# As16" util.Debug As16 7
    Xor ← {1‿8•bit._cast 1‿1•bit._xor´ ⟨8‿'u',1⟩•bit._cast∘⋈¨𝕩}
    "# Xor" util.Debug Xor 65‿27‿9‿1‿4‿3‿40‿50‿91‿7‿6‿0‿2‿5‿68‿22
    ∾⥊As16¨Xor˘ " " util.Debug 16‿16⥊2⊑{
      r ← 𝕩{r 𝕊 pos‿skip‿ring :
        ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
        pos ↩ (≠ring)|skip+r+pos
        ⟨pos,1+skip,ring⟩
      }´⌽data
      r
    }⍟64⟨0,0,ring⟩
  }
}
