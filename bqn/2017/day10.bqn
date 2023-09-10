Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨knothash⟩← •Import "/2017/knot-hash.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  Trans ← {𝕨 𝕊 𝕩 :
    𝕩{r 𝕊 pos‿skip‿ring :
      ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
      ⟨256|skip+r+pos,1+skip,ring⟩
    }´⌽𝕨
  }
  {
    1=part ? data util.ParseInts∘⊑ ↩ ⋄ ×´2↑2⊑data Trans⟨0,0,↕256⟩ ;
    KnotHash data
  }
}
