Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data util.ParseInts∘⊑ ↩
  ring ← ↕256
  {
    1=part ?
      ×´2↑2⊑⟨0,0,ring⟩{r 𝕊 pos‿skip‿ring :
        ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
        ⟨256|skip+r+pos,1+skip,ring⟩
      }´⌽data ;
    0
  }
}
