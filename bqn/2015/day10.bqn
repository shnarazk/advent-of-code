Solve ⇐ {env‿part 𝕊 data :
  util ← •Import¨"/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⋈¨∘⊑ ↩
  rounds ← (2=part)◶⟨40,50⟩@
  Segmentize ← {(≠⋈⊑)¨𝕩⊔˜+`≠´¨<˘2↕(⋈⊑)⊸∾𝕩}
  ≠1⊑((1⊸+)⊸⋈⟜(∾´Segmentize))´•_while_(rounds>⊑)0‿data
}
