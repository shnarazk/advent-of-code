Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⋈¨∘⊑ ↩
  rounds ← (2=part)◶⟨40,50⟩@
  Segmentize ← {i ← 0∾(↕≠𝕩)/˜≠´¨<˘2↕(⋈⊑)⊸∾𝕩 ⋄ (i⊏𝕩)∾¨˜(-˜´¨<˘2↕i∾≠𝕩)}
  ≠1⊑(1⊸+)⊸⋈⟜(∾´Segmentize)´•_while_{util.Progress(⊑𝕩)⋈≠1⊑𝕩 ⋄ rounds>⊑𝕩}0‿data
}
