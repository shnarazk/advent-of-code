Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  +´=○≠⟜⍷¨(2=part)◶⟨⊢,∧∧¨¨⟩" "⊸util.Tokenize¨data
}
