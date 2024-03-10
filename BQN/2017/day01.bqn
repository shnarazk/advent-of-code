Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  +´(⊑×=´)˘(2=part)◶⟨2⊸↕∘(util.ParseInt∘⋈¨)⊢∾⊏,⍉·≍⟜((2÷˜≠)⊸⌽)util.ParseInt∘⋈¨⟩⊑data
}
