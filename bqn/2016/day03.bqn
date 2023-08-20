Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {+´(2⊏𝕩)<(1⊏𝕩)+⊏𝕩}⍉∧˘(1=part)◶⟨⍉˘⌾(∘‿3‿3⊸⥊),⊢⟩>util.ParseInts¨data
}
