Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts¨ ↩
  combinations ← (∾⟜(100-+´))¨(100≥+´)¨⊸/⥊↕101+(¯1+≠data)↑0
  ⌈´{((1=part)∨500=4⊸⊑)◶⟨0,×´·0⊸⌈4⊸↑⟩+´data×𝕩}¨combinations
}
