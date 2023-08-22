Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug 10↑{1((¯4⊸(↓⋈↑)∘⊑∘↑)∾↓)𝕩}¨" "⊸util.Tokenize¨¨","⊸util.Tokenize¨ data
  {
    1=part ?
      0 ;
    0
  }
}
