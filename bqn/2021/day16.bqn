Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      "data" util.Debug 10↑⊑data
      "hex" util.Debug 20↑data "0123456789ABCDEF"⊸⊐⌾⋈¨∘⊑ ↩
      "bits" util.Debug 20↑data (∾{⌽4↑8‿1•bit._cast⋈𝕩}¨) ↩
      0 ;
    0
  }
}
