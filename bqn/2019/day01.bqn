Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "# data" util.Debug data util.ParseInt¨ ↩
  {
    1=part ? +´(¯2⊸+·⌊÷⟜3)¨data ;
    0
  }
}
