Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data ↩ 'L'=>data
  {
    1=part ?
      0 ;
    0
  }
}
