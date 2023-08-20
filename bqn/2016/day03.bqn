Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data ↩ ⍉∧˘>util.ParseInts¨data
  {
    1=part ? +´(2⊏data)<(1⊏data)+⊏data ;
    0
  }
}
