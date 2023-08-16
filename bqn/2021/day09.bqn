Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"," env.Var⌾⋈ "BQN_LIB"
  lows ← {∧´<´1⊸(⊑∘↑⋈↓)𝕩}¨∞ geometry.Gather5 map ← util.ParseInt∘⋈¨>data
  {
    1=part ? +´lows×○⥊1+map ;
    ×´3↑∨≠¨⊔(∞⊸≠)⊸/⥊{map{𝕩÷9>𝕨}¨⌊´¨∞ geometry.Gather5 𝕩}⍟(+´≢)((1÷⊢)⌈(⊢×+`))⌾⥊lows
  }
}
