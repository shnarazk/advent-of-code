Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data util.ParseInt¨ ↩
  {
    1=part ?
      Check ← {𝕨+=´(2⋆16)⊸|𝕩}
      ⊑{c‿p : c⊸Check⊸⋈ 2147483647|16807‿48271×p}⍟40000000 0⋈data ;
    0
  }
}
