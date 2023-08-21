Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {1=part ? ×´⊑(2020=+´)¨⊸/⥊∾⌜˜𝕩 ; ×´⊑(2020=+´)¨⊸/⥊𝕩∾⌜∾⌜˜𝕩}util.ParseInt¨data
}
