Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  (2=part)◶⟨+´(¯2⊸+·⌊÷⟜3)¨,+´{0≥𝕩 ? 0 ; 𝕊⊸+(¯2⊸+·⌊÷⟜3)𝕩}¨⟩util.ParseInt¨data
}
