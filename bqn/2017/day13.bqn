Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ⟨⟩⊸≢¨⊸/∘(util.ParseInts¨) ↩
  {
    1=part ? +´∞⊸≠⊸/{depth‿range : 0=(2×range-1)|depth ? range×depth ; ∞}¨data ;
    0
  }
}
