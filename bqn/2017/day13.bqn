Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ⟨⟩⊸≢¨⊸/∘(util.ParseInts¨) ↩
  {
    1=part ? +´∞⊸≠⊸/{0=(2×𝕩-1)|𝕨 ? 𝕨×𝕩; ∞}´¨data ;
    -{𝕊 n : ∨´{0=(2×𝕩-1)|n+𝕨}´¨data ? 1+n ; -𝕩}•_while_(0⊸≤)0
  }
}
