Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨intcode⟩ ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  {
    1=part ?
      ⊑0⊸≠⊸/(((IntCode data).Input⟨1⟩).Run@).Output@ ;
    0
  }
}
