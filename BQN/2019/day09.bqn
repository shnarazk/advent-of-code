 Solve ⇐ {env‿part 𝕊 data :
  util‿math ← •Import¨"/util.bqn"‿"/math.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  ⊑(((intcode.Intcode data).Input⟨part⟩).Run@).Output@
}
