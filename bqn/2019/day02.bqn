Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  ⟨intcode⟩ ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  {
    1=part ? (((Intcode data).Config 12‿2).Run@).Get 0 ;
    ⊑⊑{19690720=((1⊑𝕩).Get 0)}¨⊸/⋈⟜{𝕩.Run@}´¨{(𝕩+100×𝕨)⋈(IntCode data).Config 𝕨‿𝕩}´¨⥊↕100‿100
  }
}
