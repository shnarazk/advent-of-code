Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"

  data util.ParseInts∘⊑ ↩
  {
    1=part ? (intcode.Run 12‿2 intcode.Configure data).Get 0 ;
    ⊑⊑{19690720=((1⊑𝕩).Get 0)}¨⊸/⋈⟜intcode.Run´¨{(𝕩+100×𝕨)⋈𝕨‿𝕩 intcode.Config data}´¨⥊↕100‿100
  }
}
