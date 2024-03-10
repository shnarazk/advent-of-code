Solve ⇐ {env‿part 𝕊 data :
  util‿math ← •Import¨"/util.bqn"‿"/math.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  {
    1=part ?
      ⌈´{
        (amp ← {𝕤 ⋄ intcode.Intcode data}¨↕5){𝕨.Input 𝕩}¨𝕩
        0{∾⟜𝕩⌾(𝕨.Input⁼)@ ⋄ ⊑(𝕨.Run@).Output@}´⌽amp
      }¨math.Permutations 5 ;
    ⌈´{
      (amp ← {𝕤 ⋄ intcode.Intcode data}¨↕5){𝕨.Input 𝕩}¨𝕩
      1⊑{index‿input :
        node ← index⊑amp
        ∾⟜input⌾(node.Input⁼)@
        ⟨5|1+index,¯1⊑@(node.Run@).Output@⟩
      }•_while_{𝕤 ⋄ intcode.halt≠(¯1⊑amp).status}0‿0
    }¨5+math.Permutations 5
  }
}
