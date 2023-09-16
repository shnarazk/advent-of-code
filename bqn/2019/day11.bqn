Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data util.ParseInts∘⊑ ↩
  h ← Hashmap˜⟨⟩
  {
    1=part ?
      dir ← ¯1‿0
      pos ← 0‿0
      robot ← (intcode.Intcode data).Input⟨0⟩
      {𝕊 robot :
        color‿right ← (robot.Run@).Output@
        pos h.Set color
        dir ⟨¯1‿0,0‿1,1‿0,0‿¯1⟩⊸{𝕨⊑˜4|(¯1+2×right)+𝕨⊸⊐⌾⋈𝕩} ↩
        pos dir⊸+ ↩
        robot.Input⋈0 h.Get pos
        robot
      }•_while_{intcode.halt≠𝕩.Status@}robot
      ≠h.Values@;
    0
  }
}
