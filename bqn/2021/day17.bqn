Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  xmin‿xmax‿ymin‿ymax ← util.ParseInts⊑data
  Xrange ← {⟨2×𝕨,𝕩⟩}
  Reaches ← {
    y‿x ← ⊑{pos 𝕊 vec :
      pos vec⊸+ ↩
      ⟨pos, ⋈⟜(0⊸⌈)´¯1+vec⟩
    }´•_while_(ymax≥⊑)⟨0‿0,𝕩⟩
    {
      (xmin≤x)∧(xmax≥x)∧ymin≤y ? 1‿1 ;
      (xmin≤x)∧(xmax≥x) ? 1‿0 ;
      xmin>x ? 0‿¯1 ;
      xmax<x ? 0‿ 1

     }
  }
  {
    1=part ?
      0
    ;
      0
  }
}
