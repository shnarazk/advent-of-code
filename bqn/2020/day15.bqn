Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  h ← data HashMap ∾˜¨1+↕≠data
  goal ← (2=part)◶⟨2020,30000000⟩@
  1⊑{n‿p :
    a h.Set n∾⊑(∾˜n) h.Get a ← -´0‿0 h.Get p
    ⟨n+1,a⟩
  }•_while_(goal≥⊑)⟨1+≠data,¯1⊑data⟩
}
