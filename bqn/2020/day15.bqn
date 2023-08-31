Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data util.ParseInts∘⊑ ↩
  h ← data HashMap ∾˜¨1+↕≠data
  {
    1=part ?
      1⊑{n‿p :
        a ← -´0‿0 h.Get p
        "# memory" util.Debug x‿y ← (∾˜n) h.Get a
        a h.Set n‿x
        ⟨n+1,a⟩
      }•_while_(2020≥⊑)"init" util.Debug ⟨1+≠data,¯1⊑data⟩
      ;
    0
  }
}
