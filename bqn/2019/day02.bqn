Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  h ← (↕≠)⊸Hashmap data
  {
    1=part ?
      1 h.Set 12
      2 h.Set 2
      {𝕊 pc :
        {
          1=𝕩 ? ops ← h.Get¨h.Get¨pc+1‿2 ⋄ (h.Get 3+pc)h.Set +´ops ⋄ pc 4⊸+ ↩ ;
          2=𝕩 ? ops ← h.Get¨h.Get¨pc+1‿2 ⋄ (h.Get 3+pc)h.Set ×´ops ⋄ pc 4⊸+ ↩ ;
          (pc⋈𝕩)!0
        }h.Get pc
        pc
      }•_while_(99≠h.Get)0
      h.Get 0
     ;
    0
  }
}
