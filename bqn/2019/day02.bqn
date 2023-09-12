Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  h ← (↕≠)⊸Hashmap data
  Machine ← {𝕊 m :
    {𝕊 ip :
      {
        1=𝕩 ? ops ← m.Get¨m.Get¨ip+1‿2 ⋄ (m.Get 3+ip)m.Set +´ops ⋄ ip 4⊸+ ↩ ;
        2=𝕩 ? ops ← m.Get¨m.Get¨ip+1‿2 ⋄ (m.Get 3+ip)m.Set ×´ops ⋄ ip 4⊸+ ↩ ;
        (ip⋈𝕩)!0
      }m.Get ip
      ip
    }•_while_(99≠m.Get)0
    m
  }
  {
    1=part ? 1 h.Set 12 ⋄ 2 h.Set 2 ⋄ (Machine h).Get 0 ;
    ⊑⊑{19690720=((1⊑𝕩).Get 0)}¨⊸/⋈⟜Machine´¨{
      h ← (↕≠)⊸Hashmap data
      1 h.Set 𝕨
      2 h.Set 𝕩
      (𝕩+100×𝕨)⋈h
    }´¨⥊↕100‿100
  }
}
