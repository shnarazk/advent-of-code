Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data {x‿y‿vx‿vy : ⟨y‿x,vy‿vx⟩}∘util.ParseInts¨ ↩
  {
    1=part ?
      t ← ¯2+⊑{t‿now‿pre : ⟨t+1,×´-˜´(⌊´⋈⌈´)+⟜(t⊸×)´¨data,now⟩}•_while_(≤´1⊸↓)1‿∞‿∞
      min‿max ← (⌊´⋈⌈´)image ← +⟜(t⊸×)´¨data
      (' '¨↕max¬min){'#'⌾(𝕨⊸⊑)𝕩}´(<min)-˜¨image
      ;
    0
  }
}
