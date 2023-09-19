Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data {x‿y‿vx‿vy : ⟨y‿x,vy‿vx⟩}∘util.ParseInts¨ ↩
  t ← ¯2+⊑{t‿now‿pre : ⟨t+1,×´-˜´(⌊´⋈⌈´)+⟜(t⊸×)´¨data,now⟩}•_while_(≤´1⊸↓)1‿∞‿∞
  {
    1=part ?
      min‿max ← (⌊´⋈⌈´) image ← +⟜(t⊸×)´¨data
      (' '¨↕max¬min){'#'⌾(𝕨⊸⊑)𝕩}´(<min)-˜¨image
    ;
      t
  }
}
