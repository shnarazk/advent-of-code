Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts¨ ↩
  shape ← 1+⌈´{id‿x‿y‿w‿h : ⟨h+y,w+x⟩}¨data
  overlap ← +´{id‿x‿y‿w‿h : (-y‿x) geometry.Rotate shape↑1¨h‿w↑0}¨data
  {
    1=part ? +´1<⥊overlap ;
    overlap 1⊸= ↩
    ⊑⊑{id‿x‿y‿w‿h : ∧´⥊h‿w↑y‿x geometry.Rotate overlap}¨⊸/data
  }
}
