Solve ⇐ {env‿part 𝕊 data :
  util‿json ← •Import¨"/util.bqn"‿"/json.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Traverse ← {
    0=•Type 𝕩 ? 1==𝕩 ? +´𝕊¨𝕩 ;
    0=•Type 𝕩 ? (2=⊑≢𝕩)∧(2=≠≢𝕩) ? +´𝕊¨1⊏𝕩 ;
    1=•Type 𝕩 ? 𝕩 ;
    0
  }
  Traverse2 ← {
    0=•Type 𝕩 ? 1==𝕩 ? +´𝕊¨𝕩 ;
    0=•Type 𝕩 ? (2=⊑≢𝕩)∧(2=≠≢𝕩) ? ∧´"red"⊸≢¨1⊏𝕩 ? +´𝕊¨1⊏𝕩 ;
    1=•Type 𝕩 ? 𝕩 ;
    0
  }
  (2=part)◶⟨Traverse,Traverse2⟩json.Parse⊑data
}
