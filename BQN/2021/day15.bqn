Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn" ∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ >util.ParseInt∘⋈¨¨data
  data ↩ {
    1=part ? data ;
    newshape ← 5× baseshape ← ≢data
    (newshape↑0){𝕩⌈(𝕨×baseshape) geometry.Shift newshape↑1+9|(+´𝕨)+¯1+data}´⥊↕5‿5
  }
  map ← 0⌾(0‿0⊸⊑)∞⌜↕≢data
  Expand ← {𝕩⌊data+⌊´¨∞ geometry.Neighbor4 𝕩}
  (¯1+≢)⊸⊑⊑(Expand⊸⋈⊣)´•_while_(≢´)⋈⟜¬map
}
