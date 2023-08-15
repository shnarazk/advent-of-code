Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn" ∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ >util.ParseInt∘⋈¨¨data
  data ↩ {
    1=part ? data ;
    shape ← 5× baseshape ← ≢data
    (shape↑0){p 𝕊 m : m⌈(p×baseshape) geometry.Shift shape↑1+9|(+´p)+¯1+data}´⥊↕5‿5
  }
  map ← 0⌾(0‿0⊸⊑)∞⌜↕≢data
  Expand ← data{(⊑𝕩)⌊𝕨+⌊´1↓𝕩}¨geometry.Gather5∞
  (¯1+≢)⊸⊑⊑(Expand⊸⋈⊣)´•_while_(≢´)⋈⟜¬map
}
