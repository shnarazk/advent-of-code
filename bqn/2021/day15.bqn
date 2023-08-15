Solve ⇐ {env‿part 𝕊 data :
  util‿geometory ← •Import¨"/util.bqn"‿"/geometric.bqn" ∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ >util.ParseInt∘⋈¨¨data
  map ← 0⌾(0‿0⊸⊑)∞⌜↕≢data
  Expand ← data{(⊑𝕩)⌊𝕨+⌊´1↓𝕩}¨geometory.Gather5
  (¯1+≢)⊸⊑⊑(Expand⊸⋈⊣)´•_while_(≢´)⋈⟜¬map
}
