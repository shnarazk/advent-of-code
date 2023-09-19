Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data util.ParseInt∘⊑ ↩
  Power ← {y‿x :
    rackID ← x+10
    5-˜⌊100÷˜1000|rackID×data+y×rackID
  }
  {
    1=part ?
      m ← Power¨shape ← ⋈⌜˜1+↕300
      ¯1+⌽1⊑⊑∨⥊shape⋈˜¨+´¨¯∞ geo.Neighbor9 m;
    0
  }
}
