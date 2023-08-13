Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "token" util.Debug nodes ← ∧⍷∾⥊adj ← ⍉≍"-"⊸util.Tokenize¨data
  start‿end ← nodes⊐"start"‿"end"
  "# " util.Debug map ← nodes⊸⊐¨adj
  util.Debug type ← 'Z'⊸≥∘⊑¨nodes
  count ← 0
}
