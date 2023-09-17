Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (-⟜'A'∘⊑¨·1‿7⊸⊏" "⊸util.Tokenize)¨ ↩
  p ← Hashmap˜⟨⟩ # map from node to parents
  {
    1=part ?
      {𝕨 p.Set∧⟨𝕩⟩∾⟨⟩ p.Get 𝕨}˜´¨data
      children ← ⍷p.Values⁼@
      roots ← (¬∊⟜children)⊸/↕26
      p.Set⟜⟨⟩¨roots
      'A'+1⊑{cands‿seq :
        next ← ⊑∧(∧´·(∊⟜seq)p.Get)¨⊸/cands
        ⟨next⊸≠¨⊸/cands,seq∾next⟩
      }•_while_(⟨⟩≢⊑)(↕26)‿⟨⟩
      ;
    0
  }
}
