Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data ↩ ((1-2×'L'⊸=)∘⊑⋈util.ParseInt)¨ ", " util.Tokenize⊑data
  {
    1=part ? +○|´1⊑0‿⟨0,0⟩{d‿l 𝕊 dir‿pos : ⟨dir 4⊸|∘(d⊸+) ↩ ,pos+l×dir⊑⟨¯1‿0,0‿1,1‿0,0‿¯1⟩⟩}´⌽data ;
    0
  }
}
