Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ⊑ ↩
  diff ← 'a'-'A'
  Build ← ""⊸({""≢𝕩 ? diff=𝕨|∘-¯1⊑𝕩 ? ¯1↓𝕩 ; 𝕩∾⟨𝕨⟩}´)⌽
  Fix ← ⊑Build⊸⋈∘⊑•_while_(≢´)
  {1=part ? ≠ Fix data‿"" ; ⌊´{≠ Fix ""⋈˜(¬∊⟜("aA"+𝕩))⊸/data}¨↕26}
}
