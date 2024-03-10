Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ {0∾𝕩∾3+¯1⊑𝕩}∧util.ParseInt¨data
  {1=part ? ×´1‿3⊏≠¨⊔-˜´˘2↕data ; ¯1⊑((1+¯1⊑data)↑1){(+´(0⊸≤⊸/𝕨-1+↕3)⊏𝕩)⊸+⌾(𝕨⊸⊏)𝕩}´⌽data}
}
