Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  data ↩ 10
  Wall ← {y 𝕊 x : 2|+´32‿1•bit._cast⋈data+(x⋆2)+(3×x)+(2×x×y)+y+(y⋆2)}
  util.Debug map ← ¬Wall⌜˜↕40
  start ← 1‿1
  goal ← ⌽31‿39

  {
    1=part ?
      goal⊸⊑{𝕩}{∞=goal⊸⊑}0⌾(1‿1⊸⊑) ∞⌜map
      ;
    0
  }
}
