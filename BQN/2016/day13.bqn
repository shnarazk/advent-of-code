Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  Wall ← {y 𝕊 x : 2|+´32‿1•bit._cast⋈data+(x⋆2)+(3×x)+(2×x×y)+y+(y⋆2)}
  map ← ¬Wall⌜˜↕52
  start ← 1‿1
  {
    1=part ? goal ← ⌽31‿39 ⋄ goal⊸⊑{map{𝕨 ? 𝕩⊑⊸⌊1+⌊´1↓𝕩 ; ∞}¨∞ geometry.Neighbor5 𝕩}•_while_{∞=goal⊸⊑}0⌾(start⊸⊑)(∞⌜map) ;
    +´⥊∞>1⊑{(1+⊑𝕩)⋈map{𝕨 ? 𝕩⊑⊸⌊1+⌊´1↓𝕩 ; ∞}¨∞ geometry.Neighbor5 1⊑𝕩}•_while_{50>⊑}0⋈0‿0⌾(start⊸⊑)(∞⌜map)
  }
}
