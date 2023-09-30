Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  util.Debug xmin‿xmax‿ymin‿ymax ← util.ParseInts⊑data
  Quad ← {a‿b‿c : (2×a)÷˜b-˜√(b⋆2)-4×a×c}
  XSpeedRange ← {(⌈Quad⟨1,1,𝕨×¯2⟩)⊸≤¨⊸/↕𝕩}´
  YSpeedRange ← {min‿max : ⍷{⟨⟩≢((max≥-)∧(min≤-))¨⊸/+`𝕩+↕-min}¨⊸/↕-min}
  Highest ← {
     y ← 0
     {pos‿vec :
       pos vec⊸+ ↩
       y (⊑pos)⊸⌈ ↩
       ⟨pos, ⋈⟜(0⟜⌈)´¯1+vec⟩
    }•_while_(ymin≤⊑∘⊑)0‿0⋈𝕨‿𝕩
    y
  }
  {
    1=part ?
      "# Xspeed ∊" util.Debug xs ← XSpeedRange xmin‿xmax
      "# Yspeed ∊" util.Debug ys← YSpeedRange ymin‿ymax
      ⌈´⥊ys Highest⌜ xs
    ;
      0
  }
}
