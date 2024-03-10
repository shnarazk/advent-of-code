Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  xmin‿xmax‿ymin‿ymax ← util.ParseInts⊑data
  Quad ← {a‿b‿c : (2×a)÷˜b-˜√(b⋆2)-4×a×c}
  XSpeedRange ← {(⌈Quad⟨1,1,𝕨×¯2⟩)⊸≤¨⊸/↕1+𝕩}´
  SeqDown ← {to 𝕊 init :
    F ← {
      l 𝕊 x : to>x+¯1⊑l ? l ;
      l 𝕊 x : (l∾⟨x+¯1⊑l⟩) 𝕊 x-1
    }
    ⟨0⟩ F init
  }
  YSpeedRange ← {min‿max : ⍷{⟨⟩≢((max⊸≥)∧(min⊸≤))¨⊸/min SeqDown 𝕩}¨⊸/min+↕¯2×min}
  "# Xspeed ∊" util.Debug xs ← XSpeedRange xmin‿xmax
  "# Yspeed ∊" util.Debug ys ← YSpeedRange ymin‿ymax
  {
    1=part ?
      Highest ← {
        y ← 0
        {pos‿vec :
          pos vec⊸+ ↩
          y (⊑pos)⊸⌈ ↩
          ⟨pos, ⋈⟜(0⟜⌈)´¯1+vec⟩
        }•_while_(ymin≤⊑∘⊑)0‿0⋈𝕨‿𝕩
        y
      }
      ⌈´⥊ys Highest⌜ xs
    ;
      In ← {y‿x : (xmin≤x)∧(xmax≥x)∧(ymin≤y)∧(ymax≥y)}
      Satisfy ← {
        ok ← 0
        {pos‿vec :
          pos vec⊸+ ↩
          ok (In pos)⊸∨ ↩
          ⟨pos, (⋈⟜(0⊸⌈))´¯1+vec⟩
        }•_while_(ymin≤⊑∘⊑)0‿0⋈𝕨‿𝕩
        ! ∊⟜0‿1⌾⋈ok
        ok
      }
      +´⥊ys Satisfy⌜ xs

  }
}
