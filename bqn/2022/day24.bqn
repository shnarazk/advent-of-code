Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ⟨≠data,∘⟩⥊∾data
  start_position‿end_position ← 0‿¯1⊏ nowinds ← ('.'⊸≡data⊸(⊑˜))¨⊸/⥊↕≢data
  b ← {(𝕩⊸≡data⊸(⊑˜))¨↕≢data}'#'    # Block‿North‿East‿South‿West
  Reposition ← {𝕊 𝕩 : ¯1⌽⎉2 ¯1⌽⎉1 (2+≢)⊸↑𝕩}
  nesw ← {1‿1⊸↓·(¯1+≢data)⊸↑·(𝕩⊸≡data⊸(⊑˜))¨↕≢data}¨"^>v<" # North‿East‿South‿West
  Scene ← {b⌈Reposition>⌈˝⟨¯1‿0,0‿1,1‿0,0‿¯1⟩(-𝕩×⊣)⊸{y‿x𝕊m : y⌽⎉2 x⌽⎉1 m}¨nesw}
  Shift ← {(0<𝕨)◶⟨»,«⟩⍟(|𝕨)𝕩}
  Adjacent ← {𝕊 m : >⌈˝{𝕊 y‿x : y Shift⎉2 x Shift⎉1 m}¨⟨0‿0,¯1‿0,0‿1,1‿0,0‿¯1⟩}
  Return ← -·¬⊑
  start‿end ← {𝕩⊸≡¨↕≢data}¨ start_position‿end_position
  {
    1=part ?
      WidthFirstSearch ← {⟨1+𝕨,𝕩 Adjacent⊸(0⊸<⊸∧⟜¬)⟜Scene 𝕨⟩}
      Return WidthFirstSearch´•_while_(¬·end_position⊸⊑1⊸⊑)1‿start ;
    2=part ?
      WidthFirstSearch ← {𝕊 round‿states‿mode:
        next ← states Adjacent⊸(0⊸<⊸∧⟜¬)⟜Scene round
        goal ← mode⊑⟨@,end,start,end⟩
        {goal≡goal∧next ? next ↩ goal×mode 1⊸+ ↩ ; @}
        ⟨1+round,next,mode⟩
      }
      Return WidthFirstSearch•_while_(4⊸≠2⊸⊑)1‿start‿1
  }
}
