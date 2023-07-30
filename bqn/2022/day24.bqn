Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  "≢" util.Debug ≢data ↩ ⟨≠data,∘⟩⥊∾data
  start_position‿end_position ← 0‿¯1⊏ nowinds ← ('.'⊸≡data⊸(⊑˜))¨⊸/⥊↕≢data 
  bnesw ← {(𝕩⊸≡data⊸(⊑˜))¨↕≢data}¨ "#^>v<"    # Block‿North‿East‿South‿West
  # FIXME: winds can't be on wall; their cycles are n-2
  Scene ← {>⌈˝ ⟨0‿0,¯1‿0,0‿1,1‿0,0‿¯1⟩(-𝕩×⊣)⊸{y‿x𝕊m : y⌽⎉2 x⌽⎉1 m}¨bnesw}
  Shift ← {(0<𝕨)◶⟨»,«⟩⍟(|𝕨)𝕩}
  Adjacent ← {𝕊 m : >⌈˝{𝕊 y‿x : y Shift⎉2 x Shift⎉1 m}¨⟨0‿0,¯1‿0,0‿1,1‿0,0‿¯1⟩}
  Return ← {⊑𝕩}
  "start‿end" util.Debug start‿end ← {𝕩⊸≡¨↕≢data}¨ start_position‿end_position
  # "Adjacent" util.Debug Adjacent start
  WidthFirstSearch ← {round 𝕊 states:
    "overflow"!round<10
    (•Fmt round) util.Debug states ↩ states Adjacent⊸{𝕨∧¬𝕩}⟜Scene round 
    ⟨1+round,states⟩
  }
  Return WidthFirstSearch´•_while_(¬·end_position⊸⊑1⊸⊑)1‿start
}
