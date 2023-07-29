Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  "≠seq" util.Debug ≠seq ← util.ParseInt¨"," util.Tokenize ⊑data
  "≢grids" util.Debug ≢grids ← ∘‿5‿5⥊util.ParseInt¨" " util.Tokenize∾" "⊸∾˜¨2↓data
  n ← ≠grids
  "numbers in grid" util.Debug ≠⍷⥊grids
  ! (⥊grids) ≡○(∧⍷) seq
  ! 0 = ⌊´seq
  occurs ← ⍋seq
  Occur ← occurs⊑˜⊢
  {
    1=part ?
      ogrids ← Occur¨ grids
      "othr" util.Debug ⥊=⌜˜↕5
      Segments ← {∾⟨<˘𝕩,<˘⍉𝕩,<(⥊=⌜˜↕5)/⥊𝕩,<(⥊4⊸=∘+⌜˜↕5)/⥊𝕩⟩}
      "test" util.Debug Segments 5‿5⥊↕25
      Segments˘grids
      # "segments" util.Debug 5↑needs ← Segments˘grids
      # ⊑{winner‿len:
      #   hands ← len↑seq
      #   check ← {∨´{∧´𝕩∊seq}¨𝕩}¨needs
      #   ⟨1⊐check,len+1⟩
      # }•_while_(n=⊑)n‿5
    ;
    2=part ? 0
  }
}
