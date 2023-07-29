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
      "check occur" util.Debug Occur¨ 12↑seq
      "oracle" util.Debug Occur¨ 14‿21‿17‿24‿4
      # Segments ← {∾⟨<˘𝕩,<˘⍉𝕩,<(⥊=⌜˜↕5)/⥊𝕩,<(⥊4⊸=∘+⌜˜↕5)/⥊𝕩⟩}
      Segments ← {∾⟨<˘𝕩,<˘⍉𝕩⟩}
      # "test" util.Debug Segments 5‿5⥊↕25
      "costs" util.Debug costs ← (⌊´·⌈´¨Segments)˘ogrids
      "player3" util.Debug 2⊏(⌈´¨Segments)˘ogrids
      "shortest" util.Debug shortest ← 1+⌊´costs
      "at" util.Debug at ← ⊑⍋costs
      "calls" util.Debug shortest↑seq
      "last_call" util.Debug last_call ← (shortest-1)⊑seq
      "bingo" util.Debug nums ← ⥊at⊏grids
      "remains" util.Debug remains ← nums/˜¬nums∊shortest↑seq
      last_call×+´remains
    ;
    2=part ? 0
  }
}
