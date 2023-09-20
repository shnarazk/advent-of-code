Solve ⇐ {env‿part 𝕊 data :
  ⟨ParseInt,Split⟩ ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  seq ← ParseInt¨"," Split ⊑data
  grids ← ∘‿5‿5⥊ParseInt¨" " Split ∾" "⊸∾˜¨2↓data
  !(⥊grids)≡○(∧⍷)seq
  !0=⌊´seq
  occurs ← ⍋seq
  Occur ← occurs⊑˜⊢
  Segments ← {∾⟨<˘𝕩,<˘⍉𝕩⟩}
  costs ← (⌊´·⌈´¨Segments)˘Occur¨grids
  round‿at ← {1=part ? ⟨1+⌊´costs,⊑⍋costs⟩ ; 2=part ? ⟨1+⌈´costs,¯1⊑⍋costs⟩}
  last_call ← (round-1)⊑seq
  nums ← ⥊at⊏grids
  remains ← nums/˜¬nums∊round↑seq
  last_call×+´remains
}
