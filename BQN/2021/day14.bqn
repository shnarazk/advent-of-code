Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨head⟩‿rule ← (¯2⊸×++`)∘(⟨⟩⊸≡¨)⊸⊔data
  begin ← ⊑ head -⟜'A'¨ ↩
  "# rule" util.Debug 'A'+⍉≍ rule ↩ 'A'-˜∾¨"-> "⊸util.Split¨rule
  !(≠head)≡1++´⥊ map ← (m0 ← 26‿26↑0){1⊸+⌾(𝕨⊸⊑)𝕩}´⥊<˘2↕head
  ocr ← 1⊸+⌾(begin⊸⊑)+´˘⍉1⊑{round‿m :
    ⟨-¬round,m+m0{b‿e‿s F d : t ← b‿e⊑m ⋄ t⊸+⌾(s‿e⊸⊑)t⊸+⌾(b‿s⊸⊑)-⟜t⌾(b‿e⊸⊑)d}´rule⟩
  }•_while_(0⊸<⊑)(2=part)◶⟨10⊸⋈,40⊸⋈⟩map
  (⌈´-⌊´)0⊸≠⊸/ocr
}
