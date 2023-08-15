Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨head⟩‿rule ← (¯2⊸×++`)∘(⟨⟩⊸≡¨)⊸⊔ data
  begin ← ⊑ head -⟜'A'¨ ↩
  "# rule" util.Debug 'A'+⍉≍ rule ↩ 'A'-˜¨"-> "⊸util.Tokenize¨rule
  !(≠head)≡1++´⥊ map ← (26‿26↑0){be 𝕊 m : 1⊸+⌾(be⊸⊑)m}´⥊<˘2↕head
  rounds ← (2=part)◶⟨10,40⟩@
  ocr ← 1⊸+⌾(begin⊸⊑)+´˘⍉1⊑{𝕊 round‿m :
    diff ← (26‿26↑0){
      ⟨b,e⟩‿⟨s⟩ F d : t ← b‿e⊑m ⋄ (t⊸+)⌾(s‿e⊸⊑)(t⊸+)⌾(b‿s⊸⊑)(-⟜t)⌾(b‿e⊸⊑)d
    }´rule
    ⟨1+round,m+diff⟩
  }•_while_(rounds⊸≥⊑)1‿map
  (⌈´-⌊´)0⊸≠⊸/ocr
}
