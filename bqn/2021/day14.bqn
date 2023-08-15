Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨head⟩‿rule ← (¯2⊸×++`)∘(⟨⟩⊸≡¨)⊸⊔ data
  head -⟜'A'¨ ↩
  rule ↩ 'A'-˜¨"-> "⊸util.Tokenize¨rule
  "head" util.Debug head
  util.Debug begin ← ⊑head
  "# rule" util.Debug 'A'+⍉≍rule
  map ← (26‿26↑0){be 𝕊 m : 1⊸+⌾(be⊸⊑)m}´⥊<˘2↕head
  !(≠head)≡1++´⥊map
  rounds ← (2=part)◶⟨10,40⟩@
  ocr ← 1⊸+⌾(begin⊸⊑)+´˘⍉1⊑{𝕊 round‿m :
    dd ← 0
    diff ← (26‿26↑0){
      ⟨b,e⟩‿⟨s⟩ F d :
        t ← b‿e⊑m
        (t⊸+)⌾(s‿e⊸⊑)(t⊸+)⌾(b‿s⊸⊑)(-⟜t)⌾(b‿e⊸⊑)d
    }´rule
    (•Fmt round) util.Debug +´˘m+diff
    ⟨1+round,m+diff⟩
  }•_while_(rounds⊸≥⊑)1‿map
  (⌈´-⌊´)0⊸≠⊸/ocr
}
