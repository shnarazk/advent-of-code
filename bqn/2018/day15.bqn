Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ".#EG"⊸⊐∘> ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elves ← 2⋈˜¨(2=⊑⟜data)¨⊸/⥊↕≢data
  goblins ← 3⋈˜¨(3=⊑⟜data)¨⊸/⥊↕≢data
  chars ← elves∾goblins
  {
    1=part ?
      {𝕊 turn:
        order ← ⍋chars
        {𝕊 nth :
           {
            ∞ : @ ;
            𝕩 : @
          }nth⊑chars
        }¨order
        0
      }•_while_(⊢)1
      0 ;
    0
  }
}
