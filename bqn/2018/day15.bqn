Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ".#EG"⊸⊐∘> ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elf_hitpoint ← 3
  goblin_hitpoint ← 3
  elves ← {⟨𝕩,2,elf_hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
  goblins ← {⟨𝕩,2,goblin_hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
  util.Debug chars ← elves∾goblins
  map ← ≢data
  util.Debug (∊⟜(↕10))⌾⋈ 1
  Act ← {chars 𝕊 i:
     pos‿species‿hitpoint ← i⊑chars
    enemytype ← ¬⌾(-⟜2)species
    enemies ← (enemytype⊸=)¨⊸/chars
    {
      ⟨⟩≡enemies ? @
      ;
        enemymap ← ∊⟜(⊑¨enemies)⌾⋈¨⊸/↕map
        rangeoftargets ← ⍷enemymap×geo.Neighbor8¨↕map
        {
          (∨´(0=⊑⟜data)¨rangeoftargets)∧(¬∊⟜rangeoftargets⌾⋈pos) ? @ ;
           # move
          {
            ∊⟜rangeoftargets⌾⋈pos ?
               "move"
            ; @
          }
          # attack
          adjacent ← geo.Neighbor8 pos
          {
            ⟨⟩≢attackabletargets ← ∊⟜adjacent⊸/enemies ?
              order ← ⍋(2‿0‿1⊸⊏)attackabletargets
              target ← attackabletargets⊑˜⊑order
            ;
              @
          }
        }
    }
  }
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
