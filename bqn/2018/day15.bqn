Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Distance ← {(⊢⌊𝕨{𝕨◶⟨∞,⊢⟩𝕩}¨(1+⌊´¨∘(∞⊸geo.Neighbor4)))⍟(2×(≠𝕨))(-𝕩) geo.Rotate 0⌾(0‿0⊸⊑)∞¨𝕨}
  symbols ← ".#EG"
  shape ← ≢data symbols⊸⊐∘>∘(⟨⟩⊸≢¨⊸/)∘(' '⊸≠¨⊸/¨) ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elf_attack_power‿goblin_attack_power‿hitpoint ← 3‿3‿200
  chars ← ↕∘≠⊸(⋈⊸∾¨){
    elves ← {⟨𝕩,2,hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
    goblins ← {⟨𝕩,3,hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
    elves∾goblins
  }
  # CurrentMap ← {blocks{i‿pos‿s‿hp 𝕊 𝕩: (0<hp)◶⟨⊢,s⌾(pos⊸⊑)⟩𝕩}´𝕩}
  ended ← 0
  Act ← {
    i 𝕊 chars  :
      id‿pos‿species‿hitpoint ← i⊑chars
      0<hitpoint ?
      enemytype ← ¬⌾(-⟜2)species
      livings ← (0<3⊸⊑)¨⊸/chars
      pol ← 1⊸⊑¨livings
      current_open ← 1⌾(pos⊸⊑)¬((∊⟜pol⌾⋈)∨(⊑⟜blocks))¨↕shape
      targets ← (enemytype=2⊸⊑)¨⊸/livings
      {⟨⟩≢targets ? ended ↩ 1 ; @}
      ⟨⟩≢targets ?
      enemymap ← ∊⟜(1⊸⊑¨targets)↕shape
      rangeoftargets ← ∧⍷∾⥊enemymap{𝕨◶⟨⟨⟩,⊢⟩𝕩}¨∞⊸≢¨⊸/¨∞ geo.Neighbor4 ↕shape
      {
        ∊⟜rangeoftargets⌾⋈pos ? @
        ;
          destination ← pos
          {
            ¬∊⟜rangeoftargets⌾⋈pos ?
            d ← current_open Distance pos
            destination ↩ ⟨⟩⊸≢◶⟨⊢,1⊸⊑⊑⟩∧(∞≠⊑)¨⊸/{𝕩⋈˜𝕩⊑d}¨rangeoftargets
            ; @
          }
          ⟨⟩≢destination ?
          path ← current_open Distance destination
          pos ↩ 1⊑⊑∧(⊑⟜path)⊸⋈¨(⊑⟜current_open)¨⊸/∞⊸≢¨⊸/pos⊑∞ geo.Neighbor4 ↕shape
          chars pos⌾(1⊸⊑id⊸⊑) ↩
          ; @
      }
      adjacents ← ∞⊸≢⊸/pos⊑∞ geo.Neighbor4 ↕shape
      {
        ⟨⟩≢attackabletargets ← ((∊⟜adjacents)⌾⋈1⊸⊑)¨⊸/targets ?
        target ← attackabletargets⊑˜⊑⍋(3‿1⊸⊏)¨attackabletargets
        p ← (2⊸=)◶⟨goblin_attack_power,elf_attack_power⟩species
        chars (0⌈-⟜p)⌾(3⊸⊑(⊑target)⊸⊑) ↩
        ; @
      }
      chars
      ;
    𝕨 𝕊 𝕩 : 𝕩
  }
  {
    1=part ?
      (-⟜ended)⊸×⟜(⌈´)´{turn‿points:
        chars ↩ chars Act´⍒(1⊸⊑)¨chars
        ep ← +´(3⊸⊑)¨(2=2⊸⊑)¨⊸/chars
        gp ← +´(3⊸⊑)¨(3=2⊸⊑)¨⊸/chars
        ⟨turn+1,util.Progress ep⋈gp⟩
      }•_while_(0<⌊´∘(1⊸⊑))⟨0,1‿1⟩
    ;
      initial_chars ← chars
      2⊑{min‿max‿outcome :
        util.Progress 𝕩
        mid ← ⌊2÷˜min+max
        chars‿elf_attack_power‿ended ↩ initial_chars‿mid‿0
        result ← {turn‿points :
          chars ↩ chars Act´⍒(1⊸⊑)¨chars
          ep ← +´(3⊸⊑)¨(2=2⊸⊑)¨⊸/chars
          gp ← +´(3⊸⊑)¨(3=2⊸⊑)¨⊸/chars
          ⟨turn+1,(ep×∧´(0<3⊸⊑)¨(2=2⊸⊑)¨⊸/chars)⋈gp⟩
        }•_while_(0<⌊´∘(1⊸⊑))⟨0,1‿1⟩
        {∧´(0<3⊸⊑)¨(2=2⊸⊑)¨⊸/chars ? ⟨min,mid,(-⟜ended)⊸×⟜(⌈´)´result⟩ ; ⟨mid,max,outcome⟩}
      }•_while_(1<(-˜´2⊸↑))4‿300‿0
  }
}
