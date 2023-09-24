_under_ ← {
    𝔽 _𝕣_ 𝔾 𝕩 :  𝔽𝔾𝕩 ⋄ 𝕩 ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩 : 𝕨𝔽𝔾𝕩 ⋄ 𝕩
}
Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Distance ← {(⊢⌊𝕨{𝕨◶⟨∞,⊢⟩𝕩}¨(1+⌊´¨∘(∞⊸geo.Neighbor4)))⍟(2×(≠𝕨))(-𝕩) geo.Rotate 0⌾(0‿0⊸⊑)∞¨𝕨}
  symbols ← ".#EG"
  data (⟨⟩⊸≢¨⊸/)∘(' '⊸≠¨⊸/¨) ↩
  data symbols⊸⊐∘> ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elf_hitpoint ← 200
  goblin_hitpoint ← 200
  attack¯power ← 3
  chars ← ↕∘≠⊸(⋈⊸∾¨){
    "# ≠elves" util.Debug ≠elves ← {⟨𝕩,2,elf_hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
    "# ≠goblins" util.Debug ≠goblins ← {⟨𝕩,3,goblin_hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
    elves∾goblins
  }
  shape ← ≢data
  CurrentMap ← {blocks{i‿pos‿s‿hp 𝕊 𝕩: (0<hp)◶⟨⊢,s⌾(pos⊸⊑)⟩𝕩}´𝕩}
  Show ← {
    𝕊 𝕩 : 2==𝕩 ? ∧´⥊((3⊸≥)∧1=•Type)¨𝕩 ? util.Debug ⊑⟜symbols¨𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : 2==𝕩 ? •Show 𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : 1==𝕩 ? 8<≠𝕩 ? ∧´≡○≠´˘2↕𝕩 ? util.Debug ⍉≍𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : util.Debug 𝕩 ;
    𝕨 𝕊 𝕩 :
      2==𝕩 ? ∧´⥊((3⊸≥)∧1=•Type)¨𝕩 ? 𝕨 util.Debug ⊑⟜symbols¨𝕩 ⋄ 𝕩  ;
      2==𝕩 ? 𝕨 util.Debug 𝕩 ⋄ 𝕩  ;
      1==𝕩 ? 8<≠𝕩 ? ∧´≡○≠´˘2↕𝕩 ? 𝕨 util.Debug ⍉≍𝕩 ⋄ 𝕩 ;
      1    ? 𝕨 util.Debug 𝕩
  }
  ended ← 0
  Act ← {
    i 𝕊 chars  :
      "turn" Show id‿pos‿species‿hitpoint ← i⊑chars
      0<hitpoint ?
      "enemytype" Show enemytype ← ¬⌾(-⟜2)species
      livings ← (0<3⊸⊑)¨⊸/chars
      pol ← 1⊸⊑¨livings
      current_open ← 1⌾(pos⊸⊑)¬((∊⟜pol⌾⋈)∨(⊑⟜blocks))¨↕shape
      targets ← (enemytype=2⊸⊑)¨⊸/livings
      {⟨⟩≢targets ? ended ↩ 1 ; @}
      ⟨⟩≢targets ?
      "targets" Show targets
      "# enemymap" Show enemymap ← ∊⟜(1⊸⊑¨targets)↕shape
      "RoT" Show rangeoftargets ← ∧⍷∾⥊enemymap{𝕨◶⟨⟨⟩,⊢⟩𝕩}¨∞⊸≢¨⊸/¨∞ geo.Neighbor4 ↕shape
      # (∨´(0=⊑⟜data)¨rangeoftargets) ?
      "# already in attack position?" Show ∊⟜rangeoftargets⌾⋈pos
      {
        ∊⟜rangeoftargets⌾⋈pos ? @
        ;
          destination ← pos
          {
            ¬∊⟜rangeoftargets⌾⋈pos ?
            d ← current_open Distance pos
            "destination" Show destination ↩ ⟨⟩⊸≢◶⟨⊢,1⊸⊑⊑⟩∧(∞≠⊑)¨⊸/{𝕩⋈˜𝕩⊑d}¨rangeoftargets
            ; @
          }
          ⟨⟩≢destination ?
          path ← current_open Distance destination
          "check" Show pos⊑∞ geo.Neighbor4 ↕shape
          newpos ← 1⊑⊑∧(⊑⟜path)⊸⋈¨"xx"Show(⊑⟜current_open)¨⊸/∞⊸≢¨⊸/pos⊑∞ geo.Neighbor4 ↕shape
          "move to" Show pos ↩ newpos
          chars pos⌾(1⊸⊑id⊸⊑) ↩
          ;
          @
      }
      adjacents ← ∞⊸≢⊸/pos ⊑∞ geo.Neighbor4 ↕shape
      {
        ⟨⟩≢attackabletargets ← ((∊⟜adjacents)⌾⋈1⊸⊑)¨⊸/targets ?
        "weakest target to attack" Show target ← attackabletargets⊑˜⊑⍋(3‿1⊸⊏)¨attackabletargets
        "reduced to" Show _under_(3⊸⊑(⊑target)⊸⊑) chars (0⌈-⟜attack¯power)⌾(3⊸⊑(⊑target)⊸⊑) ↩
        ;
        @
      }
      chars
      ;
    𝕨 𝕊 𝕩 : 𝕩
  }
  {
    1=part ?
      (-⟜ended)⊸×⟜(⌈´)´util.Debug{𝕊 turn‿points:
        order ← ⍋(1⊸⊑)¨chars
        order util.Debug ⍉≍chars ↩ chars Act´⌽order
        (0.1+2×6>+´(0<3⊸⊑)¨chars) util.Progress ⊑⟜symbols¨CurrentMap chars
        "elves points" Show ep ← +´(3⊸⊑)¨(2=2⊸⊑)¨⊸/chars
        "goblin points" Show gp ← +´(3⊸⊑)¨(3=2⊸⊑)¨⊸/chars
        ⟨turn+1,ep⋈gp⟩
      }•_while_(0<⌊´∘(1⊸⊑))⟨0,1‿1⟩
      ;
    0
  }
}
