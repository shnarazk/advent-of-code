_under_ ← {
    𝔽 _𝕣_ 𝔾 𝕩 :  𝔽𝔾𝕩 ⋄ 𝕩 ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩 : 𝕨𝔽𝔾𝕩 ⋄ 𝕩
}
Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Distance ← {(⊢⌊𝕨{𝕨◶⟨∞,⊢⟩𝕩}¨(1+⌊´¨∘(∞⊸geo.Neighbor4)))⍟(2×(≠𝕨))𝕩 geo.Rotate 0⌾(0‿0⊸⊑)∞¨𝕨}
  symbols ← ".#EG"
  data symbols⊸⊐∘> ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elf_hitpoint ← 3
  goblin_hitpoint ← 3
  attack¯power ← 3
  chars ← ↕∘≠⊸(⋈⊸∾¨){
    "≠elves" util.Debug ≠elves ← {⟨𝕩,2,elf_hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
    "≠goblins" util.Debug ≠goblins ← {⟨𝕩,3,goblin_hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
    elves∾goblins
  }
  shape ← ≢data
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
  Act ← {chars 𝕊 i :
    Show i
    id‿pos‿species‿hitpoint ← i⊑chars
    0<hitpoint ?
    "enemytype" Show enemytype ← ¬⌾(-⟜2)species
    ⟨⟩≢targets ← (enemytype=2⊸⊑)¨⊸/chars ?
    Show enemymap ← ∊⟜(1⊸⊑¨targets)↕shape
    "RoT" Show 4⊸↑ rangeoftargets ← ∧⍷∾⥊enemymap{𝕨◶⟨⟨⟩,⊢⟩𝕩}¨∞⊸≢¨⊸/¨∞ geo.Neighbor4 ↕shape
    (need_to_move ← ∨´(0=⊑⟜data)¨rangeoftargets)∨(∊⟜rangeoftargets⌾⋈pos) ?
    destination ← pos
    {
      need_to_move ?
        Show pol ← 1⊸⊑¨(0<3⊸⊑)¨⊸/chars # positions of lives
        d ← pos Distance˜Show¬((∊⟜pol⌾⋈)∨(⊑⟜blocks))¨↕shape
        "destination" Show destination ↩ ⟨⟩⊸≢◶⟨⊢,1⊸⊑⊑⟩∧(∞≠⊑)¨⊸/{𝕩⋈˜𝕩⊑d}¨rangeoftargets
      ; @
    }
    ⟨⟩≢destination ?
    "move to" Show pos ↩ destination
    adjacents ← ∞⊸≢⊸/pos ⊑∞ geo.Neighbor4 ↕shape
    ⟨⟩≢attackabletargets ← ((∊⟜adjacents)⌾⋈1⊸⊑)¨⊸/targets ?
    "weakest target to attack" Show target ← attackabletargets⊑˜⊑⍋(2‿0⊸⊏)¨attackabletargets
    "reduced to" Show _under_(3⊸⊑(⊑target)⊸⊑) chars -⟜attack¯power⌾(3⊸⊑(⊑target)⊸⊑) ↩
    ;
      @
  }
  "test: Act" Show chars Act 0
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
