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
  "≠elves" util.Debug ≠elves ← {⟨𝕩,2,elf_hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
  "≠goblins" util.Debug ≠goblins ← {⟨𝕩,3,goblin_hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
  chars ← elves∾goblins
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
  Act ← {chars 𝕊 i‿map :
    pos‿species‿hitpoint ← i⊑chars
    "enemytype" Show enemytype ← ¬⌾(-⟜2)species
    ⟨⟩≢targets ← (enemytype=1⊸⊑)¨⊸/chars ?
    enemymap ← ∊⟜(⊑¨targets)↕shape
    "rot" Show 4⊸↑ rangeoftargets ← ∧⍷∾⥊enemymap{𝕨◶⟨⟨⟩,⊢⟩𝕩}¨∞⊸≢¨⊸/¨∞ geo.Neighbor8 ↕shape
    (need_to_move ← ∨´(0=⊑⟜data)¨rangeoftargets)∨(∊⟜rangeoftargets⌾⋈pos) ?
    destination ← pos
    {
      need_to_move ?
        d ← pos Distance˜0=map
        "destination" Show destination ↩ ⟨⟩⊸≢◶⟨⊢,1⊸⊑⊑⟩∧(∞≠⊑)¨⊸/{𝕩⋈˜𝕩⊑d}¨rangeoftargets
      ; @
    }
    ⟨⟩≢destination ?
    # attack
      # To attack, the unit first determines all of the targets that
      # are in range of it by being immediately adjacent to it.
      # If there are no such targets, the unit ends its turn.
      # Otherwise, the adjacent target with the fewest hit points is
      # selected; in a tie, the adjacent target with the fewest hit
      # points which is first in reading order is selected.
    adjacent ← geo.Neighbor8 pos
    ⟨⟩≢attackabletargets ← ∊⟜adjacent⊸/targets ?
    order ← ⍋(2‿0‿1⊸⊏)attackabletargets
    target ← attackabletargets⊑˜⊑order
    ;
      @
  }
  "test act" Show chars Act 0⋈data
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
