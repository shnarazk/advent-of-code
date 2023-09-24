Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  symbols ← ".#EG"
  data symbols⊸⊐∘> ↩
  blocks ← (1=⊑⟜data)¨↕≢data
  elf_hitpoint ← 3
  goblin_hitpoint ← 3
  elves ← {⟨𝕩,2,elf_hitpoint⟩}¨(2=⊑⟜data)¨⊸/⥊↕≢data
  goblins ← {⟨𝕩,3,goblin_hitpoint⟩}¨(3=⊑⟜data)¨⊸/⥊↕≢data
  chars ← elves∾goblins
  shape ← ≢data
  Show ← {
    𝕊 𝕩 : 2==𝕩 ? ∧´⥊(1=•Type)¨𝕩 ? util.Debug ⊑⟜symbols¨𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : 2==𝕩 ? •Show 𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : 1==𝕩 ? 8<≠𝕩 ? ∧´≡○≠´˘2↕𝕩 ? util.Debug ⍉≍𝕩 ⋄ 𝕩  ;
    𝕊 𝕩 : util.Debug 𝕩 ;
    𝕨 𝕊 𝕩 :
      2==𝕩 ? ∧´⥊(1=•Type)¨𝕩 ? 𝕨 util.Debug ⊑⟜symbols¨𝕩 ⋄ 𝕩  ;
      2==𝕩 ? 𝕨 util.Debug 𝕩 ⋄ 𝕩  ;
      1==𝕩 ? 8<≠𝕩 ? ∧´≡○≠´˘2↕𝕩 ? 𝕨 util.Debug ⍉≍𝕩 ⋄ 𝕩 ;
      1    ? 𝕨 util.Debug 𝕩
  }
  _under_ ← {
      𝔽 _𝕣_ 𝔾 𝕩 :  𝔽𝔾𝕩 ⋄ 𝕩 ;
    𝕨 𝔽 _𝕣_ 𝔾 𝕩 : 𝕨𝔽𝔾𝕩 ⋄ 𝕩
   }
  Act ← {chars 𝕊 i :
    pos‿species‿hitpoint ← i⊑chars
    "enemytype" Show enemytype ← ¬⌾(-⟜2)species
    ⟨⟩≢targets ← (enemytype=1⊸⊑)¨⊸/chars ?
    enemymap ← ∊⟜(⊑¨targets)↕shape
    "rot" Show 4⊸↑ rangeoftargets ← ∧⍷∾⥊enemymap{𝕨◶⟨⟨⟩,⊢⟩𝕩}¨∞⊸≢¨⊸/¨∞ geo.Neighbor8 ↕shape
    (need_to_move ← ∨´(0=⊑⟜data)¨rangeoftargets)∨(∊⟜rangeoftargets⌾⋈pos) ?
    {
      need_to_move ?
        # To move, the unit first considers the squares that are in
        # range and determines which of those squares it could reach
        # in the fewest steps. A step is a single movement to any
        # adjacent (immediately up, down, left, or right) open (.)
        # square. Units cannot move into walls or other units. The
        # unit does this while considering the current positions of
        # units and does not do any prediction about where units will
        # be later. If the unit cannot reach (find an open path to)
        # any of the squares that are in range, it ends its turn. If
        # multiple squares are in range and tied for being reachable
        # in the fewest steps, the square which is first in reading
        # order is chosen.
        "move" Show @
      ; @
    }
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
  "test act" Show chars Act 0
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
