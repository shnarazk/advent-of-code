Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ 'L'=>data
  # floor‿empty‿occupied ← ↕3
  Flip ← {1 𝕊 0 : 2 ; 2 𝕊 m : 5≤m ? 1 ; w 𝕊 m : w}¨
  {
    1=part ? +´⥊2=⊑{⟨Flip⟜((+´2⊸=)¨geometry.Neighbor9)⊑𝕩,⊑𝕩⟩}•_while_(≢´)⋈⟜(0¨)data ;
    grid ← ↕⋈˜⌈´ h‿w ← ≢data
    tran ← ∾⌜{×∘≠◶⟨⟨⟩,1⊸↑⟩(1=⊑⟜data)¨⊸/𝕩}¨⌜{y‿x :
      ⟨
        ⌽(    0‿0⊸≤∧○(∧´)y‿w⊸>)¨⊸/x⊏⎉1 grid
         ((y+1)‿0⊸≤∧○(∧´)h‿w⊸>)¨⊸/x⊏⎉1 grid
        ⌽(    0‿0⊸≤∧○(∧´)h‿x⊸>)¨⊸/y⊏⎉2 grid
         (0‿(x+1)⊸≤∧○(∧´)h‿w⊸>)¨⊸/y⊏⎉2 grid
        ⌽(    0‿0⊸≤∧○(∧´)y‿x⊸>)¨⊸/⟨0,x-y⟩<⊸+0‿0⍉grid
         (    y‿x⊸<∧○(∧´)h‿w⊸>)¨⊸/⟨0,x-y⟩<⊸+0‿0⍉grid
        ⌽((y+1)‿0⊸≤∧○(∧´)h‿x⊸>)¨⊸/⟨0,(x+y)-(w-1)⟩<⊸+0‿0⍉⌽grid
         (    0‿x⊸≤∧○(∧´)y‿w⊸>)¨⊸/⟨0,(x+y)-(w-1)⟩<⊸+0‿0⍉⌽grid
      ⟩
    }¨↕h‿w
    +´⥊2=⊑{⟨Flip⟜((+´2=⊑⟜(⊑𝕩))¨tran)⊑𝕩,⊑𝕩⟩}•_while_(≢´)⋈⟜(0¨)data
  }
}
