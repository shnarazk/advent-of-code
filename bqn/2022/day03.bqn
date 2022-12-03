#!/usr/bin/env cbqn

help ← 1↓"
Solving Advent of Code 2022 in BQN.
Usage:
  command [-h] [--help] input
Options:
  -h, --help: Print this message and exit
  -i: Input file"

o ← "-h"‿"--help" # ‿"-i"
oo ← (≠o) = oi ← o ⊐ ar←•args
•Exit∘•Out∘help⍟(∨´2⊸>) oi
inputData ← ⊑2⊑ ar ⊔˜ (¬-˜⊢× oi⊏˜ ↕∘≠⌈`∘×¬)oo
# •Show inputData

lines ← •FLines inputData
# •Show lines
 
Point ← { 𝕩 < 'a' ? 27+𝕩-'A'; 1+𝕩-'a' }

Part1 ← {
  f‿l ← (2÷˜≠)⊸{⟨𝕨↑𝕩,𝕨↓𝕩⟩} 𝕩
  target ← f (⌈´˘)∘(=⌜) l
  f Point∘(⊑∘/)˜ target 
}
•Show +´ Part1¨ lines

Part2 ← { 
  ⟨a, b, c⟩:{ 
    # •Show ⟨a, b, c⟩
    Common ← { 𝕨(/⟜𝕨)∘(⌈´˘)∘(=⌜)𝕩 }
    s ←⊑ a Common b Common c
    # •Show s 
    Point s
  }
}
•Show +´ Part2˘ ∘‿3 ⥊ lines
