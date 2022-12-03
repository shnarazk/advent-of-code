#!/usr/bin/env bqn

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
breakpoint ← 2⊸(÷˜)¨ ≠¨ lines
•Show breakpoint {⟨𝕨↑𝕩,𝕨↓𝕩⟩}¨ lines
 
Part1 ← {
 𝕊 ⟨f,l⟩: { 
    target ← f (⌈´˘)∘(=⌜) l
    target ⊑∘/ f
  }
}
Point ← {
  𝕩 < 'a' ? 27+𝕩-'A';
            1+𝕩-'a'
}

•Show (Part1)¨ (breakpoint {⟨𝕨↑𝕩,𝕨↓𝕩⟩}¨ lines)
•Show (Point Part1)¨ (breakpoint {⟨𝕨↑𝕩,𝕨↓𝕩⟩}¨ lines)
•Show +´(Point Part1)¨ (breakpoint {⟨𝕨↑𝕩,𝕨↓𝕩⟩}¨ lines)

# Part2 ← { 0 }
# •Show +´ Part1¨ lines
# •Show +´ Part2¨ lines
