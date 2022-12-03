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
 
Point ← { 𝕩 < 'a' ? 27+𝕩-'A'; 1+𝕩-'a' }

Part1b ← {
  breakpoint ← 2÷˜≠ 𝕩
  f ← breakpoint ↑ 𝕩 
  l ← breakpoint ↓ 𝕩
  target ← f (⌈´˘)∘(=⌜) l
  target ⊑∘/ f
}
•Show +´(Point Part1b)¨ lines

# Part2 ← { 0 }
# •Show +´ Part1¨ lines
# •Show +´ Part2¨ lines
