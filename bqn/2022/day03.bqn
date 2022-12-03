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
    "A X": 1 + 3;
    "A Y": 2 + 6;
    "A Z": 3 + 0;
    "B X": 1 + 0;
    "B Y": 2 + 3;
    "B Z": 3 + 6;
    "C X": 1 + 6;
    "C Y": 2 + 0;
    "C Z": 3 + 3;
    0
}
Part2 ← {
    "A X": 3 + 0;
    "A Y": 1 + 3;
    "A Z": 2 + 6;
    "B X": 1 + 0;
    "B Y": 2 + 3;
    "B Z": 3 + 6;
    "C X": 2 + 0;
    "C Y": 3 + 3;
    "C Z": 1 + 6;
    0
}
# •Show +´ Part1¨ lines
# •Show +´ Part2¨ lines
