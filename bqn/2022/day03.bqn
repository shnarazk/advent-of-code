#!/usr/bin/env cbqn

lines ← •FLines ⊑•args
# •Show lines

Point ← { 𝕩 < 'a' ? 27+𝕩-'A'; 1+𝕩-'a' }

Part1 ← {
  f‿l ← (2÷˜≠)⊸{⟨𝕨↑𝕩,𝕨↓𝕩⟩} 𝕩
  f (Point∘(⊑∘/)˜)⟜(⌈´˘)∘(=⌜) l
}
•Show +´ Part1¨ lines

Part2 ← { 
  ⟨a, b, c⟩: { 
    Common ← { 𝕨(/⟜𝕨)∘(⌈´˘)∘(=⌜)𝕩 }
    Point ⊑ a Common b Common c
  }
}
•Show +´ Part2˘ ∘‿3 ⥊ lines
