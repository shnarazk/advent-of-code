#!/usr/bin/env cbqn
⟨DataFile, ParseInts⟩ ← •Import "../lib.bqn"
map ← '0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
map_height ← ≠map
map_width ← ≠⊑map
•Show ⟨map_height, map_width⟩
At ← { F ⟨x, y⟩ : y⊑x⊑map }

Sight ← {4‿∘⥊⟨(𝕨⊸⋈¨↕𝕩),(𝕨⊸⋈¨(1+𝕩)↓↕map_height),(⋈⟜𝕩¨↕𝕨),(⋈⟜𝕩¨(1+𝕨)↓↕map_width)⟩}
# Visible ← {0⌈´(𝕨>At)¨𝕩} 
# Part1 ← { F ⟨x, y⟩ :
#   dirs ← x Sight y
#   h ← At ⟨x, y⟩
#   result ← ∨´⥊h Visible¨ dirs
#   •Show ⟨x, y, result⟩
#   result
# }
Invisible ← {0⌈´(𝕨≤At)¨𝕩} 
Part1 ← { F ⟨x, y⟩ :
  dirs ← x Sight y
  h ← At ⟨x, y⟩
  ¬∧´⥊h Invisible¨ dirs
}
•Show +´Part1¨⥊(↕map_width) ⋈⌜ (↕map_height)

# •Show +´(100000⊸≥)¨⊸/ lInes
# used ← ⌈´ lines
# need ← used - 40000000 
# •Show ∧(need⊸≤)¨⊸/ lines
