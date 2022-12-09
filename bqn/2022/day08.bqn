#!/usr/bin/env cbqn
⟨DataFile, ParseInts⟩ ← •Import "../lib.bqn"
map ← '0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
map_height ← ≠map
map_width ← ≠⊑map
•Show ⟨map_height, map_width⟩

At ← { F ⟨x, y⟩ : y⊑x⊑map }
Part1 ← { F ⟨x, y⟩ :
  Sight ← {4‿∘⥊⟨(𝕨⊸⋈¨↕𝕩),(𝕨⊸⋈¨(1+𝕩)↓↕map_height),(⋈⟜𝕩¨↕𝕨),(⋈⟜𝕩¨(1+𝕨)↓↕map_width)⟩}
  Invisible ← {0⌈´(𝕨≤At)¨𝕩} 
  dirs ← x Sight y
  h ← At ⟨x, y⟩
  ¬∧´⥊h Invisible¨ dirs
}
•Show +´Part1¨⥊(↕map_width) ⋈⌜ (↕map_height)
ScenicScore ← { F ⟨x, y⟩ :
  Sight ← {4‿∘⥊⟨⌽(𝕨⊸⋈¨↕𝕩), (𝕨⊸⋈¨(1+𝕩)↓↕map_height), ⌽(⋈⟜𝕩¨↕𝕨), (⋈⟜𝕩¨(1+𝕨)↓↕map_width)⟩}
  dirs ← x Sight y
  h ← At ⟨x, y⟩
  Blocking ← {
    0 = ≠𝕩 ? 0;
    i←⊑⟨1⟩⊐˜(h≤At)¨𝕩
    i<≠𝕩 ? 1+i;
    ≠𝕩
  }
  ×´⥊Blocking¨ dirs
}
•Show ⌈´ScenicScore¨⥊(↕map_width) ⋈⌜ (↕map_height)
