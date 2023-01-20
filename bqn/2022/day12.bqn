#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lines ← •FLines "data/2022/input-day12.txt" lib.DataFile •args
shape ← (≠⋈(≠⊑)) lines
sea_level ← ¯100
map ← (shape⊸⥊)∘(sea_level⊸+'a'⊸(-˜))∘∾ lines
IndexOf ← { ⊑(𝕨⊸=⊑⟜𝕩)¨⊸/⥊↕·≢ 𝕩 }
start‿end ← (map⊸(IndexOf˜)sea_level⊸+∘-⟜'a')¨ 'S'‿'E'
map ⟨sea_level,sea_level+'z'-'a'⟩⌾(start‿end⊸⊑) ↩
Debug ← { t 𝕊 𝕩:
  lib.term.Up 1+≠𝕩
  Colorize ← { 𝕩≥𝕨 ? 80‿(⌊255-255⌊⌊2500÷√𝕩)‿(⌊255⌊30×1.8⋆⁼𝕩); 100‿100‿100 }
  { lib.term.Outln∾{ ((t Colorize 𝕩) lib.color.RGB 0)∾" " }¨𝕩⋄ ⟨⟩ }˘𝕩
}
Choose ← { other 𝕊 self: {
    self ∧○(0⊸<) other  ? self⌊1+other;
    (0<other)∧(other<∞) ? 1+other;
    self
  }
}
MakeNeighbor ← { (⌽⍉)⍟(4-𝕩)(∞⊸»˘)(⌽⍉)⍟𝕩 𝕨 }
Neighbors ← { (𝕩⊸MakeNeighbor)¨ ↕4 }
reachables ← { (≢map)⥊(¯1+⥊map)≤⥊𝕩 }¨ Neighbors map
MaskedNeighbors ← reachables × { (𝕩⊸MakeNeighbor)¨ ↕4 }
m ← 1˙⌾(start⊸⊑) map
lib.While { 𝕤⋄ 0>end⊑m }‿{ 𝕤⋄ 0 Debug m (Choose¨˘´⟜ MaskedNeighbors) ↩ }
n ← { sea_level=𝕩 ? 1; 𝕩 }¨˘ map
lib.While { 𝕤⋄ 0>end⊑n }‿{ 𝕤⋄ 0 Debug n (Choose¨˘´⟜ MaskedNeighbors) ↩ }
(lib.term.reset∾lib.term.clear) lib.term.Println (⋈○(¯1⊸+end⊸⊑))´ m‿n
