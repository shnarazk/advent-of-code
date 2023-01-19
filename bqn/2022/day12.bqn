#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
# ⟨lines,status,monkeys⟩ ⇐
lines ← •FLines "data/2022/input-day12.txt" lib.DataFile ⟨⟩ # •args
shape ← (≠⋈(≠⊑)) lines
sea_level ← ¯100 
map ← (shape⊸⥊)∘(sea_level⊸+'a'⊸(-˜))∘∾ lines
IndexOf ← {⊑(𝕨⊸=⊑⟜𝕩)¨⊸/⥊↕·≢ 𝕩}
lib.color.green lib.term.Println start ← (sea_level+'S'-'a') IndexOf map
lib.color.green lib.term.Println end ← (sea_level+'E'-'a') IndexOf map
•Show start⊸⊑ map
map sea_level˙⌾(start⊸⊑) ↩
map (sea_level+'z'-'a')⌾(end⊸⊑) ↩
Debug ← {t 𝕊 𝕩:
  lib.term.Up 1+≠𝕩
  {"" lib.term.Outln∾{ 𝕊 c: ({c≥t ? (80)‿(⌊255-255⌊⌊2500÷√c)‿(⌊255⌊30×1.8⋆⁼c); 100‿100‿100} lib.color.RGB 0) lib.color.Out " "}¨𝕩⋄ ⟨⟩ }˘𝕩
 }
Choose ← { other 𝕊 self :
  {
   self ∧○(0⊸<) other ? self⌊1+other; 
   (0<other)∧(other<∞) ? 1+other;
    self
  }
}
MakeNeighbor ← {(⌽⍉)⍟(4-𝕩)(∞⊸»˘)(⌽⍉)⍟𝕩 𝕨}
Neighbors ← {(𝕩⊸MakeNeighbor)¨ ↕4}
reachables ← {(≢map)⥊(¯1+⥊map)≤⥊𝕩}¨ Neighbors map
MaskedNeighbors ← reachables × {(𝕩⊸MakeNeighbor)¨ ↕4}
m ← 1˙⌾(start⊸⊑) map
lib.While {𝕤⋄ 0>end⊑m}‿{𝕤⋄ 0 Debug m (Choose¨˘´⟜ MaskedNeighbors) ↩} 
•Show ans1 ← ¯1+end⊑m # we start the loop with 1.

n ← { sea_level=𝕩 ? 1; 𝕩}¨˘ map
lib.While {𝕤⋄ 0>end⊑n}‿{𝕤⋄ 0 Debug n (Choose¨˘´⟜ MaskedNeighbors) ↩} 
•Show ans1⋈¯1+end⊑n # we start the loop with 1.
