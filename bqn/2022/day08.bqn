#!/usr/bin/env cbqn
⟨DataFile, _uncurry⟩ ← •Import "../lib.bqn"
map ← (⋈˜∘√∘≠)⊸⥊∾'0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
Sight ← {⟨⌽(𝕨⊸⋈¨↕𝕩),(𝕨⊸⋈¨(1+𝕩)↓↕⊑≢map),⌽(⋈⟜𝕩¨↕𝕨),(⋈⟜𝕩¨(1+𝕨)↓↕1⊑≢map)⟩}_uncurry

Part1 ← {
  Visible ← {w F xs: ∧´{w≥○(map˙⊸(⊑˜))𝕩}¨xs}
  ∨´{w F dirs: {w Visible 𝕩}¨dirs}⟜Sight 𝕩
}
•Show +´Part1¨⥊(⋈⌜○↕)_uncurry ≢map

Part2 ← {
  Blocking ← {w F xs: {0=≠xs ? 0; i ← ⊑⟨1⟩⊐˜{w≤○(map˙⊸(⊑˜))𝕩}¨xs⋄ i<≠xs ? 1+i; ≠xs}}
  ×´{w F dirs: {w Blocking 𝕩}¨dirs}⟜Sight 𝕩
}
•Show ⌈´Part2¨⥊(⋈⌜○↕)_uncurry ≢map
