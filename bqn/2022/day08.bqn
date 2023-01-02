#!/usr/bin/env cbqn
⟨DataFile,_uncurry⟩ ← •Import "../lib.bqn"
map ← (⋈˜∘√∘≠)⊸⥊∾'0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
Sight ← {⟨⌽(𝕨⊸⋈¨↕𝕩),(𝕨⊸⋈¨(1+𝕩)↓↕⊑≢map),⌽(⋈⟜𝕩¨↕𝕨),(⋈⟜𝕩¨(1+𝕨)↓↕1⊑≢map)⟩}_uncurry
# Borders are handled as exceptions
_alldirs_ ← {F _𝕣_ 𝔾 𝕩: 𝔾´{w H dirs: 4=≠dirs ? {w F 𝕩}¨dirs; 0}⟜Sight 𝕩}
Invisible ← {w F xs: ∨´{w≤○(map˙⊸(⊑˜))𝕩}¨xs}
•Show +´¬¨(Invisible _alldirs_ ∧)¨⥊(⋈⌜○↕)_uncurry ≢map
Blocking ← {w F xs: {0=≠xs ? 0; i ← ⊑⟨1⟩⊐˜{w≤○(map˙⊸(⊑˜))𝕩}¨xs⋄ i<≠xs ? 1+i; ≠xs}}
•Show ⌈´(Blocking _alldirs_ ×)¨⥊(⋈⌜○↕)_uncurry ≢map
