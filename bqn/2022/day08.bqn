#!/usr/bin/env cbqn
⟨DataFile,_uncurry⟩ ← •Import "../lib.bqn"
map ← (⋈˜∘√∘≠)⊸⥊∾'0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
# We need all four direction map. So the split train found in BQNcrate is not appropriate.
# Sight ← {𝕊⟨w,h⟩: w (((h⊸(⋈˜)¨¨)∘⊣)∾((w⊸⋈¨¨)∘⊢))○{𝕊 p:{p>𝕩?¯1+p-𝕩;𝕩}¨¨p((⊢-˜+`×¬)∘=⊔⊢)↕1⊑≢map} h}
Sight ← {⟨⌽(𝕨⊸⋈¨↕𝕩),(𝕨⊸⋈¨(1+𝕩)↓↕⊑≢map),⌽(⋈⟜𝕩¨↕𝕨),(⋈⟜𝕩¨(1+𝕨)↓↕1⊑≢map)⟩}_uncurry
_alldirs_ ← {F _𝕣_ 𝔾 𝕩: 𝔾´{w H dirs: {w F 𝕩}¨dirs}⟜Sight 𝕩}

# We need to prove all four directions are invisible pathes. It can't be caused from the
# fact we have a visible path. Because, on the edge, the path is zero length and thus is
# handled as a non-existing path.
Invisible ← {w F xs: ∨´{w≤○(map˙⊸(⊑˜))𝕩}¨xs}
•Show +´¬¨(Invisible _alldirs_ ∧)¨⥊(⋈⌜○↕)_uncurry ≢map

Blocking ← {w F xs: {0=≠xs ? 0; i ← ⊑⟨1⟩⊐˜{w≤○(map˙⊸(⊑˜))𝕩}¨xs⋄ i<≠xs ? 1+i; ≠xs}}
•Show ⌈´(Blocking _alldirs_ ×)¨⥊(⋈⌜○↕)_uncurry ≢map
