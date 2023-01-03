#!/usr/bin/env cbqn
⟨DataFile⟩ ← •Import "../lib.bqn"
map ← (⋈˜√∘≠)⊸⥊∾'0'-˜˜˜ •FLines "data/2022/input-day08.txt" DataFile •args
Sight ← {𝕊 ⟨w,x⟩: w((x⊸(⋈˜)¨¨⊣)∾(w⊸⋈¨¨⊢))○{𝕊 p:{p>𝕩?¯1+p-𝕩;𝕩}¨¨p((⊢-˜+`×¬)∘=⊔⊢)↕≠map}x}
_all_ ← {F _𝕣_ G 𝕩: {w H d: 4=≠d ? G´{w F 𝕩}¨d; 0}⟜Sight 𝕩}
•Show+´(¬{w F d: ∨´{w≤○(⊑⟜map)𝕩}¨d}_all_∧)¨⥊⋈⌜○↕´≢map
•Show⌈´({w F d: (≠d)⌊1+⊑⟨1⟩⊐˜w⊸(≤○(⊑⟜map))¨d}_all_×)¨⥊⋈⌜○↕´≢map
