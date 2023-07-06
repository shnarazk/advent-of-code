lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 data:
  Facets ← {x‿y‿z:
    [
      ⟨x-0.5,y,z⟩, ⟨x+0.5,y,z⟩
      ⟨x,y-0.5,z⟩, ⟨x,y+0.5,z⟩
      ⟨x,y,z-0.5⟩, ⟨x,y,z+0.5⟩
    ]
  } 
  fs ← ∾Facets¨ cubes ← lib.ParseInts¨data
  { 1=part ? (≠-(2⊸×∘(-○≠⟜⍷))) fs; @}
} 
