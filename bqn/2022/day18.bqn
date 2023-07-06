lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 data:
  Facets ← {x‿y‿z:
    [
      ⟨x-0.5,y,z⟩, ⟨x+0.5,y,z⟩
      ⟨x,y-0.5,z⟩, ⟨x,y+0.5,z⟩
      ⟨x,y,z-0.5⟩, ⟨x,y,z+0.5⟩
    ]
  } 
  "fs" lib.Debug ≠fs ← ⥊<˘∾Facets¨ cubes ← lib.ParseInts¨data
  "envelop" lib.Debug ≠envelop ← {1=+´∧´¨fs=<𝕩}¨⊸/ fs
  # envelop ← (1⊸=·+´˘(∧´=)⌜˜)⊸/ fs out of memory
  { 1=part ?
      # (≠-(2⊸×∘(-○≠⟜⍷)))fs
      ≠envelop
    ; 
      ≠envelop  # 直線距離が1未満ならそれは隣接facetなのでは
  }
} 
