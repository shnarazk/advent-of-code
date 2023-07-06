lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 data:
  { 1=part ?
      Facets ← {x‿y‿z:
        [
          ⟨x-0.5,y,z⟩, ⟨x+0.5,y,z⟩
          ⟨x,y-0.5,z⟩, ⟨x,y+0.5,z⟩
          ⟨x,y,z-0.5⟩, ⟨x,y,z+0.5⟩
        ]
      }
      "fs" lib.Debug ≠fs ← ⥊<˘∾Facets¨ cubes ← lib.ParseInts¨data
      (≠-(2⊸×∘(-○≠⟜⍷)))fs
      # if you need not only the number of facets but also facets themselves.
      # "envelop" lib.Debug ≠envelop ← {1=+´∧´¨fs=<𝕩}¨⊸/ fs
      # envelop ← (1⊸=·+´˘(∧´=)⌜˜)⊸/ fs out of memory
      # ≠envelop
    ;
      # we need 'direction'
      ∞
  }
}
