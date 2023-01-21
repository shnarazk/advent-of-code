#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
Run ⇐ { part 𝕊 data:
  segments ← lib.ParseInts¨ data
  ⟨xmin,xmax⟩‿⟨ymin,ymax⟩ ← (⌊´⋈(1⊸+⌈´))¨(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾segments
  map ← ymax‿xmax⥊ 0˙↕xmax×ymax
  "map" lib.Debug ≢map
}
