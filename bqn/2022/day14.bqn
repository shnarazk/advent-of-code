#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
Run ⇐ { part 𝕊 data:
  problems ← lib.ParseInts¨ data
  xs‿ys ← (¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾problems
  "area" lib.Debug ⟨xmin,xmax⟩‿⟨ymin,ymax⟩ ← (⌊´⋈⌈´)¨ xs‿ys
}
# •arsgia
# a‿b gf 𝕩
# 𝕩 (g○f˜)˜´ a‿b
