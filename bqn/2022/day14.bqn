#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
Inject ← {
 ⟨⟩ 𝕊 m: m;
  s 𝕊 m:
    m {
      beg‿end 𝕊 m:
        dx‿dy ← end-beg
        seq ← {
          0<dy ? (⋈⟜(0⊑beg))¨(1⊑beg)+↕1+|dy;
          0>dy ? (⋈⟜(0⊑end))¨(1⊑end)+↕1+|dy;
          0<dx ? ((1⊑beg)⊸⋈)¨(0⊑beg)+↕1+|dx;
          0>dx ? ((1⊑end)⊸⋈)¨(0⊑end)+↕1+|dx;
           ! 0
        }
        (1˙¨seq)⌾(seq⊸⊑) m
    }´⥊⋈˘2↕s
}
Run ⇐ { part 𝕊 data:
  seg ← lib.ParseInts¨ data
  ⟨xmin,xmax⟩‿⟨ymin,ymax⟩ ← (⌊´⋈(1⊸+⌈´))¨(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾seg
  segments ← {(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈¨○(/⟜𝕩))´ 𝕨} 𝕩}¨ seg
  map ← segments (Inject´)˜ ymax‿xmax⥊ 0˙↕xmax×ymax
  "map shape" lib.Debug ≢map
}
