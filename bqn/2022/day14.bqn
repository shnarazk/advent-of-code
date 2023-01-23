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
Drop ← { part 𝕊 map:
  abyss ← ⊑≢map
  y‿x ← start ← 0‿500
  falling‿hasRoom ← 1‿1
  lib.While { 𝕤⋄ falling } ‿ { 𝕤 ⋄
    new_y ← 1+y
    {
      abyss=new_y ? map 1˙⌾(y‿x⊸⊑) ↩ ⋄ falling‿hasRoom ↩ 0‿(part=2);
      (new_y‿x (¬⊑) map) ? y ↩ new_y ;
      (new_y‿(¯1+x) (¬⊑) map) ? y‿x ↩ new_y‿(¯1+x) ;
      (new_y‿( 1+x) (¬⊑) map) ? y‿x ↩ new_y‿( 1+x) ;
      map 1˙⌾(y‿x⊸⊑) ↩ ⋄ falling‿hasRoom ↩ 0‿(start ≢ y‿x)
    }
  }
  hasRoom‿map
}

Solve ⇐ { part 𝕊 data:
  seg ← lib.ParseInts¨ data
  "geometry" lib.Debug xmax‿ymax ← (2⊸+⌈´)¨(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾seg
  { 2=part ? xmax ymax⊸+ ↩; @ }
  segments ← {(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈¨○(/⟜𝕩))´ 𝕨} 𝕩}¨ seg
  map ← segments Inject´˜ ymax‿xmax⥊ 0˙↕xmax×ymax
  continue‿sands ← 1‿0
  lib.While { 𝕤 ⋄ continue }‿{ 𝕤 ⋄ continue‿map ↩ part Drop map ⋄ sands 1⊸+ ↩ }
  {1=part ? ¯1+sands; sands}
}
