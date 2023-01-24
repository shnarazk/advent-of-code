lib ← •Import "../lib.bqn"

InjectBlock ← {
 ⟨⟩ 𝕊 m: m;
  s 𝕊 m:
    m { beg‿end 𝕊 m:
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
DropSand ← { part 𝕊 map‿trace:
  # ! 0≠≠trace
  abyss ← ⊑≢map
  y‿x ← start ← ¯1⊑trace
  falling ← 1
  lib.While { 𝕤, falling } ‿ { 𝕤,
    new_y ← 1+y
    {
      abyss=new_y ?
        map 1˙⌾(y‿x⊸⊑) ↩
        { 1=part ? trace ↩ ⟨⟩ ; @ }
        trace ¯1⊸↓ ↩
        falling ↩ 0
        ;
      (new_y‿x (¬⊑) map) ?
        y ↩ new_y
        trace ∾⟜⟨y‿x⟩ ↩
        ;
      (new_y‿(¯1+x) (¬⊑) map) ?
        y‿x ↩ new_y‿(¯1+x)
        trace ∾⟜⟨y‿x⟩ ↩
        ;
      (new_y‿( 1+x) (¬⊑) map) ?
        y‿x ↩ new_y‿( 1+x)
        trace ∾⟜⟨y‿x⟩ ↩
      ;
        map 1˙⌾(y‿x⊸⊑) ↩,
        trace ¯1⊸↓ ↩
        falling ↩ 0
    }
  }
  map‿trace
}

Solve ⇐ { part 𝕊 data:
  seg ← lib.ParseInts¨ data
  "geometry" lib.Debug xmax‿ymax ← (2⊸+⌈´)¨(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾seg
  { 2=part ? xmax ymax⊸+ ↩; @ }
  segments ← {(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈¨○(/⟜𝕩))´ 𝕨} 𝕩}¨ seg
  map ← segments InjectBlock´˜ ymax‿xmax⥊ 0˙↕xmax×ymax
  sands‿trace ← 0‿⟨0‿500⟩
  lib.While { 𝕤, 0<≠trace }‿{ 𝕤
    map‿trace ↩ part DropSand map‿trace
    sands 1⊸+ ↩
    # "sand‿trace" lib.Debug sands‿(≠trace)
  }
  {1=part ? ¯1+sands; sands}
}
