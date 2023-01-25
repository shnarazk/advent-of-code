lib ← •Import "../lib.bqn"

InjectBlock ← { beg‿end 𝕊 m:
  dx‿dy ← end-beg
  seq ← {
    0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy;
    0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy;
    0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx;
    0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
  }
  (1˙¨seq)⌾(seq⊸⊑) m
}´⟜(⥊⋈˘∘(2⊸↕))˜

Solve ⇐ { part 𝕊 data:
  seg ← lib.ParseInts¨ data
  "geometry" lib.Debug xmax‿ymax ← (2⊸+⌈´)¨(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈○(/⟜𝕩))´ 𝕨} ∾seg
  segments ← {(¬⋈⊢)○(2⊸|¨↕∘≠)⊸{(⋈¨○(/⟜𝕩))´ 𝕨} 𝕩}¨ seg
  {
    1=part ?
      map ← segments InjectBlock´˜ ymax‿xmax⥊ 0˙↕xmax×ymax
      lib.Debug "starting"
      sands‿trace ← 0‿⟨0‿500⟩
      DropSand1 ← { 𝕊 trace:
        y‿x ← start ← ¯1⊑trace
        falling ← 1
        lib.While { 𝕤, falling } ‿ { 𝕤,
          new_y ← 1+y
          {
            ymax=new_y ?
              map 1˙⌾(y‿x⊸⊑) ↩
              trace ↩ ⟨⟩
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
        trace
      }
      lib.While { 𝕤, 0<≠trace }‿{ 𝕤, trace DropSand1 ↩, sands 1⊸+ ↩ }
      ¯1+sands
    ;
      xmax ymax⊸+ ↩
      map ← segments InjectBlock´˜ ymax‿xmax⥊ 0˙↕xmax×ymax
      lib.Debug "starting"
      DropSand2 ← { y 𝕊 x:
        0=y‿x⊑map ?
          map 2˙⌾(y‿x⊸⊑) ↩
          { yy ← y, lib.While { 𝕤, ymax>yy ? 0=yy‿x⊑map; 0 }‿{ 𝕤, map 2˙⌾(yy‿x⊸⊑) ↩, yy 1⊸+ ↩ } }
          { ymax>yy ← 1+y ? yy 𝕊¨ x+⟨¯1,0,1⟩ ; @ }
        ;
          @
      }
      0 DropSand2 500
      +´2=⥊map
  }
}
