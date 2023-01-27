lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 data:
  "region" lib.Debug xmax‿ymax ← ⋈○(2⊸+)´⌈˝>∾segments ← <˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/ lib.ParseInts¨ data
  {
    1=part ?
      map ← ymax‿xmax⥊ 0˙↕xmax×ymax
      InjectBlocks ← { 𝕊 beg‿end:
        dx‿dy ← end-beg
        seq ← {
          0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy;
          0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy;
          0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx;
          0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
        }
        map (1˙¨seq)⌾(seq⊸⊑) ↩
        ⟨⟩
      }¨<˘∘(2⊸↕)
      InjectBlocks¨ segments
      lib.Debug "starting"
      sands‿trace ← 0‿⟨0‿500⟩
      DropSand1 ← { 𝕊 tr:
        y‿x ← start ← ¯1⊑tr
        falling ← 1
        lib.While { 𝕤, falling } ‿ { 𝕤,
          new_y ← 1+y
          {
            ymax=new_y ?
              map 1˙⌾(y‿x⊸⊑) ↩
              tr ↩ ⟨⟩
              falling ↩ 0
              ;
            (new_y‿x (¬⊑) map) ?
              y ↩ new_y
              tr ∾⟜⟨y‿x⟩ ↩
              ;
            (new_y‿(¯1+x) (¬⊑) map) ?
              y‿x ↩ new_y‿(¯1+x)
              tr ∾⟜⟨y‿x⟩ ↩
              ;
            (new_y‿( 1+x) (¬⊑) map) ?
              y‿x ↩ new_y‿( 1+x)
              tr ∾⟜⟨y‿x⟩ ↩
            ;
              map 1˙⌾(y‿x⊸⊑) ↩,
              tr ¯1⊸↓ ↩
              falling ↩ 0
          }
        }
        tr
      }
      While ← {𝕨{𝕊∘𝔾⍟𝔽𝕩}𝕩@}´
      # While ← {𝕩{𝔽⍟𝔾∘𝔽_𝕣_𝔾∘𝔽⍟𝔾𝕩}𝕨@}´
      # While ← {𝕩{𝔽⍟𝔾∘𝔽_𝕣_𝔾∘𝔽⍟𝔾𝕩}𝕨@}´
      # While ← {𝕩{𝔽_𝕣_𝔾∘𝔽⍟𝔾𝕩}𝕨@}´
      While { 𝕤, trace DropSand1 ↩, ⟨⟩≢trace }‿{ 𝕤, sands 1⊸+ ↩ }
      # lib.While { 𝕤, 0<≠trace }‿{ 𝕤, trace DropSand1 ↩, sands 1⊸+ ↩ }
      sands
    ;
      xmax ymax⊸+ ↩
      map ← ymax‿xmax⥊ 0˙↕xmax×ymax
      InjectBlocks ← { 𝕊 beg‿end:
        dx‿dy ← end-beg
        seq ← {
          0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy;
          0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy;
          0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx;
          0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
        }
        map (1˙¨seq)⌾(seq⊸⊑) ↩
        ⟨⟩
      }¨<˘∘(2⊸↕)
      InjectBlocks¨ segments
      lib.Debug "starting"
      DropSand2 ← { y 𝕊 x:
        0=y‿x⊑map ?
          map 2˙⌾(y‿x⊸⊑) ↩
          # { yy ← y, lib.While { 𝕤, ymax>yy ? 0=yy‿x⊑map; 0 }‿{ 𝕤, map 2˙⌾(yy‿x⊸⊑) ↩, yy 1⊸+ ↩ } }
          { ymax>yy ← 1+y ? yy DropSand2¨ x+⟨¯1,0,1⟩ ; @ }
        ;
          @
      }
      0 DropSand2 500
      +´2=⥊map
  }
}
