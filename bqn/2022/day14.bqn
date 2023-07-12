lib ← •Import "../lib.bqn"

Solve ⇐ { part 𝕊 data:
  "region" lib.Debug xmax‿ymax ← ⋈○(2⊸+)´⌈˝>∾segments ← <˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/lib.ParseInts¨data
  {
    1=part ?
      map ← ymax‿xmax⥊ 0˙↕xmax×ymax
      InjectBlocks ← {𝕊 beg‿end :
        dx‿dy ← end-beg
        seq ← {
          0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy ;
          0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy ;
          0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx ;
          0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
        }
        map (1˙¨seq)⌾(seq⊸⊑) ↩
        ⟨⟩
      }¨<˘∘(2⊸↕)
      InjectBlocks¨segments
      DropSand1 ← {𝕊 tr :
        1⊑{𝕊 falling‿tr :
          loc ← ¯1⊑tr
          {
            ymax=1+⊑loc                  ? map 1˙⌾(loc⊸⊑) ↩ ⋄ 0‿⟨⟩ ;
            ((loc+offset ← 1‿ 0)(¬⊑)map) ? 1⋈tr∾⟨loc+offset⟩ ;
            ((loc+offset ← 1‿¯1)(¬⊑)map) ? 1⋈tr∾⟨loc+offset⟩ ;
            ((loc+offset ← 1‿ 1)(¬⊑)map) ? 1⋈tr∾⟨loc+offset⟩ ;
                                           map 1˙⌾(loc⊸⊑) ↩ ⋄ ⟨0,¯1↓tr⟩
          }
        }•_while_⊑1‿tr
      }
      ¯1+⊑{𝕊 sands‿trace : ⟨1+sands,DropSand1 trace⟩}•_while_{⟨⟩⊸≢1⊑𝕩}0‿⟨0‿500⟩
    ;
      xmax ymax⊸+ ↩
      map ← ymax‿xmax⥊ 0˙↕xmax×ymax
      InjectBlocks ← { 𝕊 beg‿end:
        dx‿dy ← end-beg
        seq ← {
          0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy ;
          0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy ;
          0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx ;
          0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
        }
        map (1˙¨seq)⌾(seq⊸⊑) ↩
        ⟨⟩
      }¨<˘∘(2⊸↕)
      InjectBlocks¨segments
      0{y Drop x : 0=y‿x⊑map ? map 2˙⌾(y‿x⊸⊑) ↩ ⋄ {ymax>yy ← 1+y ? yy Drop¨ x+⟨¯1,0,1⟩ ; @} ; @}500
      +´2=⥊map
  }
}
