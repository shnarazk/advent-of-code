Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "region" lib.Debug xmax‿ymax ← ⋈○(2⊸+)´⌈˝>∾segments ← <˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/lib.ParseInts¨data
  {2=part ? xmax ymax⊸+ ↩ ; @}
  map ← ymax‿xmax⥊0˙↕xmax×ymax
  InjectBlocks ← {beg‿end :
    dx‿dy ← end-beg
    seq ← {
      0<dy ? ⋈⟜(0⊑beg)¨(1⊑beg)+↕1+|dy ;
      0>dy ? ⋈⟜(0⊑end)¨(1⊑end)+↕1+|dy ;
      0<dx ? (1⊑beg)⊸⋈¨(0⊑beg)+↕1+|dx ;
      0>dx ? (1⊑end)⊸⋈¨(0⊑end)+↕1+|dx
    }
    map 1¨⌾(seq⊸⊑) ↩
  }¨<˘∘(2⊸↕)
  InjectBlocks¨segments
  {
    1=part ?
      DropSand ← {
        1⊑{falling‿tr :
          loc ← ¯1⊑tr
          {
            ymax=1+⊑loc                ? map 1˙⌾(loc⊸⊑) ↩ ⋄ 0‿⟨⟩ ;
            (newloc ← loc+1‿ 0)(¬⊑)map ? 1⋈tr∾⟨newloc⟩ ;
            (newloc ← loc+1‿¯1)(¬⊑)map ? 1⋈tr∾⟨newloc⟩ ;
            (newloc ← loc+1‿ 1)(¬⊑)map ? 1⋈tr∾⟨newloc⟩ ;
                                         map 1˙⌾(loc⊸⊑) ↩ ⋄ ⟨0,¯1↓tr⟩
          }
        }•_while_⊑1‿𝕩
      }
      ¯1+⊑{sands‿trace : ⟨1+sands,DropSand trace⟩}•_while_{⟨⟩⊸≢1⊑𝕩}0‿⟨0‿500⟩
    ;
      0{y Drop x : 0=y‿x⊑map ? map 2˙⌾(y‿x⊸⊑) ↩ ⋄ {ymax>yy ← 1+y ? yy Drop¨ x+⟨¯1,0,1⟩ ; @} ; @}500
      +´2=⥊map
  }
}
