Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "region" util.Debug ymax‿xmax ← ⋈○(2⊸+)´⌈˝>∾segments ← ⌽¨¨<˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/util.ParseInts¨data
  {2=part ? xmax ymax⊸+ ↩ ; @}
  map ← ymax‿xmax⥊0˙↕xmax×ymax
  InjectBlocks ← {beg‿end :
    dy‿dx ← end-beg
    seq ← {
      0<dy ? ⋈⟜(1⊑beg)¨(0⊑beg)+↕1+|dy ;
      0>dy ? ⋈⟜(1⊑end)¨(0⊑end)+↕1+|dy ;
      0<dx ? (0⊑beg)⊸⋈¨(1⊑beg)+↕1+|dx ;
      0>dx ? (0⊑end)⊸⋈¨(1⊑end)+↕1+|dx
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
      floor ← 2+⌈´1⊸⊑¨∾segments
      map ↩ floor‿(2×xmax)↑map       # Expand region
      front ← 500=↕1⊑≢map
      ⊑1‿front{𝕨 𝕊 sands‿line : (sands++´)⊸⋈𝕨¬⊸∧⌈˝[«line,line,»line]}´⌽1↓⥊<˘map
  }
}
