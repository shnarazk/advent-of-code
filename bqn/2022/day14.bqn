Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "region" util.Debug xmax‿ymax ← ⋈○(2⊸+)´⌈˝>∾segments ← <˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/util.ParseInts¨data
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
      floor ← 2+⌈´1⊸⊑¨∾segments
      map ↩ (1+floor)‿(2×xmax)↑map       # Expand region
      map ↩ 1¨⌾(¯1⊸⊏)map            # Fill the bottom line as sentinel
      BottomIndices ← {y‿x 𝕊 down: (y+down)∾¨down-˜x+↕1+2×down} # ⋄ ! 8‿¯1≡⊑5‿2 BottomIndices 3
      # "map" util.Debug ≢map
      # "indices" util.Debug 0‿500 BottomIndices 5
      FlatBottom ← ∧´0=(⊑⟜map)¨    # ⋄ ! 0‿500 FlatBottom∘BottomIndices 5
      {S to_visit :
        ⟨start⟩‿remain ← 1(↑⋈↓)to_visit
        {𝕊 𝕩:
          floor≤𝕩+⊑start ? remain ;
          l ← start BottomIndices down ← 𝕩
          {FlatBottom l ? map 2¨⌾(l⊸⊑) ↩ ⋄ 1+down ; 0<down ? remain∾˜(0=⊑⟜map)¨⊸/¯1⌽l ; remain}
        }•_while_(1=•Type)0
      }•_while_(⟨⟩⊸≢)⟨0‿500⟩
      # "map" util.Debug ".#○"⊸(⊑˜)¨(40⊸↑480⊸↓)˘map
      +´2=⥊map
  }
}
