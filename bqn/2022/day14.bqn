Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ymax‿xmax ← ⋈○(2⊸+)´⌈˝>∾segments ← ⌽¨¨<˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/util.ParseInts¨data
  {2=part ? xmax ymax⊸+ ↩ ; @}
  map ← ⟨ymax,xmax⌈500+ymax⟩↑0
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
      map (shift ← ¯2+ymax)⊸↓˘ ↩
      DropSand ← {
        ymax=1+⊑𝕨 ? map 1⌾(𝕨⊸⊑) ↩ ⋄ 0‿⟨⟩ ;
        ⟨⟩≢p ← map⊸(¬⊑˜)¨⊸/𝕨<⊸+⟨1‿0,1‿¯1,1‿1⟩ ? 1⋈𝕩∾1↑p ;
        map 1⌾(𝕨⊸⊑) ↩ ⋄ ⟨0,¯1↓𝕩⟩
      }´∘((⊑¯1⊸↑)⊸⋈)∘(1⊸⊑)•_while_⊑1⊸⋈
      ¯1+⊑{sands‿trace : ⟨1+sands,1⊑DropSand trace⟩}•_while_{⟨⟩⊸≢1⊑𝕩}0‿⟨⟨0,500-shift⟩⟩
    ;
      shift ← 500-floor ← 2+⌈´⊑¨∾segments
      map ↩ shift⊸↓˘floor‿(2×xmax)↑map
      front ← (500-shift)=↕1⊑≢map
      ⊑1‿front{𝕨 𝕊 sands‿line : (sands++´)⊸⋈𝕨¬⊸∧⌈˝[«line,line,»line]}´⌽1↓⥊<˘map
  }
}
