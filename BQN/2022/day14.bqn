Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ymax‿xmax ← 2+⌈˝>∾segments ← <∘⌽˘¨∘‿2⊸⥊¨⟨⟩⊸≢¨⊸/util.ParseInts¨data
  {2=part ? xmax ymax⊸+ ↩ ; @}
  map ← ⟨ymax,xmax⌈500+ymax⟩↑0
  {seq ← ⋈⌜´((<∘↕·(1⊸+)-)+⊢)´˘∨˘⍉>𝕩 ⋄ map 1¨⌾(seq⊸⊑) ↩ }¨∘<˘∘(2⊸↕)¨segments
  {
    1=part ?
      map (shift ← ¯2+ymax)⊸↓˘ ↩
      DropSand ← {
        ymax=1+⊑𝕨 ? map 1⌾(𝕨⊸⊑) ↩ ⋄ 0‿⟨⟩ ;
        ⟨⟩≢p ← map⊸(¬⊑˜)¨⊸/𝕨<⊸+⟨1‿0,1‿¯1,1‿1⟩ ? 1⋈𝕩∾1↑p ;
        map 1⌾(𝕨⊸⊑) ↩ ⋄ ⟨0,¯1↓𝕩⟩
      }´∘((⊑¯1⊸↑)⊸⋈)∘(1⊸⊑)•_while_⊑1⊸⋈
      ¯1+⊑{sands‿trace : ⟨1+sands,1⊑DropSand trace⟩}•_while_{⟨⟩⊸≢1⊑𝕩}0‿⟨⟨0,500-shift⟩⟩ ;
    front ← (500-shift)=↕1⊑≢map ↩ (shift ← 500-floor)⊸↓˘(floor ← 2+⌈´⊑¨∾segments)‿(2×xmax)↑map
    ⊑1‿front{𝕨 𝕊 sands‿line : (sands++´)⊸⋈𝕨¬⊸∧⌈˝[«line,line,»line]}´⌽1↓⥊<˘map
  }
}
