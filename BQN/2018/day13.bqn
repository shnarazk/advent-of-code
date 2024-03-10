Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  dir ← ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
  symbol ← " /-\|+^<>v"
  # util.Debug >⟨⟩⊸≢¨⊸/data
  data (>⟨⟩⊸≢¨⊸/) ↩
  data symbol⊸⊐⌾⋈¨ ↩
  Clash ← ≠○≠⟜⍷⊑¨
  Display ← {𝕨 util.Debug ⊑⟜symbol¨data{pos‿or‿n 𝕊 map : or⌾(pos⊸⊑)map}´𝕩 ⋄ 𝕩}
  {
    1=part ?
      Next ← {
        x ← (0=𝕨)◶⟨⊢,∧⟩𝕩 # x ≢ pos‿orientation‿number_of_turns
        "# 𝕨" util.Debug pos‿orientation‿turns ← 𝕨⊑x
        "# newpos" util.Debug newpos ← pos+ d ← ⊑⟜dir os ← orientation-6
        os ↩ {
           0 : os ;
           1 : "# turn"⊸util.Debug⊑⟜⟨2,3,0,1⟩os ; # / ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
           2 : os ;
           3 : "# turn"⊸util.Debug⊑⟜⟨1,0,3,2⟩os ; # \ ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
           4 : os ;
           5 : "# cross"⊸util.Debug (turns (3|1⊸+) ↩)⊸⊑⊑⟜⟨⟨2,1,0⟩,⟨0,3,1⟩,⟨3,0,2⟩,⟨1,2,3⟩⟩os ;      # up,left,right,down≍left,straight,right
           𝕩 : os
        }newpos⊑data
        "# next" util.Debug ⟨newpos,6+os,turns⟩⌾(𝕨⊸⊑)x
        # 𝕨 Display ⟨newpos,6+os,turns⟩⌾(𝕨⊸⊑)x
      }
      n ← ≠ carts ← ∧∾{(⋈∾⟨𝕩,0⟩˙)¨(𝕩=⊑⟜data)¨⊸/⥊↕≢data}¨6+↕4
      ⌽⊑⊑≡´¨⊸/<˘2↕∧⊑¨⊑{c‿i : ⟨i Next c,n|i+1⟩}•_while_(¬∘Clash ⊑)carts‿0
    ;
      k ← 0
      Next ← {
        {20=k ? •Exit 0 ; @}
        w ← (≠𝕩)⊸|𝕨
        x ← 𝕩 # x ≢ pos‿orientation‿number_of_turns
        {0=𝕨 ? x ↩ ∧∞⊸≢¨⊸/x ; @}
        {
          ∞≡w⊑x ? x ;
          pos‿orientation‿turns ← w⊑x
          newpos ← pos+ d ← ⊑⟜dir os ← orientation-6
          os ↩ {
             0 : os ;
             1 : "# turn"⊸util.Debug⊑⟜⟨2,3,0,1⟩os ; # / ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
             2 : os ;
             3 : "# turn"⊸util.Debug⊑⟜⟨1,0,3,2⟩os ; # \ ⟨¯1‿0,0‿¯1,0‿1,1‿0⟩
             4 : os ;
             5 : "# cross"⊸util.Debug (turns (3|1⊸+) ↩)⊸⊑⊑⟜⟨⟨2,1,0⟩,⟨0,3,1⟩,⟨3,0,2⟩,⟨1,2,3⟩⟩os ;
             𝕩 : os
          }newpos⊑data
          next ← ⟨newpos,6+os,turns⟩⌾(w⊸⊑)x
          clashes ← ⊑¨≡´¨⊸/⥊<˘2↕∧⊑¨next
          clashlist ← (∊⟜clashes⌾⋈⊑)¨next
          util.Progress ≠∞⊸≢¨⊸/next
          clashlist{0 𝕊 𝕩 : 𝕩 ; 1 𝕊 𝕩 : ∞}¨next
        }
      }
      carts ← ∧∾{(⋈∾⟨𝕩,0⟩˙)¨(𝕩=⊑⟜data)¨⊸/⥊↕≢data}¨6+↕4
      ⌽⊑⊑∞⊸≢¨⊸/⊑{c‿i : ⟨i Next c,i+1⟩}•_while_(1<(+´·∞⊸≢¨⊑))carts‿0

  }
}
