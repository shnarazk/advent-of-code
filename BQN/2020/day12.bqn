Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ 1(⊑∘↑⋈util.ParseInt∘↓)¨data
  {
    1=part ?
      +○|´1↓⟨'E',0,0⟩{
        'N'‿d 𝕊 dir‿y‿x : dir‿(y-d)‿x ;
        'S'‿d 𝕊 dir‿y‿x : dir‿(y+d)‿x ;
        'E'‿d 𝕊 dir‿y‿x : dir‿y‿(x+d) ;
        'W'‿d 𝕊 dir‿y‿x : dir‿y‿(x-d) ;
        'L'‿d 𝕊 dir‿y‿x : d ÷⟜¯90˜↩ ⋄ ("NESW"⊑˜4|d+<⁼"NESW"⊒dir)‿y‿x ;
        'R'‿d 𝕊 dir‿y‿x : d ÷⟜90˜↩ ⋄ ("NESW"⊑˜4|d+<⁼"NESW"⊒dir)‿y‿x ;
        'F'‿d 𝕊 dir‿y‿x : dir∾y‿x+d×(⊑⟜⟨¯1‿0,0‿1,1‿0,0‿¯1⟩)⊑"NESW"⊒dir
      }´⌽data ;
    2=part ?
      +○|´2↓⟨¯1,10,0,0⟩{
        'N'‿d 𝕊 y‿x‿sy‿sx : (y-d)‿x‿sy‿sx ;
        'S'‿d 𝕊 y‿x‿sy‿sx : (y+d)‿x‿sy‿sx ;
        'E'‿d 𝕊 y‿x‿sy‿sx : y‿(x+d)‿sy‿sx ;
        'W'‿d 𝕊 y‿x‿sy‿sx : y‿(x-d)‿sy‿sx ;
        'L'‿d 𝕊 y‿x‿sy‿sx : d ÷⟜¯90˜↩ ⋄ dy‿dx ← (4|d)◶⟨{⟨𝕨,𝕩⟩},{⟨𝕩,-𝕨⟩},{⟨-𝕨,-𝕩⟩},{⟨-𝕩,𝕨⟩}⟩´⟨y-sy,x-sx⟩⋄ (sy+dy)‿(sx+dx)‿sy‿sx ;
        'R'‿d 𝕊 y‿x‿sy‿sx : d ÷⟜ 90˜↩ ⋄ dy‿dx ← (4|d)◶⟨{⟨𝕨,𝕩⟩},{⟨𝕩,-𝕨⟩},{⟨-𝕨,-𝕩⟩},{⟨-𝕩,𝕨⟩}⟩´⟨y-sy,x-sx⟩⋄ (sy+dy)‿(sx+dx)‿sy‿sx ;
        'F'‿d 𝕊 y‿x‿sy‿sx : dy‿dx ← d×⟨y-sy,x-sx⟩⋄ ⟨y+dy,x+dx,sy+dy,sx+dx⟩
      }´⌽data ;
    0
  }
}
