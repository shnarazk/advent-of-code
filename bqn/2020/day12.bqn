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
    0
  }
}
