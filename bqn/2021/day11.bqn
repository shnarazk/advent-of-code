Solve ⇐ {env‿part 𝕊 data :
  util‿geometric ← •Import¨"/util.bqn"‿"/geometric.bqn"∾˜¨<"," env.Var⌾⋈ "BQN_LIB"
  data (-⟜'0')¨∘⍉∘> ↩
  flash ← 10
  Step ← {step‿num_flashes‿map :
    m ← {𝕩{(flash>𝕨)∧(1≤𝕩)∧(10<𝕨+𝕩) ? 10 ; 𝕨+𝕩}¨(+´1⊸=¨)¨geometric.Gather9 flash⊸=¨𝕩}•_while_(∨´·⥊flash⊸=¨)1+map
    ⟨1+step,num_flashes+(+´(flash⊸≤)¨⥊m),(flash⊸>⊸×)¨m⟩
  }
  {1=part ? 1⊑Step•_while_(100>⊑)0‿0‿data ; ⊑Step•_while_(∨´0≠(⥊2⊸⊑))0‿0‿data}
}
