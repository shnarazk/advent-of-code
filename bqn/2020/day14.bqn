Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ 1↓(+`util.startsWith⟜"mask"¨)⊸⊔data
  {
    1=part ?
      h ← Hashmap˜⟨⟩
      {
        ⟨mask⟩‿insts ← 1(↑⋈↓)𝕩
        mask ↩ ⌽-¬"X01"⊐7↓mask
        insts util.ParseInts¨ ↩
        !∧´(2⋆31)>∾insts
        {addr‿val : addr h.Set mask{¯1 𝕊 x : x ; w 𝕊 x : w}¨0‿0‿0‿0∾˜32‿1•bit._cast⋈val}¨insts
      }¨data
      +´{𝕨+2×𝕩}´¨h.Values@ ;
    0
  }
}
