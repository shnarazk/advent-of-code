Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ 1↓(+`util.startsWith⟜"mask"¨)⊸⊔data
  h ← Hashmap˜⟨⟩
  {
    1=part ?
      {
        ⟨mask⟩‿insts ← 1(↑⋈↓)𝕩
        mask ↩ ⌽-¬"X01"⊐7↓mask
        insts util.ParseInts¨ ↩
        !∧´(2⋆31)>∾insts
        {addr‿val : addr h.Set mask{¯1 𝕊 x : x ; w 𝕊 x : w}¨0‿0‿0‿0∾˜32‿1•bit._cast⋈val}¨insts
      }¨data
      +´{𝕨+2×𝕩}´¨h.Values@ ;
    Expand ← {⟨⟨⟩⟩{¯1=𝕨 ? ⥊⟨0⟩‿⟨1⟩∾⌜𝕩 ; ⥊⟨⟨𝕨⟩⟩∾⌜𝕩}´𝕩}
    # util.Debug Expand 1‿0‿1‿0
    # util.Debug Expand ¯1‿1‿¯1
    {
      ⟨mask⟩‿insts ← 1(↑⋈↓)𝕩
      mask ↩ ⌽-¬"X01"⊐7↓mask
      insts util.ParseInts¨ ↩
      {addr‿val : h.Set⟜val¨Expand mask{¯1 𝕊 x : ¯1 ; 0 𝕊 x : x ; 1 𝕊 x : 1}¨0‿0‿0‿0∾˜32‿1•bit._cast⋈addr}¨insts
    }¨data
    +´h.Values@
  }
}
