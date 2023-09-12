Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  h ← Hashmap˜⟨⟩
  data (∧(⋈⟜(2⊸↑util.Tokenize)´·"[]"⊸util.Tokenize '-'⊸=◶⟨⊢,' '⟩¨)¨) ↩
  record ← 1↓(+`("Guard"≡(⊑1⊸⊑))¨)⊸⊔ data
  r ← {⟨{(0=𝕨)◶⟨⊢,60⊸+⟩𝕩}´3↓util.ParseInts 𝕨,⟨⊑𝕩⟩∾util.ParseInts 1⊑𝕩⟩}´¨¨record
  {
    v ← (120↑0) h.Get id ← 1⊑1⊑⊑𝕩
    {v ↩ v+𝕨⌽⁼120↑1+(𝕩-𝕨)↑0}○⊑´˘∘‿2⥊1↓𝕩
    id h.Set v
  }¨r
  Prop ← (2=part)◶⟨+´1⊸⊑,⌈´1⊸⊑⟩
  {a‿(b‿c) : b×60-˜⊑⍒c}⊑∨(Prop⊸⋈)¨h.Values⁼˜@
}
