Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "data" util.Debug data ↩ >((¯1+¬×1++`)"contain"⊸≡¨)⊸⊔¨(" ,"⊸util.Tokenize ¯1⊸↓)¨ data
  Container ← {a‿b‿c : a∾"-"∾b}
  Containee ← {"no"‿"other"‿"bags" ≡ 𝕩 ? ⟨⟩ ; ⥊<∘{n‿a‿b‿c : (util.ParseInt n)⋈a∾"-"∾b}˘∘‿4⥊𝕩}
  "data" util.Debug 10↑data Container⊸⋈⟜Containee´˘ ↩
  {
    1=part ?
      0 ;
    0
  }
}
