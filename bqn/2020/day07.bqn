Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ >((¯1+¬×1++`)"contain"⊸≡¨)⊸⊔¨(" ,"⊸util.Tokenize ¯1⊸↓)¨data
  Container ← {a‿b‿c : a∾"-"∾b}
  Containee ← {"no"‿"other"‿"bags" ≡ 𝕩 ? ⟨⟩ ; ⥊<∘{n‿a‿b‿c : (util.ParseInt n)⋈a∾"-"∾b}˘∘‿4⥊𝕩}
  dic ← ∧⍷⊑¨⥊<˘data Container⊸⋈⟜Containee´˘ ↩
  data (∧{c‿l : (dic⊸⊐⌾<c)⋈dic⊸⊐⌾(<1⊸⊑)¨l}˘) ↩
  start ← dic⊸⊐⌾<"shiny-gold"
  {1=part ? ≠{start=𝕩 ? 1 ; ∨´(𝕊 1⊸⊑)¨𝕩‿1⊑data}¨⊸/start⊸≠⊸/↕≠dic ; -¬{1++´×⟜𝕊´¨𝕩‿1⊑data}start}
}
