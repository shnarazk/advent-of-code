Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data >∘(({a‿to‿b‿equals‿dist : a‿b‿dist}" ->"⊸util.Tokenize)¨) ↩
  cities ← ∧⍷⥊(0‿1⊸⊏)˘data
  h ← ((<·∧·{cities⊸⊐⌾⋈𝕩}¨0‿1⊸⊏)˘Hashmap(util.ParseInt 2⊸⊑)˘)data
  Permutation ← {
       𝕊 n : (↕n)𝕊⟨⟨⟩⟩ ;
    ⟨⟩ 𝕊 l : l ;
    cs P l : ∾{⟨𝕩⟩⊸∾¨((𝕩≠cs)⊸/cs)P l}¨cs
  }
  (2=part)◶⟨⌊,⌈⟩´{+´h.Get∘∧¨<˘2↕𝕩}¨⥊Permutation≠cities
}
