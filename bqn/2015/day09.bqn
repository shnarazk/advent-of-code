Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿math ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/math.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data >∘(({a‿to‿b‿equals‿dist : a‿b‿dist}" ->"⊸util.Tokenize)¨) ↩
  cities ← ∧⍷⥊(0‿1⊸⊏)˘data
  h ← ((<·∧·{cities⊸⊐⌾⋈𝕩}¨0‿1⊸⊏)˘Hashmap(util.ParseInt 2⊸⊑)˘)data
  (2=part)◶⟨⌊,⌈⟩´{+´h.Get∘∧¨<˘2↕𝕩}¨⥊math.Permutations≠cities
}
