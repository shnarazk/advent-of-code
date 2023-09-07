Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿math ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/math.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Parser ← {
    l ← " ." util.Tokenize 𝕩
    ⟨⟨⊑l,10⊑l⟩,("gain"≡2⊑l)◶⟨-,⊢⟩util.ParseInt 3⊑l⟩
  }
  data Parser¨ ↩
  names ← ∧⍷∾⊑¨data
  data {p‿c : ⟨names⊐p,c⟩}¨ ↩
  h ← Hashmap´<˘⍉>data
  {
    1=part ? ⌈´{+´(h.Get+h.Get∘⌽)˘2↕𝕩∾⟨⊑𝕩⟩}¨math.Permutations≠names ;
    ⌈´{+´(0⊸h.Get+0⊸h.Get∘⌽)˘2↕𝕩∾⟨⊑𝕩⟩}¨math.Permutations 1+≠names
  }
}
