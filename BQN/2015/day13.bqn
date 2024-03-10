Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿math ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/math.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  Parser ← {
    l ← " ." util.Split 𝕩
    ⟨⟨⊑l,10⊑l⟩,("gain"≡2⊑l)◶⟨-,⊢⟩util.ParseInt 3⊑l⟩
  }
  names ← ∧⍷∾⊑¨data Parser¨ ↩
  data {p‿c : ⟨names⊐p,c⟩}¨ ↩
  h ← Hashmap´<˘⍉>data
  ⌈´{+´(0⊸h.Get+0⊸h.Get∘⌽)˘2↕𝕩∾⟨⊑𝕩⟩}¨math.Permutations(2=part)◶⟨⊢,1⊸+⟩≠names
}
