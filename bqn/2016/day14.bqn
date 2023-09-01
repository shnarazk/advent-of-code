Solve ⇐ {env‿part 𝕊 data :
  ⟨hashmap⟩‿⟨md5⟩ ← •Import¨"/hashmap.bqn"‿"/md5.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  salt‿h3‿found‿repeat ← ⟨⊑data,Hashmap˜⟨⟩,⟨⟩,1+2016×2=part⟩
  63⊑∧⊑{found‿n :
    hash ← Md5⍟repeat salt∾•Fmt n
    {found ((n-1000)⊸≤⊸/⟨⟩h3.Get 𝕩)⊸∾ ↩}∘⊑¨⍷(1=≠∘⍷)¨⊸/⥊<˘5↕hash
    {𝕩 h3.Set n∾⟨⟩ h3.Get 𝕩}∘⊑¨⟨⟩⊸≢◶⟨⟨⟩,⊏⟩(1=≠∘⍷)¨⊸/⥊<˘3↕hash
    found⋈1+n
  }•_while_(64>≠∘⊑)⟨⟩‿0
}
