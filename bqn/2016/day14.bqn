Solve ⇐ {env‿part 𝕊 salt :
  util‿⟨hashmap⟩‿⟨md5⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/md5.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  salt ⊑ ↩
  {
    1=part ?
      h3 ← Hashmap˜⟨⟩
      found ← ⟨⟩
      -{𝕊 n :
        hash ← Md5 salt∾(•Fmt n)
        {⟨⟩≢t←(n-1000)⊸≤⊸/⟨⟩h3.Get 𝕩 ? found t⊸∾ ↩ ; @}∘⊑¨p5 ← ⍷(1=≠∘⍷)¨⊸/⥊<˘5↕hash
        {𝕩 h3.Set n∾⟨⟩ h3.Get 𝕩}∘⊑¨⟨⟩⊸≢◶⟨⟨⟩,⊏⟩(1=≠∘⍷)¨⊸/⥊<˘3↕hash
        {64≤≠found ? -63⊑∧found ; 1+n}
      }•_while_(0⊸≤)0
      ;
    0
  }
}
