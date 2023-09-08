Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  h ← Hashmap˜⟨⟩
  Distribute ← {𝕊 state :
    state h.Set 1+h.Count@
    t ← (target ← ⊑⍒state)⊑state
    state 0⌾(target⊸⊑) ↩
    state (d ← t⌊∘÷16)⊸+ ↩
    {state 1⊸+⌾(𝕩⊸⊑) ↩}¨16|target+1+↕t-16×d
    state
  }
  loop ← Distribute•_while_(¬h.Has)data
  {1=part ? h.Count@ ; (h.Count@)¬h.Get loop}
}
