Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  connect ← Hashset data (∾((⊑∾¨(1⊸↓))util.ParseInts)¨) ↩
  Linked ← {
    𝕊 a‿b : a 𝕊 b ;
    𝕨≡𝕩 ? 1 ;
    ¬connect.Has 𝕨‿𝕩 ? connect.Has 𝕩‿𝕨 ; 1
  }
  unused ← Hashset↕1+⌈´∾⥊data
  Group ← {𝕊 unused :
    g ← Hashset⊏k ← unused.Values⁼@
    {g.Set¨𝕩 ⍷∘∾∘({(𝕩⊸Linked∧¬∘g.Has)¨⊸/k}¨) ↩ ⋄ 𝕩}•_while_(⟨⟩⊸≢)⊏k
    g
  }
  {
    1=part ? (Group unused).Count@ ;
    {unused.Delete¨(Group unused).Values⁼@ ⋄ 1+𝕩}•_while_{𝕤 ⋄ 0<unused.Count@}0
  }
}
