Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  nodes ← ∧⍷∾data ")"⊸util.Tokenize¨ ↩
  data (nodes⊸⊐⌾⋈)¨¨ ↩
  parent ← Hashmap´<˘⍉>⌽¨data
  children ← ↕∘≠⊸Hashmap 1⊸⊑¨¨⊑¨⊸⊔ data
  root ← ⊑(¬(∊⟜(parent.Values⁼@)))⊸/children.Values⁼@
  {
    1=part ? 0{c 𝕊 n : c++´(c+1)⊸𝕊¨⟨⟩ children.Get n}root ;
    Path ← {∾˜⟜(parent.Get∘⊑)•_while_(parent.Has⊑)⟨𝕩⟩}
    l ← ⌊○≠´to_you‿to_san ← ¯1⊸↓¨(Path nodes⊸⊒⌾⋈)¨"YOU"‿"SAN"
    common ← +´∧`to_you=○(l⊸↑)to_san
    +○(≠-common˙)´to_you‿to_san
  }
}
