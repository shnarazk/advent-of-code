Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  nodes ← ∧⍷∾data ")"⊸util.Split¨ ↩
  data nodes⊸⊐⌾⋈¨¨ ↩
  parent ← Hashmap´<˘⍉>⌽¨data
  children ← ↕∘≠⊸Hashmap 1⊸⊑¨¨⊑¨⊸⊔ data
  root ← ⊑(¬∊⟜(parent.Values⁼@))⊸/children.Values⁼@
  {
    1=part ? 0{𝕨++´(𝕨+1)⊸𝕊¨⟨⟩ children.Get 𝕩}root ;
    Path ← {∾˜⟜(parent.Get∘⊑)•_while_(parent.Has⊑)⟨𝕩⟩}
    len ← ⌊○≠´to_you‿to_san ← ¯1⊸↓¨(Path nodes⊸⊒⌾⋈)¨"YOU"‿"SAN"
    common ← +´∧`to_you=○(len⊸↑)to_san
    +○(≠-common˙)´to_you‿to_san
  }
}
