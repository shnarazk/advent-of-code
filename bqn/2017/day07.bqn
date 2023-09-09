Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (" ->,"⊸util.Tokenize)¨ ↩
  parent ← Hashmap˜⟨⟩
  subnodes ← Hashmap˜⟨⟩
  weight ← Hashmap˜⟨⟩
  treeweight ← Hashmap˜⟨⟩
  {⟨node,weight⟩‿nodes ← 2(↑⋈↓)𝕩 ⋄ parent.Set⟜node¨nodes}¨data
  root ← parent.Get•_while_(parent.Has)¯1⊑parent.Values⁼@
  {
    1=part ? root ;
    {⟨node,w⟩‿nodes ← 2(↑⋈↓)𝕩 ⋄ node weight.Set util.ParseInt w ⋄ node subnodes.Set nodes}¨data
    SetTreeWeight ← {𝕩 treeweight.Set w ← (weight.Get 𝕩) + +´𝕊¨subnodes.Get 𝕩 ⋄ w}
    SetTreeWeight root
    Check ← {
      uws ← ⍷ws ← treeweight.Get¨nodes ← subnodes.Get 𝕩
      {1≥≠uws ? ∾Check¨nodes ;
        util.Debug nodes⋈ws
        util.Debug uws
        "wrong weight index" util.Debug target ← 1<+´(⊑uws)=ws
        "diff" util.Debug counterweight ← target◶⟨-,⊢⟩-´uws
        "node index" util.Debug i ← (ws⊸⊐)⌾⋈target⊑uws
        "mal weight" util.Debug i⊑ws
        "its name" util.Debug reason ← i⊑nodes
        r ← Check reason
        { r≢⟨⟩ ? r ;
          "its weight" util.Debug weight.Get i⊑nodes
          "and its subweights" util.Debug treeweight.Get¨subnodes.Get i⊑nodes
          ⟨counterweight+weight.Get i⊑nodes⟩
        }
      }
    }
    Check root
  }
}
