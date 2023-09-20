Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (" ->,"⊸util.Split)¨ ↩
  parent ← Hashmap˜⟨⟩
  {⟨node,weight⟩‿nodes ← 2(↑⋈↓)𝕩 ⋄ parent.Set⟜node¨nodes}¨data
  root ← parent.Get•_while_(parent.Has)¯1⊑parent.Values⁼@
  {
    1=part ? root ;
    subnodes ← Hashmap˜⟨⟩
    weight ← Hashmap˜⟨⟩
    treeweight ← Hashmap˜⟨⟩
    {⟨node,w⟩‿nodes ← 2(↑⋈↓)𝕩 ⋄ node weight.Set util.ParseInt w ⋄ node subnodes.Set nodes}¨data
    {𝕩 treeweight.Set w ← (weight.Get 𝕩)++´𝕊¨subnodes.Get 𝕩 ⋄ w}root
    Check ← {
      uws ← ⍷ ws ← treeweight.Get¨ nodes ← subnodes.Get 𝕩
      {
        1≥≠uws ? ∾Check¨nodes ;
        "# wrong weight index" util.Debug target ← 1<+´(⊑uws)=ws
        "# node index" util.Debug i ← (ws⊸⊐)⌾⋈target⊑uws
        {⟨⟩≢r ← Check i⊑nodes ? r ; ⟨(target◶⟨-,⊢⟩-´uws)+weight.Get i⊑nodes⟩}
      }
    }
    ⊑Check root
  }
}
