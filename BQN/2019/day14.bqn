Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (¯2⊸((↓⋈↑))·(util.ParseInts⊸{⟨⟩≡𝕨 ? 𝕩 ; ⊑𝕨}¨)(" ,=>"⊸util.Split))¨ ↩
  h ← Hashmap˜⟨⟩
  3↑{list 𝕊 amount‿target : target h.Set amount⋈list}´¨data
  ht ← Hashmap˜⟨⟩
  RankTree ← {𝕨 𝕊 𝕩:
    𝕩 ht.Set 𝕨⌈¯∞ ht.Get 𝕩
    "ORE"≢𝕩 ? (1+𝕨)𝕊¨1⊏⍉∘‿2⥊1⊑h.Get 𝕩 ; @
  }
  0 RankTree "FUEL"
  "# dependency tree" util.Debug tree ← ⍉≍⊔´<˘⍉>⌽¨ht.Values⁼˜@
  Need ← {
    requires ← "FUEL" Hashmap○⋈ 𝕩
    {𝕊 node :
      req ← requires.Get node
      am‿ingredients ← h.Get 𝕩
      set ← ⌈req÷am
      {𝕩 requires.Set(set×𝕨)+0 requires.Get 𝕩}´˘∘‿2⥊ingredients
    }¨¨¯1↓tree
    requires.Get "ORE"
  }
  {
    1=part ? Need 1 ;
    resource ← 1000000000000
    ⊑{(resource<Need)◶⟨∾⟜𝕩,𝕨⊸∾⟩2⌊∘÷˜𝕨+𝕩}´•_while_(1<-˜´)0‿resource
  }
}
