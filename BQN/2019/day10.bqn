Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ".#"⊸⊐⌾⋈¨∘> ↩
  asteroids ← (⊑⟜data)⊸/⥊↕≢data
  indexbest ← ⊑⍒⊑¨map←{𝕊 pos :
    h ← Hashset⟨⟩
    h.Set∘(÷⟜(•math.GCD○|´))¨pos<⊸-asteroids
    h⋈˜h.Count@
  }¨asteroids
  root ← indexbest⊑asteroids
  {
    1=part ? 1-˜(1⊑indexbest⊑map).Count@ ;
    Degree ← {
      ¯1‿ 1≡×𝕩 ? ⟨(0)-•math.Atan÷˜´𝕩,⟨+○|´𝕩,𝕩⟩⟩ ;
       1‿ 1≡×𝕩 ? ⟨π-•math.Atan÷˜´𝕩,⟨+○|´𝕩,𝕩⟩⟩ ;
      ¯1‿¯1≡×𝕩 ? ⟨(2×π)-•math.Atan÷˜´𝕩,⟨+○|´𝕩,𝕩⟩⟩ ;
       1‿¯1≡×𝕩 ? ⟨π-•math.Atan÷˜´𝕩,⟨+○|´𝕩,𝕩⟩⟩ ;
       1‿ 0≡×𝕩 ? ⟨π,⟨+○|´𝕩,𝕩⟩⟩ ;
       0‿ 1≡×𝕩 ? ⟨0.5×π,⟨+○|´𝕩,𝕩⟩⟩ ;
      ¯1‿ 0≡×𝕩 ? ⟨0,⟨+○|´𝕩,𝕩⟩⟩ ;
       0‿¯1≡×𝕩 ? ⟨1.5×π,⟨+○|´𝕩,𝕩⟩⟩ ;
       !0
    }
    # util.Debug >⋈⟜Degree¨⟨
    #   ¯1‿0,¯2‿0,¯0.8‿0.2,¯0.5‿0.5
    #   0‿1,0.2‿0.8,0.4‿0.6,0.99‿0.1,
    #   1‿0,0.7‿¯0.7,0.1‿¯0.8,
    #   0‿¯1,¯0.2‿¯0.7,¯0.5‿¯0.2,¯0.8‿¯0.1,¯0.999‿(¯1÷100)
    # ⟩
    h ← hashmap˜⟨⟩
    {𝕨 h.Set∧⟨𝕩⟩∾⟨⟩h.Get 𝕨}´¨Degree¨0‿0⊸≢¨⊸/asteroids-<root
    list ← (1⊸⊑)¨∧h.Values⁼˜@
    (+⟜(100⊸×))´root+1⊑2⊑{count‿index‿value :
      {
        index=≠list ? count‿0‿value ;
        ⟨⟩≡index⊑list ? count‿(1+index)‿value ;
        ⟨element⟩‿rest ← 1(↑⋈↓)index⊑list
        list rest⌾(index⊸⊑) ↩
        ⟨1+count,1+index,element⟩
      }
    }•_while_(200>⊑)0‿0‿0
  }
}
