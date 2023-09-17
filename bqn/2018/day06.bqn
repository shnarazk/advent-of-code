Solve ⇐ {env‿part 𝕊 data :
  util‿geo ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      min‿max ← (⌊´⋈⌈´) data util.ParseInts¨ ↩
      kind ← ≠data
      m ← 1⊑⟨1,∞¨↕max¬min⟩{d 𝕊 k‿m : ⟨1+k, k⌾((d-min)⊸⊑)m⟩}´data
      f ← {{∞=⊑𝕩 ? {⟨⟩ : ∞ ; ⟨a⟩ : a ; 𝕩 : 0}⍷∞⊸≠⊸/𝕩 ; ⊑𝕩}¨∞ geo.Neighbor5 𝕩}•_while_(∨´∞=⥊)m
      k ← ∧⍷(1‿¯1⊏⍉f)∾○⥊(1‿¯1⊏f)
      ⌈´(¬(∊⟜k⌾⋈)¨↕1+kind)⊸//⁼⥊f
      ;
    0
  }
}
