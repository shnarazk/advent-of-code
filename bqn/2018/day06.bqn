Solve ⇐ {env‿part 𝕊 data :
  util‿geo‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/geometry.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  min‿max ← (⌊´⋈⌈´) data util.ParseInts¨ ↩
  kind ← ≠data
  {
    1=part ?
      m ← 1⊑⟨1,∞¨↕max¬min⟩{d 𝕊 k‿m : ⟨1+k, k⌾((d-min)⊸⊑)m⟩}´data
      f ← {{∞=⊑𝕩 ? {⟨⟩ : ∞ ; ⟨a⟩ : a ; 𝕩 : 0}⍷∞⊸≠⊸/𝕩 ; ⊑𝕩}¨∞ geo.Neighbor5 𝕩}•_while_(∨´∞=⥊)m
      k ← ∧⍷(1‿¯1⊏⍉f)∾○⥊(1‿¯1⊏f)
      ⌈´(¬(∊⟜k⌾⋈)¨↕1+kind)⊸//⁼⥊f
      ;
    limit ← 10000
    Within ← {limit>+´(+○|´-⟜𝕩)¨data}
    !Within cand ← ⌊50÷˜+´data
    visited ← cand Hashmap○⋈ 1
    {𝕊 cands :
      ⟨c⟩‿r ← 1(↑⋈↓) cands
      util.Progress visited.Count@
      {
        visited.Has c ? @ ;
        c visited.Set ok ← WithIn c
        ok ?
          n ← ¬∘visited.Has¨⊸/c<⊸+⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
          r n⊸∾ ↩
        ; @
      }
      r
    }•_while_(⟨⟩⊸≢)cand<⊸+⟨¯1‿0,0‿1,1‿0,0‿¯1⟩
    +´visited.Values@
  }
}
