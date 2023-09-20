Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  h ← Hashmap˜⟨⟩
  Mark ← {sign‿fp 𝕊 path :
    1⋈0‿0{d‿len 𝕊 n‿pos :
      dir ← ⟨1‿0,¯1‿0,0‿¯1,0‿1⟩⊑˜"UDLR"⊸⊐⌾⋈d ⋄ 𝕩
      {pos h.Set n⌾(fp⊸⊑)sign+0‿0‿∞‿∞ h.Get pos dir⊸+ ↩ ⋄ n 1⊸+ ↩ ⋄ 𝕩-1}•_while_(0⊸<)len
      n‿pos
    }´⌽path
  }
  ⟨0‿1‿0‿0,2⟩‿⟨1‿0‿0‿0,3⟩Mark¨((⊑⋈(util.ParseInt 1⊸↓))¨","⊸util.Split)¨data
  (2=part)◶⟨⌊´(+○|´⊑)¨,⌊´(+´2↓1⊸⊑)¨⟩(∧´0<1⊸⊑)¨⊸/⥊h.Values⁼˜@
}
