Part1 ← {amount‿from‿to F state :
  {
    val‿dropped ← (⊑⋈(1⊸↓))from⊑𝕩
    pushed ← (<val)∾to⊑𝕩
    pushed˙⌾(to⊸⊑)dropped˙⌾(from⊸⊑)𝕩
  }⍟amount state
}
Part2 ← {amount‿from‿to F state :
 val‿dropped ← amount(↑⋈↓)from⊑state
 (val⊸∾)⌾(to⊸⊑)dropped˙⌾(from⊸⊑)state
}

Solve ⇐ {env‿part 𝕊 data :
  ⟨color,ParseInts⟩← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨header,lines⟩ ← ⟨⟨⟩⟩⊸(⊑⊐˜)⊸(↑⋈↓)data
  •Out color.green color.Fmt init ← ⟨⟨⟩⟩∾¯1⊸↓¨⟨⟩⊸≢¨⊸/(' '⊸≠)¨⊸/¨<˘⍉⟨≠header,∘⟩⥊∾((¬∊⟜" []")(' '⊸+×)-⟜' ')¨header
  •Out color.green color.Fmt 5↑actions ← ParseInts¨1↓lines
  (⊑¨1⊸↓){1=part ? init Part1´ 𝕩 ; init Part2´ 𝕩}⌽actions
}
