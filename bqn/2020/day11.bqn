Solve ⇐ {env‿part 𝕊 data :
  util‿geometry ← •Import¨"/util.bqn"‿"/geometry.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ↩ 'L'=>data
  # floor‿empty‿occupied ← ↕3
  around ← (4≠↕)9
    {
    1=part ?
      (+´·⥊2⊸=)⊑{now‿pre :
        ⟨{1 𝕊 0 : 2 ; 2 𝕊 m : 4≤m ? 1 ; w 𝕊 m : w}¨⟜((+´2⊸=)¨(around⊸/¨geometry.Neighbor9))now,now⟩
      }•_while_(≢´)⋈⟜(0¨)data
  }
}
