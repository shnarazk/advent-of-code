Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜ "," env.Var⌾⋈ "BQN_LIB"
  data (¯4+">}]) ([{<"⊸⊐¨) ↩
  {
    1=part ?
      +´⊑¨{notfound‿stack‿l :
        ⟨c⟩‿r ← 1(↑⋈↓)l
        {
          0<c ? ⟨0,c∾stack,r⟩ ;
          c=-⊑stack ? ⟨0,1↓stack,r⟩ ;
          ⟨c-⊸⊑⟨0,3,57,1197,25137⟩,c∾stack,r⟩
        }
      }•_while_{𝕊 f‿s‿l : ⟨⟩≢l ? 0≥f ; 0}∘(¯1‿⟨⟩∾<)¨data
  }
}
