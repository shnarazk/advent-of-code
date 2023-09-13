Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt¨ ↩
  {
    1=part ? +´data ;
    h ← Hashset⟨⟩
    -⊑{n‿sum :
      sum (n⊑data)⊸+ ↩
      {h.Has sum ? ⟨-sum,0⟩ ; h.Set sum ⋄ ⟨(≠data)|1+n, sum⟩}
    }•_while_(0≤⊑)0‿0
  }
}
