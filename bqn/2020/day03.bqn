Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  height‿width ← ≢data >∘('#'⊸=¨) ↩
  {
    1=part ? 1⊑{y‿c : ⟨1+y, c+data⊑˜⟨y,width|3×y⟩⟩}•_while_(height>⊑)1‿0 ;
    ×´2⊑¨{dy‿dx : {y‿x‿c : ⟨dy+y,width|dx+x⟩∾c+y‿x⊑data}•_while_(height>⊑)dy‿dx‿0}¨⟨1‿1,1‿3,1‿5,1‿7,2‿1⟩
  }
}
