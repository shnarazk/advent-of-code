Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt¨ ↩
  {
    1=part ?
      Check ← {𝕨+=´(2⋆16)⊸|𝕩}
      ⊑{c‿p : c⊸Check⊸⋈ 2147483647|16807‿48271×p}⍟40000000 0⋈data ;
    Check ← {𝕨+=´(2⋆16)⊸|𝕩}
    Generate ← {f‿m 𝕊 x : 1⊑{(0≠f⊸|)⊸⋈ 2147483647|m×𝕩}´•_while_(⊑)1‿x}
    ⊑{𝕊 c‿⟨a,b⟩ : c⊸Check⊸⋈(4‿16807 Generate a)⋈(8‿48271 Generate b)}⍟5000000 0⋈data
  }
}
