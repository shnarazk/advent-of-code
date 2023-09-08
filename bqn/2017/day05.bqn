Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  l ← ≠data util.ParseInt¨ ↩
  Inc ← (2=part)◶⟨1,1+¯2×3⊸≤⟩
  1⊑{pc‿n : data {pc 𝕩⊸+ ↩ ⋄ Inc⊸+𝕩}⌾(pc⊸⊑) ↩ ⋄ pc∾1+n}•_while_((0⊸≤∧l⊸>)⊑)0‿0
}
