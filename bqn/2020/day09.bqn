Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  len ← ≠data ↩ util.ParseInt¨data
  sum ← 1⊑{𝕊 f‿p :
    ⟨t⟩‿r ← 1(↑⋈↓)p
    ⟨x⟩‿l ← ¯1(↑⋈↓)t
    (∊⟜(⥊(≠×+)⌜˜l)⌾<x)◶⟨0‿x,1‿r⟩@
  }•_while_⊑1⋈<˘26↕data
  {
    1=part ? sum ;
    1⊑{f‿n : v ← sum⊸≥⊸/+`n↓data ⋄ {(∊⟜v)⌾⋈sum ? 0∾(⌊´+⌈´)n↓(n+≠v)↑data ; 1∾1+n}}•_while_⊑1‿0
  }
}
