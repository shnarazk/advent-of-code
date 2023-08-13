Solve ⇐ {env‿part 𝕊 line :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ← >{[
    ⟨1⊑𝕩,   0,   0,  0⟩
    ⟨2⊑𝕩,   0,   0,  0⟩
    ⟨3⊑𝕩, 4⊑𝕩,   0,  0⟩
    ⟨5⊑𝕩,   0, 6⊑𝕩,  0⟩
  ]}∘lib.ParseInts¨line
  Examine ← {u 𝕊 n :
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    Expand ← {𝕊 cands :
      lib.Progress n⋈best
      ∧⟨⟩{time‿resources‿robots 𝕊 next :
        {
          upto<time ? upto<t ← time-w ← 1+⌈⌈´(𝕩⊏masks)/robots÷˜(n ← 𝕩⊏bp)(0⊸⌈-)resources ?
          tt ← t∾(n-˜resources+w×robots)∾((1⊸+)⌾(𝕩⊸⊑)robots)
          ¬∨´∧´∘tt⊸≤¨next ? next ⟨tt⟩⊸∾ ↩ ⋄ best ((4⊑tt)+(t-upto)×¯1⊑tt)⊸⌈ ↩ ; @
        }¨{robots<○(𝕩⊸⊑)limits}¨⊸/↕4
        next
      }´{⟨⊑𝕩,4↑1↓𝕩,5↓𝕩⟩}¨cands
    }
    Expand•_while_(⟨⟩⊸≢)⟨⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩⟩
    best
  }
  {1=part ? +´24((1⊸+)×Examine)¨↕≠data ; ×´32 Examine¨↕3}
}
