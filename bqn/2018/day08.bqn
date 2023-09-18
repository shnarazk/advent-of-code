Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  {
    1=part ?
      2⊑{index‿stack‿sum:
        {
          ∞≡⊑stack ?
            child‿meta ← (0‿1+index)⊏data
            ⟨index+2,(∞¨↕child)∾⟨meta⟩∾1↓stack,sum⟩
          ;
            ⟨meta⟩‿tack ← 1(↑⋈↓)stack
            ⟨index+meta,tack,sum++´(index+↕meta)⊏data⟩
        }
      }•_while_(⟨⟩≢1⊸⊑)⟨0,⟨∞⟩,0⟩
    ;
      +´2⊑{index‿stack‿sum:
        {
          ∞≡⊑stack ?
            child‿meta ← (0‿1+index)⊏data
            # child and meta will be used AFTER traverse, so keep then in stack
            ⟨index+2,(∞¨↕child)∾⟨child‿meta⟩∾1↓stack,sum⟩
          ;
            ⟨child‿meta⟩‿tack ← 1(↑⋈↓)stack
            {
              0=child ?
                ⟨index+meta,tack,sum∾˜+´(index+↕meta)⊏data⟩
              ;
                s‿um ← child(↑⋈↓)sum
                i ← ((≠s)⊸>∧(0⊸≤))¨⊸/¯1+(index+↕meta)⊏data
                v ← +´i⊏⌽s
                ⟨index+meta,tack,v∾um⟩
            }
        }
      }•_while_(⟨⟩≢1⊸⊑)⟨0,⟨∞⟩,⟨⟩⟩
  }
}
