Solve ⇐ {env‿part 𝕊 data :
  Dec ← +⟜(2⊸×)´∘⌽
  data '1'⊸= ↩
  {
    1=part ? ×○Dec⟜¬(2÷˜≠data)<+¨´data ;
    2=part ?
      Select ← {f 𝕊 𝕩 :
        ⊑⊑{cands‿k :
          target ← (2÷˜≠cands){𝕨=𝕩 ? f ; f ? 𝕨<𝕩 ; 𝕨>𝕩}+´mask ← k⊸⊑¨cands
          ⟨cands/˜target=mask,k+1⟩
        }•_while_(1⊸<·≠⊑)𝕩‿0
      }
      ×○Dec´0‿1 Select¨< data
  }
}
