Solve ⇐ {env‿part 𝕊 data :
  # lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  Dec ← +⟜(2⊸×)´∘⌽
  data ('1'⊸=) ↩
  {
    1=part ? ×○Dec⟜¬(2÷˜≠data)<+¨´data ;
    2=part ?
      Select ← {
        𝕨   𝕊 ⟨cand⟩ : cand ;
        f‿k 𝕊 cands  :
          mask ← k⊸⊑¨cands
          target ← (2÷˜≠cands){𝕨=𝕩 ? f ; f ? 𝕨<𝕩 ; 𝕨>𝕩}+´mask
          f‿(k+1)𝕊(target=mask)/cands
      }
      ×○Dec´⟨0‿0,1‿0⟩Select¨<data
    ; !0
  }
}
