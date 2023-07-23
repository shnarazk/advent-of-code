Solve ⇐ { env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  To_dec ← +⟜(2⊸×)´∘⌽
  data (>'1'⊸=) ↩
  rank2‿rank1 ← ≢data
  {
    1=part ? ×○To_dec´⋈⟜¬(rank2÷2)<+˝data ;
    2=part ?
      Select ← {
        𝕨   𝕊 ⟨cand⟩ : cand ;
        f‿k 𝕊 cands  :
          mask ← k⊸⊑¨cands
          target ← (2÷˜≠cands){𝕨=𝕩 ? f ; f ? 𝕨<𝕩 ; 𝕨>𝕩}+´mask
          f‿(k+1)𝕊(target=mask)/cands
      }
      ×○To_dec´⟨0‿0,1‿0⟩Select¨<<˘data
    ; !0
  }
}
