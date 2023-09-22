Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  Digits ← {𝕊 𝕩 : ⟨⟩ 𝕊 𝕩 ; ⟨⟩ 𝕊 0 : ⟨0⟩ ; l 𝕊 0 : l ; (𝕨∾˜10|𝕩)𝕊 𝕩⌊∘÷10}
  !⟜(⟨0⟩⊸≡)Digits 0
  !⟜(⟨1,2,0⟩⊸≡)Digits 120
  {
    1=part ?
      10↑data↓2⊑{ia‿ib‿seq :
        {0=1000|≠seq ? util.Progress (≠seq)÷10+data ; @}
        rs ← ⟨⟩Digits+´ current ← ia‿ib⊏seq
        seq ∾⟜rs ↩
        ⟨(≠seq)|ia+1+⊑current,(≠seq)|ib+1+1⊑current,seq⟩
      }•_while_((10+data)>(≠2⊸⊑))⟨0,1,3‿7⟩
    ;
      data Digits ↩
      l ← ¯1+-≠data
      (data≢(-≠data)⊸↑)◶⟨data⊸(-˜○≠), -¬data⊸(-˜○≠)⟩3⊑{ia‿ib‿seq :
        {0=1000|≠seq ? util.Progress ≠seq ; @}
        rs ← Digits+´ current ← ia‿ib⊏seq
        seq ∾⟜rs ↩
        ⟨(≠seq)|ia+1+⊑current,(≠seq)|ib+1+1⊑current,seq⟩
      }•_while_{end ← l↑2⊑𝕩 ⋄ (data≢¯1↓end)∧data≢1↓end}⟨0,1,3‿7⟩

  }
}
