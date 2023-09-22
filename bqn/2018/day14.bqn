Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  Digits ← {⟨⟩ 𝕊 0 : ⟨0⟩ ; l 𝕊 0 : l ; (𝕨∾˜10|𝕩)𝕊 𝕩⌊∘÷10}
  !⟜(⟨0⟩⊸≡)⟨⟩ Digits 0
  !⟜(⟨1,2,0⟩⊸≡)⟨⟩ Digits 120
  {
    1=part ?
      10↑data↓3⊑{r‿ia‿ib‿seq :
        {0=1000|r ? util.Progress ⟨r,(≠seq)÷10+data⟩ ; @}
        rs ← ⟨⟩Digits+´ current ← ia‿ib⊏seq
        seq ∾⟜rs ↩
        ⟨r+1,(≠seq)|ia+1+⊑current,(≠seq)|ib+1+1⊑current,seq⟩
      }•_while_((10+data)>(≠3⊸⊑))⟨0,0,1,3‿7⟩
    ;
      0
  }
}
