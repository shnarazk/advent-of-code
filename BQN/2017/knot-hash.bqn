Trans ← {𝕨 𝕊 𝕩 :
  𝕩{r 𝕊 pos‿skip‿ring :
    ring (⌽⌾(r⊸↑))⌾((pos)⊸⌽) ↩
    ⟨256|skip+r+pos,1+skip,ring⟩
  }´⌽𝕨
}
KnotHash ⇐ {
       𝕊 data : 0 𝕊 data ;
  type 𝕊 data :
    data ∾⟜17‿31‿73‿47‿23∘-⟜@ ↩
    As16 ← {⊑⟜"0123456789abcdef"¨(⌽2↑⟨⟩{l 𝕊 0 : l ; (𝕨∾16|𝕩) 𝕊 𝕩⌊∘÷16}𝕩)}
    Xor ← {1‿16•bit._cast 1‿1•bit._xor´ ⟨16‿'u',1⟩•bit._cast∘⋈¨𝕩}
    type◶⟨∾·⥊⌽∘(8‿1•bit._cast)∘⋈¨,⥊,∾∘⥊As16¨⟩Xor˘16‿16⥊2⊑data Trans⍟64⟨0,0,↕256⟩
}
