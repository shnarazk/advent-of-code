⟨
  If, IfElse, While, DoWhile, For,
  Match, Select, Switch, Test,
  Tokenize, StartsWith, ParseInts,
  Max, Min, MaxAt, MinAt,
  version
⟩ ⇐
If      ← {𝕏⍟𝕎@}´                 # Also Repeat
IfElse  ← {c‿T‿F: c◶F‿T@}
While   ← {𝕩{𝔽⍟𝔾∘𝔽_𝕣_𝔾∘𝔽⍟𝔾𝕩}𝕨@}´  # While 1‿{... to run forever
DoWhile ← {𝕏@ ⋄ While 𝕨‿𝕩}´
For     ← {I‿C‿P‿A: I@ ⋄ While⟨C,P∘A⟩}
Match   ← {𝕏𝕨}´
Select  ← {(⊑𝕩)◶(1↓𝕩)@}
Switch ← {c←⊑𝕩 ⋄ m‿a←<˘⍉∘‿2⥊1↓𝕩 ⋄ (m⊸⊐⌾<C)◶a@}
Test    ← {fn←{C‿A𝕊e:C◶A‿E}´𝕩⋄Fn@}
# string operations
StartsWith ← { (≠𝕨) < (≠𝕩) ? 0 ; 0 = (<˘(≠𝕩)↕𝕨) ⊑∘⊐⟜< 𝕩 }
ParseInts ← {
  IsNum ← { (('0' ≤ 𝕩) ∧ (𝕩 ≤ '9')) ∨ ('-' = 𝕩) }
  Ordinal ← { w F 1: { w ≤ 0 ? -w; w }; w F 0: { 0 < w ? ¯1-w; w } }
  •BQN¨ 𝕩 ⊔˜ 1- ˜0⊸<⊸× ¯1 Ordinal` IsNum¨ 𝕩
}
Tokenize ← {
    F 𝕩: (' '≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩;
  𝕨 F 𝕩: (𝕨≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩
}
# math functions
Max ← { 𝕨 < 𝕩 ? 𝕩; 𝕨 }
Min ← { 𝕨 < 𝕩 ? 𝕨; 𝕩 }
MaxAt ← {(⌈´⊸(⊑⊒˜)𝕨⊸⊑¨𝕩)⊑𝕩}
MinAt ← {(⌊´⊸(⊑⊒˜)𝕨⊸⊑¨𝕩)⊑𝕩}

version ← "0.1.2"
