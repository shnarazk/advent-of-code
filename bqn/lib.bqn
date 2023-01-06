⟨
  If, IfElse, While, DoWhile, For,
  Match, Select, Switch, Test,
  Swap,
  Tokenize, StartsWith, ParseInts, ParseInt,color
  MaxAt, MinAt,
  DataFile,
  version
⟩ ⇐


#
# program structure
#
If      ← {𝕏⍟𝕎@}´                 # Also Repeat
IfElse  ← {c‿T‿F: c◶F‿T@}
While   ← {𝕩{𝔽⍟𝔾∘𝔽_𝕣_𝔾∘𝔽⍟𝔾𝕩}𝕨@}´  # While 1‿{... to run forever
DoWhile ← {𝕏@ ⋄ While 𝕨‿𝕩}´
For     ← {I‿C‿P‿A: I@ ⋄ While⟨C,P∘A⟩}
Match   ← {𝕏𝕨}´
Select  ← {(⊑𝕩)◶(1↓𝕩)@}
Switch  ← {c←⊑𝕩 ⋄ m‿a←<˘⍉∘‿2⥊1↓𝕩 ⋄ (m⊸⊐⌾<C)◶a@}
Test    ← {fn←{C‿A𝕊e:C◶A‿E}´𝕩⋄Fn@}

#
# list operations
#
#     Swap list: swap the first element and the second one in the `list` 
# i‿j Swap list: swap the `i`-th element and the `j`-th one in the `list` 
Swap ← {
        𝕊 l: ⟨a,b⟩←⟨⊑𝕩,1⊑𝕩⟩ ⋄ b˙⌾⊑a˙⌾(1⊸⊑) 𝕩;
  ⟨i,j⟩ 𝕊 l: ⟨a,b⟩←⟨i⊑𝕩,j⊑𝕩⟩ ⋄ b˙⌾(i⊸⊑)a˙⌾(j⊸⊑)𝕩
}

#
# string operations
#
StartsWith ← { (≠𝕨) < (≠𝕩) ? 0 ; 0 = (<˘(≠𝕩)↕𝕨) ⊑∘⊐⟜< 𝕩 }
ParseInts ← {
  IsNum ← { (('0' ≤ 𝕩) ∧ (𝕩 ≤ '9')) ∨ ('-' = 𝕩) }
  Ordinal ← { w F 1: { w ≤ 0 ? -w; w }; w F 0: { 0 < w ? ¯1-w; w } }
  •BQN¨ 𝕩 ⊔˜ 1- ˜0⊸<⊸× ¯1 Ordinal` IsNum¨ 𝕩
}
ParseInt ← ⊑ParseInts
Tokenize ← {
    F 𝕩: (' '≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩;
  𝕨 F 𝕩: (𝕨≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩
}
color ← {
  esc ⇐ @ + 27
  black ⇐ esc∾"[30m"
  red ⇐ esc∾"[31m"
  green ⇐ esc∾"[32m"
  yellow ⇐ esc∾"[33m"
  blue ⇐ esc∾"[34m"
  magenta ⇐ esc∾"[35m"
  cyan ⇐ esc∾"[36m"
  white ⇐ esc∾"[37m"
  # reverse ⇐ esc∾"[001m"
  reset ⇐ esc∾"[0m"
  # revert ⇐ esc∾"[1A\x1B[1G\x1B[1K"
  Out ⇐ { c 𝕊 t: c∾t∾reset }
  Fmt ⇐ { c 𝕊 t: c∾(•Fmt t)∾reset }
}

#
# math functions
#
# what are they? Element-based one?
MaxAt ← {(⌈´⊸(⊑⊒˜)𝕨⊸⊑¨𝕩)⊑𝕩}
MinAt ← {(⌊´⊸(⊑⊒˜)𝕨⊸⊑¨𝕩)⊑𝕩}

#
# file operations
#
DataFile ← {
  0 < ≠𝕩 ? •wdpath∾ "/"∾ ⊑𝕩;
           •wdpath∾ "/"∾ 𝕨
}
version ← "0.3.0"
