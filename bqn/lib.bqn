⟨
  If,IfElse,While,DoWhile, For,
  Match, Select, Switch, Test,
  Swap,
  Tokenize,StartsWith,ParseInt,ParseInts,ParseFloat,ParseFloats,color,term
  MaxAt,MinAt,
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
StartsWith ← (⊢≡↑˜⟜≠)
ParseInts ←•BQN¨·(∨´"0123456789"⊸∊)¨⊸/"0123456789-"⊸((⊢-˜¬×·+`»⊸<)∘(¬∊)˜⊔⊢)
ParseFloats ←•BQN¨·(∨´"0123456789"⊸∊)¨⊸/"0123456789.-"⊸((⊢-˜¬×·+`»⊸<)∘(¬∊)˜⊔⊢)
ParseInt ← ⊑ParseInts
ParseFloat ← ⊑ParseFloats
Tokenize ← {
    F 𝕩: (' '≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩;
  𝕨 F 𝕩: (𝕨≠𝕩) (¬-˜⊢×·+`»⊸>)⊸⊔ 𝕩
}
color ← {
  # https://en.wikipedia.org/wiki/ANSI_escape_code
  esc ⇐ @ + 27
  csi ⇐ esc∾"["
  black ⇐ csi∾"30m"
  red ⇐ csi∾"31m"
  green ⇐ csi∾"32m"
  yellow ⇐ csi∾"33m"
  blue ⇐ csi∾"34m"
  magenta ⇐ csi∾"35m"
  cyan ⇐ csi∾"36m"
  white ⇐ csi∾"37m"
  reverse ⇐ csi∾"001m"
  reset ⇐ csi∾"0m"
  RGB ⇐ {
      𝕊 r‿g‿b: esc∾"[38;2;"∾(•Fmt r)∾";"∾(•Fmt g)∾";"∾(•Fmt b)∾"m";
    0 𝕊 r‿g‿b: esc∾"[38;2;"∾(•Fmt r)∾";"∾(•Fmt g)∾";"∾(•Fmt b)∾"m";
    r‿g‿b 𝕊 0: esc∾"[48;2;"∾(•Fmt r)∾";"∾(•Fmt g)∾";"∾(•Fmt b)∾"m";
    bg 𝕊 fg: (bg 𝕊 0)∾𝕊 fg
  }
  Out ⇐ { c 𝕊 t: c∾t∾reset }
  Fmt ⇐ { c 𝕊 t: c∾(•Fmt t)∾reset }
}
term ← {
  # https://en.wikipedia.org/wiki/ANSI_escape_code
  esc ⇐ @ + 27
  csi ⇐ esc∾"["
  reverse ⇐ csi∾"001m"
  reset ⇐ csi∾"0m"
  Revert ⇐ { csi∾(•Fmt 𝕩)∾"A"∾csi∾"1G"∾csi∾"0J" }
  Up ⇐ { csi∾(•Fmt 𝕩)∾"A" }
  clear ⇐ csi∾"1G"∾csi∾"0J"
  Print ⇐ { •Out (•Fmt 𝕩)∾Up 1; •Out 𝕨∾(•Fmt 𝕩)∾reset∾Up 1 }
  Println ⇐ { •Out (•Fmt 𝕩); •Out 𝕨∾(•Fmt 𝕩)∾reset }
  Out ⇐ { •Out 𝕩∾Up 1; •Out 𝕨∾𝕩∾reset∾Up 1 }
  OutLn ⇐ { •Out 𝕩; •Out 𝕨∾𝕩∾reset }
}

#
# math functions
#
MaxAt ← {n F l: {𝕨>○(n⊸⊑)𝕩?𝕨;𝕩}´l}
MinAt ← {n F l: {𝕨<○(n⊸⊑)𝕩?𝕨;𝕩}´l}

#
# file operations
#
DataFile ← { 0 < ≠𝕩 ? •wdpath∾ "/"∾ ⊑𝕩; •wdpath∾ "/"∾ 𝕨 }
version ← "0.4.0"
