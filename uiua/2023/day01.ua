Data ← ⊜□≠@\n.&fras$"__Data_2023_input-day01.txt"&var"AOC_REPO_DIR" ..Sep

IsDigit ← ∊:[@0 @1 @2 @3 @4 @5 @6 @7 @8 @9]
---
⍤ :≍,1 IsDigit @2
⍤ :≍,0 IsDigit @A
---

Digits ← ▽IsDigit.
---
⍤ :≍,"123" Digits " 12 abc3d"
⍤ :≍,"" Digits "abcd"
---

Evaluate ← |1 parse⊂⊃(⊡0)(⊡¯1)Digits ⊔
---
⍤ :≍,13 Evaluate " 12 abc3d"
⍤ :≍,77 Evaluate "ab7cd"
---

&p$"Part1: _" /+≡(Evaluate)Data

Mnemonic ← {"零" "one" "two" "three" "four" "five" "six" "seven" "eight" "nine"}
Convert ← |1 ≡(|2 (⋅∘|+@0)>0.)/+×⇡10≡(⌕⊔) Mnemonic ¤.
---
⍤ :≍,"a9ine89in8ight0" Convert "anine8nineight0"
---

&p$"Part2: _" /+≡(Evaluate Convert ⊔)Data
