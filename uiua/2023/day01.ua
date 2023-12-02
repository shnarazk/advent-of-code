Data ← ⊜□≠@\n.&fras$"__Data_2023_input-day01.txt"&var"AOC_REPO_DIR" ..Sep
Evaluate ← |1 parse⊂⊃(⊡0)(⊡¯1)▽≡(↧⊃(≥@1)(≤@9)).⊔
---
⍤ :≍,13 Evaluate " 12 abc3d"
⍤ :≍,77 Evaluate "ab7cd"
---

&p$"Part1: _" /+≡Evaluate Data

Convert ← ≡((⋅∘|+@0)>0.)/+×⇡10≡(⌕⊔){"零" "one" "two" "three" "four" "five" "six" "seven" "eight" "nine"}¤.
---
⍤ :≍,"a9ine89in8ight0" Convert "anine8nineight0"
---

&p$"Part2: _" /+⊐≡(Evaluate Convert)Data
