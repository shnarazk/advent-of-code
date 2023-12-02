Data ← ⊜□≠@\n.&fras $"__data_2023_input-day02.txt" &var"AOC_REPO_DIR" ..Sep
Parse ← ⊂⊃(⊗ :{"red" "green" "blue"}⊡0)(parse⊔⊡1)⇌⊜□≠@\s.⊔
Data ← ≡(□≡(∧((⍜(⊡0)+|⍜(⊡1)+|⍜(⊡2)+)⊙:⊃(⊡0)(⊡1)):[0 0 0]⊏⍏.≡Parse⊜□≠@,.⊔)⊜□≠@;.⊔⊡1⊜□≠@:.⊔)Data
&p$"Part1: _" /++1⊚≡(/↧≤[12 13 14])≡(∧↥:[0 0 0]⊔)Data
&p$"Part2: _" /+≡(/×)≡(∧↥:[0 0 0]⊔)Data
