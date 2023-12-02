Data ← ↙4⊜□≠@\n.&fras $"__data_2023_input-day02.txt" &var"AOC_REPO_DIR" ..Sep
Parse ← dump∘⊂⊃(⊗ :{"red" "green" "blue"}⊡0)(parse⊔⊡1)⇌⊜□≠@\s.⊔
Data ← ≡(□≡(∧((⍜(⊡0)+|⍜(⊡1)+|⍜(⊡2)+)dump∘⊙:⊃(⊡0)(⊡1)):[0 0 0]⊏⍏.dump∘≡Parse⊜□≠@,.⊔)⊜□≠@;.⊔⊡1⊜□≠@:.⊔)Data
&p$"Part1: _"Data
