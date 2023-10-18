# Geee, I don't like regex in uiua. It's just a stupid tokenizer.
Data ← ≡(⊜□¬∊∶"- :".⊔)⊜□≠@\n.&fras $"__data_2020_input-day02.txt" &var"AOC_REPO_DIR" ..Sep
&p$"Part1: _"/+≡(|1 ↧⊙≤≥⊙,⊃⊃(parse⊡0)(parse⊡1)(/+=⊢∩⊔⍘⊟↘2)⊔)Data
&p$"Part2: _"/+≡(|1 =1/+=⊙⊏⊃⊃(⊢⊡2)(-1∵'parse⊔↙2)(⊔⊡3)⊔)Data
