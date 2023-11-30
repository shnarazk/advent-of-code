Data ← ⊜□≠@\n.&fras $"__data_2022_input-day10.txt" &var"AOC_REPO_DIR" ..Sep
Stream ← ⇌∧(⊂(⊂+⊙.|⋅∘)=0.⊙(⊡0.)) :[1 0] ≡(|1 (parse↘5|⋅0)≍"noop".⊔) Data
&p $"Part1: _" /+×⊏,:20_60_100_140_180_220 Stream
Scan ← ↯6_40⇡240
Mask ← ⍉↯40×40⇡6
&p $"Part2:\n_" ∵((@.|@#))≤1⌵-↯6_40↘1 Stream - Mask Scan
