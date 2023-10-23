Data ← ⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day10.txt"
Data ← ≡(|1 ?(⋅0)(parse ↘5)≍"noop".⊔)Data
Stream ← ⇌∧1_0(⊂?(⋅∘)(⊂+⊙(.))=0.⊙(⊡0.)∶) [1 0] Data
&p$"Part1: _"/+×⊏,∶20_60_100_140_180_220Stream
Scan ← ↯ 6_40 ⇡240
Mask ← ⍉↯40×40⇡6
- Mask Scan
&p$"Part2:\n_"∵(?@#@.)≤1⌵-↯ 6_40 ↘1Stream
