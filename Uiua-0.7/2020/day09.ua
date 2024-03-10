Data ← ⊜parse≠@\n.&fras $"__data_2020_input-day09.txt" &var"AOC_REPO_DIR" ..Sep
Win ← 25
Check ← |2.2 ¬∊∶▽∩♭≡≡/≠⇡△.⊃(⊞+.↙Win↘-Win)(⊡⊙.)
Target ← ⊢▽⊙(↘Win)≐(⊙;Check)↘Win⇡⧻..Data
&p$"Part1: _" Target
Map ← |1 ?(0;;)(?(0;;)(+⊃(⊢)(⊢⇌)⊏⍏.↙)=0.⊢)≍[].⊚=Target\+.
&p$"Part2: _" ⊡⊢⊚.⊐≡Map⊐≐↘⇡⧻.Data
