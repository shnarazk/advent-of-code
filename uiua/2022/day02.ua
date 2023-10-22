Data ← ⊜□≠@\n.&fras $"__data_2022_input-day02.txt" &var "AOC_REPO_DIR" ..Sep
Keys ← ["A X" "A Y" "A Z" "B X" "B Y" "B Z" "C X" "C Y" "C Z"]
ValsA ← [4 8 3 1 5 9 7 2 6]
&p$"Part1: _"/+∵(|1 ⊡∶ValsA⊗⊔∶Keys)Data
ValsB ← [3 4 8 1 5 9 2 6 7]
&p$"Part2: _"/+∵(|1 ⊡∶ValsB⊗⊔∶Keys)Data
