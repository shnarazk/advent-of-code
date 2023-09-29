data ← ⊜□≠@\n.&fras ⊂∶"/data/2022/input-day02.txt" &var "AOC_REPO_DIR"
keys ← ["A X" "A Y" "A Z" "B X" "B Y" "B Z" "C X" "C Y" "C Z"]
valsA ← [4 8 3 1 5 9 7 2 6]
&p$"Part1: _"/+∵(|1 ⊡∶valsA⊗∶keys!)data
valsB ← [3 4 8 1 5 9 2 6 7]
&p$"Part2: _"/+∵(|1 ⊡∶valsB⊗∶keys!)data
