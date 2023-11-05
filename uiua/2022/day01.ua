Data ← &fras $"__data_2022_input-day01.txt" &var "AOC_REPO_DIR" ..Sep
Sum ← /+⊜parse≠,@\n
Values ← ⊜Sum ¬↥↻¯1.⌕"\n\n". Data
&p$"Part1: _"/↥Values
&p$"Part2: _"/+⊏↙3⍖.Values
