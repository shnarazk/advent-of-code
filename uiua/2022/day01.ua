Data ← &fras ⊂∶"/data/2022/input-day01.txt" &var "AOC_REPO_DIR"
Sum ← /+⊜parse≠,@\n
Values ← ⊜Sum ¬↥↻¯1.⊂∶0⌕"\n\n". Data
&p$"Part1: _"/↥Values
&p$"Part2: _"/+⊏↙3⇌⍏.Values
