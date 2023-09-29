data ← &fras ⊂∶"/data/2022/input-day01.txt" &var "AOC_REPO_DIR"
Sum ← /+⊜parse≠,@\n
values ← ⊜Sum ¬↥↻¯1.⊂∶0⌕"\n\n". data
&p$"Part1: _"/↥values
&p$"Part2: _"/+⊏↙3⇌⌂.values
