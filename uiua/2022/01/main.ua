data ← &fras ⊂∶"/data/2022/input-day01.txt" &var "AOC_REPO_DIR"
Lines ← ∵(|1 parse!)⊜□≠,@\n
values ← ∵(|1 /+Lines!)⊕□-1×+1∶¬↥↻¯1.∶\+.⊂∶0∺≅∶[1 1]◫2=@\n. data
&p$"Part1: _"/↥values
&p$"Part2: _"/+⊏↙3⇌⌂.values
