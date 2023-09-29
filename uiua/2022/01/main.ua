data ← &fras⊂∶"/data/2022/input-day01.txt" &var"AOC_REPO_DIR"
blocks ← ⊕□-1×+1∶¬↥↻¯1.∶\+.⊂∶0∺≅∶[1 1]◫2=@\n.data
Lines ← □∵(|1 parse!)⊜□≠,@\n
values ← ∵(|1 Lines!)blocks
&p$"Part1: _"/↥∵(|1 /+!)values
&p$"Part2: _"/+⊏↙3⇌⌂.∵(|1 /+!)values
