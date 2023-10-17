Data ← ⊜□≠@\n.&fras $"__data_2021_input-day04.txt" &var"AOC_REPO_DIR" ..Sep
Hands ← ⊜parse≠@,.⊔⊡0Data
Boards ← ↯¯1_5_5≡(⊜parse≠@\s.⊔)↘1Data
B ← ∵⊔⍉≡≡□\↥ ∺=Boards Hands
m ← ≡≡(|1 ↥⊃(/↥⍚1/↧)(/↥⍚2/↧)=1)B
Bingos ← ≡'⊗1m
tl ← ⊏0_¯1⍏Bingos
&p$"Part1: _" ×⊃(⊡∶Hands⊡∶Bingos)(/+♭×⊃(¬ ⊡⊃(⊡∶Bingos)(⊡∶B))(⊡∶Boards))⊡0tl
&p$"Part2: _" ×⊃(⊡∶Hands⊡∶Bingos)(/+♭×⊃(¬ ⊡⊃(⊡∶Bingos)(⊡∶B))(⊡∶Boards))⊡1tl
