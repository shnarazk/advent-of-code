Data ← ⊜□≠@\n.&fras $"__data_2021_input-day04.txt" &var"AOC_REPO_DIR" ..Sep
Hands ← ⊜parse≠@,.⊔⊡0Data
Boards ← ↯¯1_5_5≡(⊜parse≠@\s.⊔)↘1Data
B ← ∵⊔⍉≡≡□\↥ ∺=Boards Hands
Bingos ← ≡'⊗1≡≡(|1 ↥⊃(/↥≑1/↧)(/↥≑2/↧)=1)B
&p$"Part1: _" ×⊃(⊡∶Hands⊡∶Bingos)(/+♭×⊃(¬ ⊡⊃(⊡∶Bingos)(⊡∶B))(⊡∶Boards))⊡0⍏Bingos
&p$"Part2: _" ×⊃(⊡∶Hands⊡∶Bingos)(/+♭×⊃(¬ ⊡⊃(⊡∶Bingos)(⊡∶B))(⊡∶Boards))⊡¯1⍏Bingos
