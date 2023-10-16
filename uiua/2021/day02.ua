Data ← ⊜□≠@\n.&fras $"__data_2021_input-day02.txt" &var"AOC_REPO_DIR" ..Sep
Record ← ≡(×⊃(⊏∶[¯1_0 1_0 0_1]⊢⊚=∶"udf"⊡0⊔⊡0)(parse⊡1)⊔)∵(⊜□≠@\s.⊔)Data
&p$"Part1: _"/×/+Record
PosAim ← [0_0 0_0]
&p$"Part2: _"/×⊡0∧(|2 ?(⍜'⊡0+∶⊂⊃(×⊡1⊙(⊡0⊡1))(⊡1⊙∘);)(⍜'⊡1+∶;)=0⍘⊟.∶) PosAim Record
