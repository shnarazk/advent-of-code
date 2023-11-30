Data ← ∵⊔-@0⊜□≠@\n.&fras $"__data_2021_input-day03.txt" &var"AOC_REPO_DIR" ..Sep
Len ← ⧻Data
Major ← ÷2Len
&p$"Part1: _"×∩(∧(+×2:):0)¬.≡(>Major/+⊔)⍉Data
GatherO ← ▽=≥⊃(÷2⧻)(/+.)≡⊡⊙.
GatherC ← ▽=<⊃(÷2⧻)(/+.)≡⊡⊙.
ReducerO ← (⊃(+1)GatherO|⊙∘):⊙(=1⧻.)
ReducerC ← (⊃(+1)GatherC|⊙∘):⊙(=1⧻.)
&p$"Part2: _"×∩(∧(+×2:):0⊡0)⊃(|1 ;⍥ReducerO Len 0)(|1 ;⍥ReducerC Len 0)Data
