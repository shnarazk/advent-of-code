Data ← &fras $"__data_2022_input-day05.txt" &var"AOC_REPO_DIR" ..Sep
ParseInts ← (⊜parse∊∶"0123456789-".⊔)
≡⊔⊜□≠@\n.⊔⍘⊟⊜□¬⊂∶0⌕"\n\n".Data
Head ←
≡(+0_¯1_¯1ParseInts)⊜□≠@\n.⊔
Moves ←
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡'↘¯1 ↘¯1Head
Towers ←

Trans ← (|3.2
  ⊙∶
  ⊂⊃⊃(⊡⊡1⋅⊙∘)(⊡⊡2⋅⊙∘)(⊂⊙⊙∘)                       # pick swapping targets
  ⊂⊙'↘1⊂∩□⊃(⊓↙↘,,∶⊔⊢⊙'⊡1)(⊙⊙∘)                    # divide 3 parts
  ⊂∩□⊙⊂⊃⊃(⊔⊡1)(⊔⊡0)(⊔⊡2)⊃(⊂(⇌|∘)∶⊡0⊙⊙'↘1,⊢∶)(⋅⊙∘) # move head after reverse if needed
  ⊃(⊃⊃(↘2 ⋅∘)(⋅⋅∘)(∘))(⊡0⋅∘)                      # prepare for substitution
  ∶⍜⊏(|2 ⋅∘)                                      # wrap up
)
&p $"Part1: _"∵⊢;∧0_1_1 Trans 0 Towers Moves
&p $"Part1: _"∵⊢;∧0_1_1 Trans 1 Towers Moves
