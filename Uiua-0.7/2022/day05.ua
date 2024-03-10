Data ← &fras $"__data_2022_input-day05.txt" &var"AOC_REPO_DIR" ..Sep
ParseInts ← (⊜parse∊:"0123456789-".⊔)
≡⊔⊜□≠@\n.⊔⍘⊟⊜□¬⌕"\n\n".Data
Head ←
≡(+0_¯1_¯1ParseInts)⊜□≠@\n.⊔
Moves ←
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡(↘¯1) ↘¯1Head
Towers ←

Trans ← (|3.2
  ⊃⊃(⋅⋅∘)(∘)(⋅∘)                                  # restack as tower move mode
  ⊂⊃⊃(⊡⊡1⋅⊙∘)(⊡⊡2⋅⊙∘)(⊂⊙⊙∘)                       # pick swapping targets
  ⊂⊙(↘1)⊂∩□⊃(⊓↙↘,,:⊔⊢⊙(⊡1))(⊙⊙∘)                  # divide 3 parts
  ⊂∩□⊙⊐⊂⊃⊃(⊔⊡1)(⊡0)(⊡2)⊃(⊂(⇌|∘):⊡0⊙⊙(↘1),⊢:)(⋅⊙∘) # move head after reverse if needed
  ⍜⊏(|2 ⋅∘)⊃(⊃⊃(↘2 ⋅∘)(⋅⋅∘)(∘))(⊡0⋅∘)             # substitution
)
&p $"Part1: _"∵⊢∧Trans Moves Towers 0
&p $"Part1: _"∵⊢∧Trans Moves Towers 1
