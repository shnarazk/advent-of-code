Data ← &fras $"__data_2022_input-day05.txt" &var"AOC_REPO_DIR" ..Sep
ParseInts ← (⊜parse∊∶"0123456789-".⊔)
≡⊔⊜□≠@\n.⊔⍘⊟⊜□¬⊂∶0⌕"\n\n".Data
Head ←
≡(+0_¯1_¯1ParseInts)⊜□≠@\n.⊔
Moves ←
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡'↘¯1 ↘¯1Head
Towers ←

# Transform ← (|3
#   # build the arsenal → [mode towers move]
#   ⊂⊙(⊂∩□)
#   # index calculation → [indexs mode towers move]
#   ⊂□⊂⊂⊃⊃(⊡0⊔⊡2)(-∶⧻⊡∶⊃⊃(⊔⊡0)(⊔⊡1⊔⊡1)(⊔⊡0⊔⊡1)⊏1_2)(⧻⊔⊡∶⊃(⊔⊡0)(⊡2⊔⊡1)⊏1_2).
#   # partitioning → [segments mode towers move]
#   ⊂⊙'↘1□⬚("")↙3∘⊕□⊃(∧(⊂⊙⊔)[]∵(|2 □⬚|⊙((↙))⊙⊙[])⇡3⊔⊡0)(/(⊂∩⊔)⊏⊃(↘1⊔⊡0)(⊔⊡1)⊔⊏3_2).
#   # mode-specific task → [replaces towers move]
#   ⊂⊙'↘2□⊂⊃(⊡1)(□/'⊂∩⊔⊏0_2)⍜'⊡0;∶?∘⇌⊃⊃(⊔⊡0)(⊡0⊔⊡1)(⊔⊡1)⊏1_0 .
#   ⍜⊏;⊙∶⊃⊃(↘1⊔⊡2)(⊔⊡0)(⊔⊡1)
# )

Tra ← (|3 ⊙';;dump∘)
∵⊢∧0_2_1 Tra 0 Towers Moves
# ∵⊢∧'Transform1 Towers Moves
