#!/usr/bin/env uiua run
# Note: this program is only for AoC, tailoring for AoC filename convension
FirstColumn ← 16
SecondColumn ← 6
Year ← ?(⊂∶"/"⊔⊡0)("./";)⧻.↘1&args
FileList ← ∵(□⊂∶".ua"⊂"day"↙¯2⊂"00"$"_")+1⇡25
NotBlankLine ← ▽∵(≠0⧻).
NotStartsWithComment ← ▽∵(/<⊂⊃(⊗@#⊔)(⊗0=@ ⊔)).
LoC ← ⧻NotStartsWithComment NotBlankLine ⊜□¬=@\n.&fras
≡(&fe⊔)..∵(⊂Year ⊔)FileList
≡(|2 ?(LoC)(□"N/A";))
≡(|2 □$"| _ | _ |"⬚@ (↙) FirstColumn $"_" ⊙(⬚@ (↙) dump∘ SecondColumn $"_")∶∩⊔)
⊂□$"|-_-|-_-:|" ⬚@-↙ FirstColumn "" ⬚@-↙ - 1 SecondColumn ""
⊂□$"| File_ | LoC_ |" ⬚@ ↙ - 4 FirstColumn "" ⬚@ ↙ - 3 SecondColumn ""
∵&p
