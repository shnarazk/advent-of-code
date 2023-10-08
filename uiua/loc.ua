#!/usr/bin/env uiua run
# Note: this program is only for AoC, tailoring for AoC filename convension
Year ← ?(⊂∶"/"⊔⊡0)("./";)⧻.↘1&args
FileList ← ∵(□⊂∶".ua"⊂"day"↙¯2⊂"00"$"_")+1⇡25
# FIXME: handle '#' in string
IgnoreSharpInString ← ∘
# FIXME: handle '@#'
IgnoreSharpAsCharactor ← ∘
NotBlankLine ← ▽∵(≠0⧻).
NotStartsWithComment ← ▽∵(/<⊂⊃(⊗@#⊔)(⊗0=@ ⊔)).
LoC ← |1 ⧻NotStartsWithComment NotBlankLine IgnoreSharpAsCharactor IgnoreSharpInString⊜□¬=@\n.&fras
≡(&fe⊔)..∵(⊂Year ⊔)FileList
≡(|2 ?(LoC)(□"N/A";))
≡(|2 □$"| _ | _ |"∶∩⊔)
⊂{"|---------------|-----:|"}
⊂{"|    File       | LoC  |"}
∵&p
