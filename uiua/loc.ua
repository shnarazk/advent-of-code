#!/usr/bin/env uiua run

FirstColumn ← 16
SecondColumn ← 6

# NotBlankLine ← ▽∵(≠0⧻).
NotStartsWithComment ← ▽∵(/<⊂⊃(⊗@#⊔)(⊗0=@ ⊔)).
LoC ← ⧻NotStartsWithComment ⊜□≠@\n.&fras

# Note: this program is only for AoC, tailoring for AoC filename convension
# ≡'LoC⊔ .▽∵(|1 ≅ ".ua" ↙¯3⊔).&fld ?"."(⊔⊡1⊔)=1⧻.&args
Year ← ?(⊂∶"/"⊔⊡0)("./";)⧻.↘1&args
FileList ← ∵(□⊂∶".ua"⊂"day"↙¯2⊂"00"$"_")+1⇡25

&p$"| File_ | LoC_ |" ∩(⬚@ ↙∶"") - 4 FirstColumn - 3 SecondColumn
&p$"|-_-|-_-:|" ∩(⬚@-↙∶"") FirstColumn - 1 SecondColumn

≡(|2 ?(LoC)(□"N/A";)) ≡(&fe⊔)..∵(⊂Year ⊔)FileList
∵&p≡(|2 □$"| _ | _ |" ∩(⬚@ (↙))⊓(FirstColumn $"_")(SecondColumn $"_")∶)
