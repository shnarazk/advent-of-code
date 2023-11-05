#!/usr/bin/env uiua run

FirstColumn ← 16
SecondColumn ← 5

Year ← ?(⊂∶"/"⊔⊡0)("./";)⧻.↘1&args
FileList ← ∵(□⊂∶".ua"⊂"day"↙¯2⊂"00"$"_")+1⇡25

&p$"| File_ | LoC_ |" ∩(⬚@ ↙∶"") - 4 FirstColumn - 3 SecondColumn
&p$"|-_-|-_-:|" ∩(⬚@-↙∶"") FirstColumn - 1 SecondColumn

RunTime ← |1 □?(|3 $"_"-∶now ⋅⋅∘)("fail";;;)=0&runc∶now ⊂{"uiua" "run" "--no-format"}□
∵(⊂Year ⊔)FileList
≡(|1.0 &p$"| _ | _ |" ∩(⬚@\s↙)⊐⊓(FirstColumn $"_")(SecondColumn $"_")∶?RunTime("N/A")&fe⊔..)
