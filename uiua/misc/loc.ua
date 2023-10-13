#!/usr/bin/env uiua run
# Usage:   loc.ua [dir]   -- display loc of .ua files in dir

FirstColumn ← 16
SecondColumn ← 6

LoC ← ⧻▽∵'<⊃(⊗@#⊔)(⊗0=@ ⊔).⊜□≠@\n.&fras

FileList ← ▽∵(|1 ≅ ".ua" ↙¯3⊔).&fld ?"."(⊔⊡1⊔)=1⧻.&args

≡'LoC⊔ .FileList
≡(|2 □$"| _ | _ |" ∩(⬚@ (↙))⊓(FirstColumn $"_")(SecondColumn $"_")∶)
⊂□$"|-_-|-_-:|" ∩(⬚@-↙∶"") FirstColumn - 1 SecondColumn
⊂□$"| File_ | LoC_ |" ∩(⬚@ ↙∶"") - 4 FirstColumn - 3 SecondColumn
∵&p
