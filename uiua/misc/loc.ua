#!/usr/bin/env uiua run
# Usage:   loc.ua [dir]   -- display loc of .ua files in dir

FirstColumn ← 16
SecondColumn ← 6

LoC ← ⧻▽∵(<⊃(⊗@#⊔)(⊗0=@\s⊔)).⊜□≠@\n.&fras

FileList ← ▽∵(|1 ≍ ".ua" ↙¯3⊔).&fld (⊔⊡1⊔|".")=1⧻.&args

&p$"| File_ | LoC_ |" ∩(⬚@\s↙:"") - 4 FirstColumn - 3 SecondColumn
&p$"|-_-|-_-:|" ∩(⬚@-↙:"") FirstColumn - 1 SecondColumn
≡(LoC⊔) .FileList
≡(|2 □$"| _ | _ |" ∩(⬚@\s↙)⊓(FirstColumn $"_")(SecondColumn $"_"):)
∵(&p⊔)
