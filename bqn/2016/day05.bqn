#!/usr/bin/env BQNLIBDIR=/.config/bqn BQNLIB=/lib.bqn cbqn
env ← {v←(⊑'='⊐˜⊢)⊸(↑⋈(1⊸↓↓))¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env",Var⇐{(@∾˜1⊑¨v)⊏˜⊐⟜𝕩˜⊑¨v}}
⟨StartsWith⟩ ← •Import∾env.Var"HOME"‿"BQNLIBDIR"‿"BQNLIB"
CallMd5 ← { ¯1↓1⊑ •SH "md5"‿"-qs"‿𝕩 }
# IsPassword ← ("00000"˙⊸StartsWith˜)
IsPassword ← {𝕩 StartsWith "00000"}
    •Show (<"test case: ")∾ IsPassword⊸ CallMd5¨ "abc3231929"‿"abc5017308"
key ← "wtnhxymk"
Input ← {key∾•Repr 𝕩}
Md5 ← (CallMd5∘Input)
# # Part 1: #####################################
•Show IsPassword⊸/ Md5¨ 1000000 + ↕1000000
# # Part 2: #####################################
