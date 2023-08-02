#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1⊸↓∘↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜@)˝v}}
⟨StartsWith⟩ ← •Import"/util.bqn"∾˜∾env.Var<"BQN_LIB"

! "00000" StartsWith "0"
! "00000" StartsWith "00"
! "00010" StartsWith "000"
! "01232" StartsWith "0123"

CallMd5 ← {¯1↓1⊑•SH"md5"‿"-qs"‿𝕩}
# IsPassword ← ("00000"˙⊸StartsWith˜)
IsPassword ← {𝕩 StartsWith "00000"}
•Show(<"test case:")∾IsPassword⊸CallMd5¨"abc3231929"‿"abc5017308"
key ← "wtnhxymk"
Input ← {key∾•Repr 𝕩}
Md5 ← CallMd5∘Input
# # Part 1: #####################################
•Show IsPassword⊸/ Md5¨ 1000000 + ↕1000000
# # Part 2: #####################################
