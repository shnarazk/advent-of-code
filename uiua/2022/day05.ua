data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
⊜□≠@\n.!⍘⊟⊜□¬⊂∶0⌕"\n\n".data
head ← 
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
moves ← 
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
towers ← 

# # on stack (⇌)2_0_2 {"abce" "" "xy"}
# (⇌)2_0_2 {"abce" "" "xy"}
Move ← (
  →!→∶
  →→→(∵⧻.⊏)→(.⊃⊢(↘1)) →→∶→∷.
  →→(∧(⊂→!)[]⊂⊓(□⍛1↙∶[])(□⍛2↙∶[])⍘⊟+× ¯1_0)
  →(⊂⍛0↙∶[])
  →→(/'⊂∷!)
  →(↙3⊂∶□""⊂∶□"" ⊕□)
  →;⍜⊏^→'↘1□⍜(⊡1)(□⊂∷!∶)∶⊃'⊡0'↘1 ?(⍜(⊡0)·)(⍜(⊡0)⇌)
)
# returns ["ce", "", "baxy"]

&p$"Part1: _"≡(|1 ⊢!)∧(Move 0) towers moves
&p$"Part2: _"≡(|1 ⊢!)∧(Move 1) towers moves
