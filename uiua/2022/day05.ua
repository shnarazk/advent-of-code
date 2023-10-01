data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
⍘⊟⊜□¬⊂∶0⌕"\n\n".data
⊜□≠@\n.!
head ← 
≡ParseInts⊜□≠@\n.!
moves ← 
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
towers ← 
↙ 10moves
# &p$"Part1: _"ParseInts ⊡10 data
# ↙ 20 data
