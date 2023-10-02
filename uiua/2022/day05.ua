data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
⍘⊟⊜□¬⊂∶0⌕"\n\n".data
⊜□≠@\n.!
head ← 
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
moves ← 

≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
towers ← 

Unfold ← (|1 /·⇌)

Split ← ⍘⊟↙2⊂∶[□""]⊜□+1≥∶⇡∶→(⧻.)

# I gave up the Under-based array modification. Instead use `rotate⁼ join drop rotate`
Move ← (|2
    Unfold!∶
    ⇵ [1 3 0 2 3 3 1 2]
    ∶∷!Split∶!⊡
    →→'!⊡
    →(⊂⇌)
    □→∶
    ⇵ [3 1 0 3 4 2 4]
    ↻¯∶⊂∶↘1↻
    ↻¯∶⊂□∶↘1↻∶
)
MoveSnd ← (|2
    Unfold!∶
    ⇵ [1 3 0 2 3 3 1 2]
    ∶∷!Split∶!⊡
    →→'!⊡
    →⊂
    □→∶
    ⇵ [3 1 0 3 4 2 4]
    ↻¯∶⊂∶↘1↻
    ↻¯∶⊂□∶↘1↻∶
)
&p$"Part1: _"≡(|1 ⊢!) ∧Move towers moves
&p$"Part2: _"≡(|1 ⊢!) ∧MoveSnd towers moves
