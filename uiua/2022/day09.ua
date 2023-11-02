Data ← ⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day09.txt"
Data ← ≡(|1 ⊂⊃(⊗∶"UDLR"⊡0⊔⊡0)(parse⊔⊡1) ⊜□≠@ .⊔)Data
# &p$"Part1: _"↙ 10 Data

💩 ← 0
DontGive ← ;
# &p $"# signature: _" sig (!(+)∶)
# &p $"# signature: _" sig (!⊙∶(+))
# &p $"# signature: _" sig (!⊏0[(+)]∶)
# &p $"# signature: _" sig (DontGive DontGive!⊙∶(💩 💩 +))
# &p $"# signature: _" sig (DontGive DontGive!⊏0[(💩 💩 +)]∶)

# (vec head_tail --- vec newpos_tail)
MoveHead ← (⊙(⍜(⊡0)+∶).)
---
⍤ "movehead"≍1_1 ⊙; MoveHead 1_1 [1_0 ∞_∞]
⍤ "movehead"≍[2_1 ∞_∞] ;MoveHead 1_1 [1_0 ∞_∞]
---

# (head tail --- number)
TheCase ← (|2 ↥×2↧⊃⊃(/↥>1)(/↥=0)(/↥>1)⌵-)
---
⍤ "Case" =2 TheCase 1_1 4_1
⍤ "Case" =1 TheCase 1_1 3_3
---

# (head_tail --- head_newpos)
MoveTail ← (|1 ⊟⊙⊏∶⊙⊙⊂⊙⊙⊟⊃⊃⊃(TheCase)(⊙∘)(+±-,)(+±-,)⊃(⊡0)(⊡1))
---
⍤ "movetail" ≍ [2_2 2_1] MoveTail [2_2 1_0]
---

# (code --- iteration vec)
Decode ← (⊃(⋅∘)(⊏∶[1_0 ¯1_0 0_¯1 0_1])⍘⊟)

# (head_tail history --- head_tail history')
StoreTail ← (|2.2 ⊙(□⊂□⊡¯1).⊙⊔)
---
⍤ "storetail" ≍ □[□1_1] ; StoreTail [∞_∞ 1_1] □[]
⍤ "storetail" ≍ □[□1_1 □0_0] ; StoreTail [∞_∞ 1_1] □[□0_0]
---

&p$"Part1:_"⧻⊝⊡1∧1_1(|2 ⊟□;⍥(|3.3 ⊙(StoreTail MoveTail) MoveHead)⊃Decode(⋅∘)⊙(⊔⍘⊟)∶) [□↯2 0_0 □[]] Data

# (windows body --- windows' body')
MoveTails ← (?⊙∘(⊙(⍜⊏MoveTail⊔)⊃(↘1)(⊡0))=0⧻.)

&p$"Part2:_"⧻⊝⊡1∧1_1(|2 ⊟□;⍥(|3.3 ⊙(StoreTail;⍥MoveTails9 ◫2⇡10)MoveHead)⊃Decode(⋅∘)⊙(⊔⍘⊟)∶) [□↯10 0_0 □[]] Data
