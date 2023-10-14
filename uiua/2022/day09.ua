Data ← ⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day09-0.txt"
Data ← ≡(|1 ⊂⊃(⊗∶"UDLR"⊡0⊔⊡0)(parse⊔⊡1) ⊜□≠@ .⊔)Data
# &p$"Part1: _"↙ 10 Data

# &p $"# signature: _" sig (!(+)∶)
# &p $"# signature: _" sig (!⊙∶(+))
# &p $"# signature: _" sig (!⊏0[(+)]∶)
# &p $"# signature: _" sig (;;!⊙∶(0 0 +))
# &p $"# signature: _" sig (;;!⊏0[(0 0 +)]∶)

# &p $"# call: _" !(!⊙∶(+)) 1 2
# &p $"# call: _" !(!⊏0[(+)]∶) 1 2
# &p $"# call: _" !(!(+)∶) 1 2

# &p $"# f signature: _" sig (!⊙∶(|2 +))
# &p $"# g signature: _" sig (!(|2 +)∶)

# (vec head tail --- vec newpos tail)
MoveHead ← (⊃⊃∘(+∶⊙∘)(⋅⋅∘))
# (vec head tail --- vec head  newpos)
MoveTail ← (⊃⊃(∘)(⋅∘)(⋅⋅∘))
# (code head tail --- iteration vec head tail)
Decode ← (⊃(⋅∘)(⊏∶[1_0 ¯1_0 0_¯1 0_1])⍘⊟)

∧(⊟;⍥(MoveTail MoveHead)dump∘⊃Decode(⋅⍘⊟)∶) [0_0 0_0] Data
