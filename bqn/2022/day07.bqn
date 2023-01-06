#!/usr/bin/env cbqn
⟨DataFile,ParseInts,StartsWith⟩ ← •Import "../lib.bqn"
# lines ← (⊑ParseInts)¨ •FLines "bqn/2022/input-day07.txt" DataFile •args # This file was created by a Rust program :-)
# •Show +´(100000⊸≥)¨⊸/ lines
# used ← ⌈´ lines
# need ← used - 40000000 
# •Show ∧(need⊸≤)¨⊸/ lines
lines ← ∧•FLines "bqn/2022/input-day07.txt" DataFile •args
# •Show lines
dirs ←(⊑","⊸(⊒˜))⊸(↑⋈(•BQN(1⊸+⊸↓)))¨ lines
•Show sample ← 4⊑dirs
ComponentsOf ← {(𝕩˙(StartsWith˜)⊑)¨⊸/dirs}
•Show eachDir ← (⊑⋈(+´∘((1⊸⊑)¨)∘ComponentsOf⊑))¨ dirs
•Show +´(1⊸⊑)¨(100000≥1⊸⊑)¨⊸/ eachDir