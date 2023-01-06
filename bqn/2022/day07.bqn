#!/usr/bin/env cbqn
⟨color,DataFile,ParseInts,StartsWith⟩ ← •Import "../lib.bqn"
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
eachDir ← (⊑⋈(+´∘((1⊸⊑)¨)∘ComponentsOf⊑))¨ dirs
•Show +´(1⊸⊑)¨(100000≥1⊸⊑)¨⊸/ eachDir
•Show dirSizes ← {𝕊 a‿b: b‿a}¨ eachDir

•Out color.blue color.Fmt "used"⋈1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
•Out color.blue color.Fmt "free"⋈free ← 70000000-1⊸⊑⊑("/"⊸≡⊑)¨⊸/eachDir
•Out color.blue color.Fmt "to be freed"⋈required ← 30000000 - free
•Out color.blue color.Fmt ⊑∧(required⊸<⊑)¨⊸/dirSizes
•Show ⊑⊑∧(required⊸<⊑)¨⊸/dirSizes
