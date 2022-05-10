#!/usr/bin/env bqn
Split ← { F letters:
    records ← ⟨1, ⟨""⟩, ⟨⟩⟩ {
        '[' 𝕊 𝕩 : ⟨¯1×(⊑𝕩)    , 1⊑𝕩               , ⟨""⟩∾(2⊑𝕩)       ⟩;
        ']' 𝕊 𝕩 : ⟨1+(¯1×(⊑𝕩)), ⟨""⟩∾(1⊑𝕩)        , 2⊑𝕩              ⟩;
        0 < ⊑𝕩 ?  ⟨⊑𝕩         , ⟨(𝕨∾⊑1⊑𝕩)⟩∾(1↓1⊑𝕩), 2⊑𝕩              ⟩;
                  ⟨⊑𝕩         , 1⊑𝕩               , ⟨(𝕨∾⊑2⊑𝕩)⟩∾(1↓2⊑𝕩)⟩
    }´ ⌽ letters
    (⌽¨1⊑records)‿(⌽¨2⊑records)
}

# Part 1: TLS #####################################
CheckTLS ← {
    CheckWord ← { (0⊑𝕩 = 3⊑𝕩) ∧ (1⊑𝕩 = 2⊑𝕩) ∧ (0⊑𝕩 ≠ 1⊑𝕩) }
    CheckChunk ← { 4 > ≠𝕩 ? 0; 0 < ⌈´CheckWord¨ <˘4↕𝕩 }
    (0 < ⌈´CheckChunk¨ 0⊑𝕩) ∧ (0 = ⌈´CheckChunk¨ 1⊑𝕩)
}
example ← ⟨ "abba[mnop]qrst", "abcd[bddb]xyyx", "aaaa[qwer]tyui", "ioxxoj[asdfgh]zxcvbn" ⟩
a_example ← 5↑ ⥊ •FLines "../data/2016/input-day07.txt"
•Show example
•Show ⥊>Split¨ example
•Show (CheckTLS∘Split)¨ example
•Show +´(CheckTLS∘Split)¨ ⥊ •FLines "../data/2016/input-day07.txt"

# Part 2: SSL #####################################
CheckSSL ← {
    CheckWord ← { (0⊑𝕩 = 2⊑𝕩) ∧ (0⊑𝕩 ≠ 1⊑𝕩) }
    Pickup ← { 3 > ≠𝕩 ? 0; CheckWord¨⊸/ <˘3↕𝕩 }
    CrossCheck ← { w ← ⥊>𝕨 ⋄ x ← ⥊>𝕩 ⋄ (0⊑w ≠ '_') ∧ (0⊑w = 1⊑x) ∧ (1⊑w = 0⊑x) }
    0⌈´⥊(∾´Pickup¨ 0⊑𝕩) CrossCheck⌜ (∾´Pickup¨ 1⊑𝕩)
}
example2 ← ⟨ "aba[bab]xyz", "xyx[xyx]xyx", "aaa[kek]eke", "zazbz[bzb]cdb" ⟩
# example2 ← 5↑ ⥊ •FLines "../data/2016/input-day07.txt"
•Show example2
•Show >Split¨ example2
•Show (CheckSSL∘Split)¨ example2
•Show +´(CheckSSL∘Split)¨ ⥊ •FLines "../data/2016/input-day07.txt"
