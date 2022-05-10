#!/usr/bin/env bqn

example ← "eedadn
drvtee
eandsr
raavrd
atevrs
tsrnev
sdttsa
rasrtv
nssdts
ntnada
svetve
tesnvt
vntsnd
vrdear
dvrsen
enarar
"

example_keys ← ⍉6↑˘∘‿7 ⥊ example
# •Show example_keys

PickMost ← {
    i ← (¯1⊸⊏∘⍋∘⊒)˘ 𝕩
    { (0⊑𝕩)⊑(1⊑𝕩) }˘ ⍉ (i ≍ (<˘ 𝕩))
}

# •Show ⊒˘ example_keys
•Show "Part 1"
•Show PickMost example_keys

lines ← ⥊ •FLines "../../data/2016/input-day06.txt"
# •Show 10 ↑ lines
keys ← ⍉ ∘‿8 ⥊ ∾´ lines
# •Show keys
•Show PickMost keys

•Show "Part 2"
PickLeast ← {
    bigN ← +´⥊≠⌜ 𝕩
    letters ← (<)˘ 𝕩
    •Show "letters"‿letters
    occurs ← (1+ ⊒)¨ letters
    •Show "numbers of occurs"
    •Show ⍉ occurs
    targets ← (⌽∘∊∘⌽)¨ letters
    •Show "targets"
    •Show targets
    ot ← occurs × targets
   •Show "ot = occurs × targets"‿ot
    scores ← ot + bigN × 1 - targets
   # •Show "scores"‿scores
    leasts ← ⌊´¨ scores
    •Show "leasts"‿leasts
    indices ← >{(𝕩⊑scores) ⊐ (𝕩⊑leasts) }¨ ↕≠ leasts
    >{(𝕩⊑indices) ⊑ (𝕩⊑letters) }¨ ↕≠ leasts
}
•Show PickLeast example_keys
# •Show PickLeast keys
