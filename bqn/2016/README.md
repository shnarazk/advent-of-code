# AoC 2016

| y2016  |  part 1 |  part 2 |
|--------|--------:|--------:|
| day 01 |   0.001 |   0.002 |
| day 02 |   0.002 |   0.002 |
| day 03 |   0.003 |   0.003 |
| day 04 |   0.004 |   0.105 |
| day 05 | skipped | skipped |
| day 06 |       0 |       0 |
| day 07 |   0.061 |   0.058 |
| day 08 |   0.007 |   0.007 |
| day 09 |   0.001 |   0.003 |
| day 10 |   0.058 |   0.062 |
| day 11 | skipped | skipped |
| day 12 | skipped | skipped |
| day 13 | skipped | skipped |
| day 14 | skipped | skipped |
| day 15 | skipped | skipped |
| day 16 | skipped | skipped |
| day 17 | skipped | skipped |
| day 18 | skipped | skipped |
| day 19 | skipped | skipped |
| day 20 | skipped | skipped |
| day 21 | skipped | skipped |
| day 22 | skipped | skipped |
| day 23 | skipped | skipped |
| day 24 | skipped | skipped |
| day 25 | skipped | skipped |

## day 8

```apl
GetNums ← {
  IsNum ← { (('0' ≤ 𝕩) ∧ (𝕩 ≤ '9')) ∨ ('-' = 𝕩) }
  Build ← { w F 1: { w ≤ 0 ? -w; w }; w F 0: { 0 < w ? ¯1-w; w } }
  •BQN¨ 𝕩 ⊔˜ 1- ˜0⊸<⊸× ¯1 Build` IsNum¨ 𝕩
}
GetNums "x=30, y=-5, z=55"
```

## day 10

```mermaid
flowchart TD
B2 -- 2 --> B1;
B1 -- 2 --> OUTPUT1=2;
B1 -- 3 --> B0;
B0 -- 3 --> OUTPUT2=3;
B0 -- 5 --> OUTPUT0=5;
```

| value | trace      |
|-------|------------|
| 2     | B2, B1     |
| 3     | B2, B1, B0 |
| 5     | B2, B1, B0 |

## day 11

- 20220522 GIVE UP PART 2.

To solve part 2, we need to implement Hash-table [object](https://mlochbaum.github.io/BQN/doc/oop.html) using with chain scheme.
- method `Add`
- method `Contains`

```apl
    MakeStack ← {𝕤
      st←@
      Push⇐{   st↩𝕩‿st}
      Pop ⇐{𝕤⋄ r‿s←st ⋄ st↩s ⋄ r}
      Len ⇐{𝕤⋄ ≠st}
    }
    s ← MakeStack @
    k ← MakeStack @
    s.Push 44
    s.Push 2
    s.Pop @
    s.Pop @
    k.Len @
```

```apl
HashTableNew ← {
  st←⟨⟩˙¨↕4⋆1+𝕩
  mask←¬2⊸|¨↕1+2×𝕩
  Key⇐{0 {𝕨+4×𝕩}´ mask/𝕩}
  Add⇐{ F 𝕩: k ← Key 𝕩 ⋄ st↩ 𝕩⊸∾⌾k⊑st}
  Contains ⇐{F 𝕩: k ← Key 𝕩 ⋄ 𝕩∊k⊑st}
  Len ⇐{𝕤⋄ ≠st}
  Dbg ⇐{mask/𝕩}
}
h ← HashTableNew 7
h.Dbg ⟨0,0,0,0,0,1,2,1,1,1,1,0,0,0,0⟩
h.Key ⟨3,0,3,0,3,1,3,1,3,1,3,0,3,0,3⟩
# h.Len @
```
