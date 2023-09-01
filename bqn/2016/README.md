# AoC 2016
```
CBQN on commit 86c570a65310fbb882f677c5123c8deeaf9fc2b1
built with FFI, singeli native aarch64, replxx
```
| y2016  |      LoC | p1 (sec) | p2 (sec) |
|--------|---------:|---------:|---------:|
| day 01 |       15 |    0.001 |    0.001 |
| day 02 |        7 |    0.002 |    0.002 |
| day 03 |        4 |    0.002 |    0.003 |
| day 04 |        9 |    0.004 |    0.103 |
| day 05 |       23 |  290.557 |  879.267 |
| day 06 |       26 |        0 |        0 |
| day 07 |       33 |    0.062 |    0.058 |
| day 08 |       22 |    0.007 |    0.007 |
| day 09 |       47 |    0.001 |    0.003 |
| day 10 |       57 |    0.059 |    0.064 |
| day 11 |       37 |    0.111 |    0.855 |
| day 12 |       25 |    0.355 |    9.983 |
| day 13 |       11 |    0.059 |    0.025 |
| day 14 |       10 |    0.916 | 1554.512 |
| day 15 |      N/A |      N/A |      N/A |
| day 16 |      N/A |      N/A |      N/A |
| day 17 |      N/A |      N/A |      N/A |
| day 18 |      N/A |      N/A |      N/A |
| day 19 |      N/A |      N/A |      N/A |
| day 20 |      N/A |      N/A |      N/A |
| day 21 |      N/A |      N/A |      N/A |
| day 22 |      N/A |      N/A |      N/A |
| day 23 |      N/A |      N/A |      N/A |
| day 24 |      N/A |      N/A |      N/A |
| day 25 |      N/A |      N/A |      N/A |

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
