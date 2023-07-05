DecodeChar ← {
  F '-': ¯1;
  F '=': ¯2;
  F ch: ch - '0'
}
Decode ← +´(⌽5⊸⋆⊒˜)×DecodeChar¨
Encode ← {
  c ← 5 | 𝕩
  n ← 5 ÷˜ 𝕩-c
  {
    n = 0 ? '0'+c;
    c = 3 ? (Encode n+1)∾'=';
    c = 4 ? (Encode n+1)∾'-';
            (Encode n)∾'0'+c
  }
}
Solve ⇐ Encode·+´·Decode¨⊢
