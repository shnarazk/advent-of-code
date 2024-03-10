Solve ⇐ {env‿part 𝕊 data :
  data -⟜'a'¨¨ ↩
  Increase ← {
    1⊑0‿⟨⟩{
      25 𝕊 0‿l : 0⋈0∾l ;
       d 𝕊 0‿l : 1⋈(d+1)∾l ;
       d 𝕊 1‿l : 1⋈d∾l
    }´𝕩
  }
  Satisfied ← {∨´(⊢≡0‿1‿2+⊑)˘3↕𝕩 ? ¬∨´("iol"-'a')∊˜𝕩 ? 2≤≠⍷⊑¨(=´)¨⊸/<˘2↕𝕩 ; 0}
  s1 ← Increase•_while_(¬Satisfied)Increase ¯1⊑data
  {
    1=part ?  ('a'⊸+)s1 ;
    ('a'⊸+)Increase•_while_(¬Satisfied) Increase s1
  }
}
