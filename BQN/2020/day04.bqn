Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ ⍉≍⥊∘(":"⊸util.Split)¨∘(" "⊸util.Split)∘(∾´)∘(∾⟜' '¨)¨(+`⟨⟩⊸≡¨)⊸⊔ data
  {
    1=part ? ≠(7=≠)¨⊸/("cid"≢⊑)¨⊸/¨⥊data ;
    Satisfy ← {
      "cid"‿w 𝕊 x : x ;
      "byr"‿w 𝕊 x : {(1920⊸≤∧2002⊸≥)util.ParseInt w ? x+10⋆0 ; x} ;
      "iyr"‿w 𝕊 x : {(2010⊸≤∧2020⊸≥)util.ParseInt w ? x+10⋆1 ; x} ;
      "eyr"‿w 𝕊 x : {(2020⊸≤∧2030⊸≥)util.ParseInt w ? x+10⋆2 ; x} ;
      "hgt"‿w 𝕊 x : {
        "cm"≡¯2↑w ? (150⊸≤∧193⊸≥)util.ParseInt ¯2↓w ? x+10⋆3 ;
        "in"≡¯2↑w ? (59⊸≤∧76⊸≥)util.ParseInt ¯2↓w ? x+10⋆3 ;
        x
      } ;
      "hcl"‿w 𝕊 x : {((7=≠)∧('#'=⊑)∧(∧´∘((∊⟜"0123456789abcdef")⌾⋈¨)∘(1⊸↓)))w ? x+10⋆4 ; x} ;
      "ecl"‿w 𝕊 x : {(∊⟜"amb"‿"blu"‿"brn"‿"gry"‿"grn"‿"hzl"‿"oth")⌾⋈w ? x+10⋆5 ; x} ;
      "pid"‿w 𝕊 x : {((9=≠)∧(∧´∘(('0'⊸≤∧'9'⊸≥)¨)))w ? x+10⋆6 ; x} ;
      𝕩
    }
    ≠{1111111=0 Satisfy´𝕩}¨⊸/⥊data
  }
}
