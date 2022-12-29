#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lines ← •Flines "data/2022/input-day15.txt" lib.DataFile ⟨⟩ # •args
data ← (lib.ParseInts{∊⟜("-,:"∾'0'+¨↕10)}⊸/)¨ lines
Mdist ← { ⟨sx,sy⟩ 𝕊 ⟨bx,by⟩: (sx-bx)+○|(sy-by) }
Band ← { target_y 𝕊 ⟨sx,sy,bx,by⟩:
  d ← ⟨sx,sy⟩ Mdist ⟨bx,by⟩
  dx ← d-|target_y-sy
  { 0 ≤ dx ? ⟨sx-dx,sx+dx⟩; ⟨⟩ }
}
F ← { ⟨s, e⟩ 𝕊 ⟨total, start, end⟩ : {s ≤ end ? ⟨total,start,e⌈end⟩; ⟨total+end-start+1,s,e⟩} }
p1 ← 2000000
•Show ∘‿1⥊ b ← ∨(0<≠)¨⊸/ p1(Band¨) data
on_mark ← ≠⍷{⟨2⊑𝕩,3⊑𝕩⟩}¨((p1⊸=)∘(3⊸⊑))¨⊸/ data
•Show on_mark + {0⊑𝕩+2⊑𝕩-1⊑𝕩+1} ⟨0,0⊑¯1⊑b,1⊑¯1⊑b⟩F´b
p2 ← 4000000
sensors ← {⟨sx,sy,bx,by⟩ ← 𝕩 ⋄ ⟨sx,sy, ⟨sx,sy⟩ Mdist ⟨bx,by⟩⟩}¨ data
CheckAround ← {
  ⟨sx,sy,d⟩ 𝕊 0:
    ss ← {(⟨sx,sy⟩ Mdist ⟨0⊑𝕩,1⊑𝕩⟩)≤1+2⊑𝕩+d}¨⊸/sensors
    Sat ← { 𝕊 c: (0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ? ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ ss; 0 }
    p ← d+1
    l ← ↕p
    k ← (Sat¨⊸/{⟨sx+𝕩,(sy-p)+𝕩⟩}¨l)
       ∾(Sat¨⊸/{⟨(sx+p)-𝕩,sy+𝕩⟩}¨l)
       ∾(Sat¨⊸/{⟨sx-𝕩,(sy+p)-𝕩⟩}¨l)
       ∾(Sat¨⊸/{⟨(sx-p)+𝕩,sy-𝕩⟩}¨l)
    {
      k≡⟨⟩ ? 0; {(1⊑𝕩)+(0⊑𝕩)×p2}⊑k
    };
  𝕨 𝕊 n: n  
}
•Show 0 CheckAround´ sensors
