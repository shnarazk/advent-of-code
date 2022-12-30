#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lines ← •Flines "data/2022/input-day15.txt" lib.DataFile ⟨⟩ # •args
data ← (lib.ParseInts{∊⟜("-,:"∾'0'+¨↕10)}⊸/)¨ lines
Mdist ← { ⟨sx,sy⟩ 𝕊 ⟨bx,by⟩: (sx-bx)+○|(sy-by) }
sensors ← {⟨sx,sy,bx,by⟩ ← 𝕩 ⋄ ⟨sx,sy, ⟨sx,sy⟩ Mdist ⟨bx,by⟩⟩}¨ data
Band ← { target_y 𝕊 ⟨sx,sy,d⟩: dx ← d-|target_y-sy⋄ { 0 ≤ dx ? ⟨sx-dx,sx+dx⟩; ⟨⟩ } }
p1 ← 2000000
b ← ∨(0<≠)¨⊸/ p1 Band¨ sensors
# •Show ∘‿1⥊ b
on_mark ← ≠⍷{⟨2⊑𝕩,3⊑𝕩⟩}¨((p1⊸=)∘(3⊸⊑))¨⊸/ data
F ← { ⟨s, e⟩ 𝕊 ⟨total, start, end⟩ : {s ≤ end ? ⟨total,start,e⌈end⟩; ⟨total+end-start+1,s,e⟩} }
•Show on_mark + {0⊑𝕩+2⊑𝕩-1⊑𝕩+1} ⟨0,0⊑¯1⊑b,1⊑¯1⊑b⟩F´b

p2 ← 4000000
CrossPoint ← {
  ⟨ax,ay,bx,by⟩ ← 𝕨
  ⟨sx,sy,tx,ty⟩ ← 𝕩
  ⟨f,g⟩ ← ⟨×by-ay, ×ty-sy⟩
  {
    f=g ? ⟨⟩;
      x ← ((sy + f×ax)-(ay + g×sx))÷(f - g)
      y ← ay + x - ax
      (ax≤x)∧(x≤bx)∧(ay≤y)∧(y≤bx)?⟨x,y⟩;⟨⟩
  }
}
CP ← { ⟨ax,ay,bx,by⟩ 𝕊 ⟨sx,sy,tx,ty⟩:
  { ax<bx ? ⟨ax,ay,bx,by⟩; ⟨bx,by,ax,ay⟩} CrossPoint { sx<tx ? ⟨sx,sy,tx,ty⟩; ⟨tx,ty,sx,sy⟩}
}
Intersections ← {
  ⟨ax,ay,ad1⟩ ← 𝕨
  ⟨bx,by,bd1⟩ ← 𝕩
  ad ← ad1 + 1
  bd ← bd1 + 1
  ⟨_pd,px,py⟩ ← ⊑∧{⟨⟨1⊑𝕩,1⊑𝕩⟩ Mdist ⟨bx,by⟩,0⊑𝕩,1⊑𝕩⟩}¨⟨⟨ax,ay+ad⟩,⟨ax,ay-ad⟩,⟨ax+ad,ay⟩,⟨ax-ad,ay⟩⟩
  ⟨_qd,qx,qy⟩ ← ⊑∧{⟨⟨0⊑𝕩,1⊑𝕩⟩ Mdist ⟨ax,ay⟩,0⊑𝕩,1⊑𝕩⟩}¨⟨⟨bx,by+bd⟩,⟨bx,by-bd⟩,⟨bx+bd,by⟩,⟨bx-bd,by⟩⟩
  {
    (px≡qx)∧(py≡qy) ? ⟨⟩;
      ⟨x1,y1⟩ ← ⟨px+(-py)+qx+qy, (-px)+(2×py)+(2×qx)+qy⟩
      ⟨x2,y2⟩ ← ⟨px+py+qx+(-qy), (¯3×px)+(¯3×py)+(-qx)+qy⟩
      ⟨⟩⊸≢¨⊸/⟨{(2|x1)∨(2|y1) ? ⟨⟩; ⟨2÷˜x1,2÷˜y1⟩},{(2|x2)∨(2|y2) ? ⟨⟩; ⟨2÷˜x2,2÷˜y2⟩}⟩
  }
  ⟨⟩⊸≢¨⊸/ ⟨ 
    ⟨ax,ay-ad,ax+ad,ay⟩ CP ⟨bx-bd,by,bx,by-bd⟩,
    ⟨ax,ay-ad,ax+ad,ay⟩ CP ⟨bx+bd,by,bx,by+bd⟩,
    ⟨ax,ay+ad,ax-ad,ay⟩ CP ⟨bx-bd,by,bx,by-bd⟩,
    ⟨ax,ay+ad,ax-ad,ay⟩ CP ⟨bx+bd,by,bx,by+bd⟩, 
    ⟨ax,ay+ad,ax+ad,ay⟩ CP ⟨bx-bd,by,bx,by+bd⟩,
    ⟨ax,ay+ad,ax+ad,ay⟩ CP ⟨bx+bd,by,bx,by-bd⟩,
    ⟨ax,ay-ad,ax-ad,ay⟩ CP ⟨bx-bd,by,bx,by+bd⟩,
    ⟨ax,ay-ad,ax-ad,ay⟩ CP ⟨bx+bd,by,bx,by-bd⟩,
 ⟩
  
}
cands ← ∧⍷∾⥊∘‿1⥊(Intersections⌜˜) sensors
# •Show ∘‿1⥊(2727057⊸=⊑)¨⊸/cands
Sat ← { 
  c 𝕊 0: {(0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ? { ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ sensors ? (1⊑c)+(0⊑c)×p2; 0}; 0};
  c 𝕊 n: n
}
•Show 0 Sat´ cands
