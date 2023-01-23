lib ← •Import "../lib.bqn"

Mdist ← { ⟨sx,sy⟩ 𝕊 ⟨bx,by⟩: (sx-bx)+○|(sy-by) }
Band ← { target_y 𝕊 ⟨sx,sy,d⟩: dx ← d-|target_y-sy⋄ { 0≤dx ? ⟨sx-dx,sx+dx⟩; ⟨⟩ } }
CrossPoint ← { ⟨ax,ay,bx,by⟩ 𝕊 ⟨sx,sy,tx,ty⟩:
  ⟨f,g⟩ ← ⟨×by-ay,×ty-sy⟩
  {
    f=g ? ⟨⟩;
      x ← ((sy + f×ax)-(ay+g×sx))÷(f - g)
      y ← ay + x - ax
      (ax≤x)∧(x≤bx)∧(ay≤y)∧(y≤bx)?⟨x,y⟩;⟨⟩
  }
}
CP ← { ⟨ax,ay,bx,by⟩ 𝕊 ⟨sx,sy,tx,ty⟩:
  { ax<bx ? ⟨ax,ay,bx,by⟩; ⟨bx,by,ax,ay⟩} CrossPoint { sx<tx ? ⟨sx,sy,tx,ty⟩; ⟨tx,ty,sx,sy⟩}
}
Intersections ← { ⟨ax,ay,ad1⟩ 𝕊 ⟨bx,by,bd1⟩:
  ⟨ad,bd⟩ ← ⟨ad1+1,bd1+1⟩
  ⟨⟩⊸≢¨⊸/ ⟨
    ⟨ax,ay-ad,ax+ad,ay⟩CP⟨bx-bd,by,bx,by-bd⟩,
    ⟨ax,ay-ad,ax+ad,ay⟩CP⟨bx+bd,by,bx,by+bd⟩,
    ⟨ax,ay+ad,ax-ad,ay⟩CP⟨bx-bd,by,bx,by-bd⟩,
    ⟨ax,ay+ad,ax-ad,ay⟩CP⟨bx+bd,by,bx,by+bd⟩,
    ⟨ax,ay+ad,ax+ad,ay⟩CP⟨bx-bd,by,bx,by+bd⟩,
    ⟨ax,ay+ad,ax+ad,ay⟩CP⟨bx+bd,by,bx,by-bd⟩,
    ⟨ax,ay-ad,ax-ad,ay⟩CP⟨bx-bd,by,bx,by+bd⟩,
    ⟨ax,ay-ad,ax-ad,ay⟩CP⟨bx+bd,by,bx,by-bd⟩,
 ⟩
}

Solve ⇐ { part 𝕊 lines:
  data ← (lib.ParseInts{∊⟜("-,:"∾'0'+¨↕10)}⊸/)¨ lines
  sensors ← {⟨sx,sy,bx,by⟩ ← 𝕩 ⋄ ⟨sx,sy, ⟨sx,sy⟩ Mdist ⟨bx,by⟩⟩}¨ data
  {
    1=part ? 
      p1 ← 2000000
      b ← ∨(0<≠)¨⊸/ p1 Band¨ sensors
      on_mark ← ≠⍷{⟨2⊑𝕩,3⊑𝕩⟩}¨((p1⊸=)∘(3⊸⊑))¨⊸/ data
      F ← { ⟨s,e⟩ 𝕊 ⟨total,start,end⟩ : {s ≤ end ? ⟨total,start,e⌈end⟩; ⟨total+end-start+1,s,e⟩} }
      on_mark + {0⊑𝕩+2⊑𝕩-1⊑𝕩+1} ⟨0,0⊑¯1⊑b,1⊑¯1⊑b⟩F´b
    ;
      p2 ← 4000000
      cands ← ∧⍷∾⥊∘‿1⥊(Intersections⌜˜)sensors
      # •Show ∘‿1⥊(2727057⊸=⊑)¨⊸/cands
      Sat ← {
        c 𝕊 0: {(0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ? ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ sensors ? (1⊑c)+(0⊑c)×p2; 0};
        c 𝕊 n: n
      }
      0 Sat´ cands
  }
}