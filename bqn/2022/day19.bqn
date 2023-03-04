lib ← •Import "../lib.bqn"
Solve ⇐ { part 𝕊 line:
  data ← >{
    is ← lib.ParseInts 𝕩
    4‿4⥊⟨
          1⊑is,    0,    0,   0,
          2⊑is,    0,    0,   0,
          3⊑is, 4⊑is,    0,   0,
          5⊑is,    0, 6⊑is,   0,
        ⟩
  }¨ line
  Examine ← { u 𝕊 n:
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    Expand ← {
      𝕊 ⟨⟩: best;
      𝕊 to_visit:
        𝕊 ⟨⟩ { time‿resources‿robots 𝕊 next:
          { 𝕊 i:
            upto< t ← time- w ← 1+⌈⌈´(i⊏masks)/robots÷˜(n ← i⊏bp)(0⊸⌈-)resources ?
              { ¬∨´(∧´𝕩⊸≤)¨next ? next ⟨𝕩⟩⊸∾ ↩ ;@ } t∾(n-˜resources+w×robots)∾((1⊸+)⌾(i⊸⊑)robots)
            ;
              best ((¯1⊑resources)+(time-upto)×¯1⊑robots)⊸⌈ ↩
          }¨{robots<○(𝕩⊸⊑)limits }¨⊸/↕4
          next
        }´{⟨⊑𝕩,4↑1↓𝕩,5↓𝕩⟩}¨to_visit
    }
    (•Fmt n) lib.Debug Expand ⟨⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩⟩ # ⟨time,resources,robots⟩
  }
  {
    1=part ? +´ 24 ((1⊸+)×Examine)¨↕≠data
    ; 2=part ? ×´ 32 Examine¨↕3
    ; "≢data" lib.Debug ≢data
  }
}
