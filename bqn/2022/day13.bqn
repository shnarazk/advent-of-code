#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
problems ← (2⊸↑˘)∘‿3⥊∾⟜ ⟨⟨⟩⟩ •FLines "data/2022/input-day13.txt" lib.DataFile •args
Reform ← { ch 𝕊 out‿digits: {
  ch=',' ? { 0<≠digits ? (out∾(•BQN digits))‿⟨⟩; out‿⟨⟩ };
  ch='[' ? { 0<≠digits ? (out∾⟨•BQN digits,'['⟩)‿⟨⟩; (out∾('['))‿⟨⟩ };
  ch=']' ? { 0<≠digits ? (out∾⟨•BQN digits,']'⟩)‿⟨⟩; (out∾(']'))‿⟨⟩ };
  out‿(digits∾ch)
} }
Enlist ← {  
  '[' 𝕊 stack: stack∾⟨⟨⟩⟩;
  ']' 𝕊 ⟨stk⟩: ⟨stk⟩;
  ']' 𝕊 stack: last ← ¯1⊑stack⋄ (∾⟜⟨last⟩)⌾(¯1⊸⊑)¯1↓stack;
  tkn 𝕊 stack: (∾⟜⟨tkn⟩)⌾(¯1⊸⊑) stack
}
problems { ⊑ ⟨⟩ Enlist´⌽ ⊑(⟨⟩‿⟨⟩) Reform´ ⌽𝕩 }¨˘ ↩
InOrder ← {
  ⟨⟩ 𝕊 ⟨⟩:  0;
  ⟨⟩ 𝕊  𝕩:  1;
  𝕨  𝕊 ⟨⟩: ¯1;
  w  𝕊  x:
    (ww‿ws)‿(xx‿xs) ← (⊑⋈(1⊸↓))¨ w‿x
    {
      (0=≡ww)∧(0=≡xx) ? { ww=xx ? ws InOrder xs; ×xx-ww }; 
      (0<≡ww)∧(0<≡xx) ? bool ← ww InOrder xx ⋄ { 1=|bool ? bool; ws InOrder xs };
      ⟨⟩≡ww           ?  1;
      ⟨⟩≡xx           ? ¯1;
      0<≡ww           ? bool ← ww InOrder ⟨xx⟩ ⋄ { 1=|bool ? bool; ws InOrder xs };
      0<≡xx           ? bool ← ⟨ww⟩ InOrder xx ⋄ { 1=|bool ? bool; ws InOrder xs };
        ! 0
    }
}
•Show +´((1=InOrder)´˘ problems)/1+↕≠problems   
