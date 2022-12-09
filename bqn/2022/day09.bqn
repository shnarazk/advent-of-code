#!/usr/bin/env cbqn
⟨DataFile, ParseInt⟩ ← •Import "../lib.bqn"
moves ← (1⊸↑⋈(ParseInt 2⊸↓))¨ •FLines "data/2022/input-day09.txt" DataFile •args
DirVec ← { 
  F ⟨"U", r⟩: ⟨ 0, -1⟩; 
  F ⟨"D", r⟩: ⟨ 0,  1⟩; 
  F ⟨"L", r⟩: ⟨-1,  0⟩; 
  F ⟨"R", r⟩: ⟨ 1,  0⟩; 
  "error" ! 1
}
Update ← { 
  ⟨dir, 0⟩ F state: state;
  ⟨dir, n⟩ F ⟨head, tail, history⟩:
    new_head ← head +¨ DirVec ⟨dir, n⟩
    ⟨diff_x, diff_y⟩ ← new_head -¨ tail
    new_tail ← {
      1 < |diff_x × diff_y ? new_tail ← tail +¨ ⟨diff_x ÷ |diff_x, diff_y ÷| diff_y⟩;
      1 < |diff_x ? new_tail ← tail +¨ ⟨diff_x ÷ |diff_x, 0⟩;
      1 < |diff_y ? new_tail ← tail +¨ ⟨0, diff_y ÷| diff_y⟩;
      tail
  }
  new_history ← {
    ⟨new_tail⟩ ⊑∘∊ history ? history;
    ⟨new_tail⟩ ∾ history
  }
  •Show ⟨new_head, new_tail, n-1⟩
  ⟨dir, n-1⟩ F ⟨new_head, new_tail, new_history⟩
}
•Show ≠2⊑⟨⟨0,0⟩, ⟨0,0⟩, ⟨⟩⟩ Update´ ⌽moves
