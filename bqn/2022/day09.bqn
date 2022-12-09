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
UpdateTail ← {  
  ⟨dx, dy⟩ ← 𝕨 -¨ 𝕩
  𝕩 +¨ {
    1 < |dx × dy ? ⟨dx ÷ |dx, dy ÷| dy⟩;
    1 < |dx      ? ⟨dx ÷ |dx, 0⟩;
    1 < |dy      ? ⟨0, dy ÷| dy⟩;
                   ⟨0, 0⟩ 
  }
}
Update ← { 
  ⟨dir, 0⟩ F state: state;
  ⟨dir, n⟩ F ⟨head, tail, history⟩:
    new_head ← head +¨ DirVec ⟨dir, n⟩
    new_tail ← new_head UpdateTail tail
    ⟨dx, dy⟩ ← new_head -¨ tail
    new_history ← {
      ⟨new_tail⟩ ⊑∘∊ history ? history;
      ⟨new_tail⟩ ∾ history
    }
    # •Show ⟨new_head, new_tail, n-1⟩
    ⟨dir, n-1⟩ F ⟨new_head, new_tail, new_history⟩
}
•Show ≠2⊑⟨⟨0,0⟩, ⟨0,0⟩, ⟨⟩⟩ Update´ ⌽moves
Update2 ← { 
  ⟨dir, 0⟩ F state: state;
  ⟨dir, n⟩ F ⟨knots, history⟩:
    Propagate ← {
      last F ⟨⟩ : ⟨⟩;
      head ← ⊑ 𝕩 
      tail ← 1↓ 𝕩
      new_head ←𝕨 UpdateTail head
      ⟨new_head⟩∾ new_head Propagate tail
    }
    head ← ⊑ knots
    tail ← 1↓ knots
    new_head ← head +¨ DirVec ⟨dir, n⟩
    new_tail ← new_head Propagate tail
    true_tail ← ⊑⌽new_tail
    new_history ← {
      ⟨true_tail⟩ ⊑∘∊ history ? history;
      ⟨true_tail⟩ ∾ history
    }
    ⟨dir, n-1⟩ F ⟨⟨new_head⟩∾new_tail, new_history⟩
}
•Show ≠1⊑⟨⟨0, 0⟩˙¨↕10, ⟨⟩⟩ Update2´ ⌽moves
