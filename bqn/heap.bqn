Parent ← { ! 0 < 𝕩⋄  ¯1+2÷˜(1+𝕩)-2|1+𝕩 }   
Children ← { ⟨¯1+2×˜(1+𝕩), 2×˜(1+𝕩)⟩ }

Heap ← {𝕤
  l ← ⟨⟩
  Dump ⇐ { 𝕤 ⋄ l }
  Push ⇐ {
    k ← ≠l
    l ↩ l∾⟨𝕩⟩
    •Show "last index "‿k
    ShiftUp k
  }
  ShiftUp ← {
    𝕊 0: @;
    𝕊 n: {
      m ← Parent n
      ⟨p, c⟩ ← ⟨m⊑l, n⊑l⟩
      •Show "ShiftUp to "‿⟨m, p, c, c ≤ p⟩
      {
        c ≤ p ?
          l ↩ p˙⌾(n⊸⊑) c˙⌾(m⊸⊑) l
          ShiftUp m;
        @
      } 
    }
  }
  Pop ⇐ { 𝕤
    n ← ¯1+≠l
    ⟨v,u⟩ ← ⟨⊑l,n⊑l⟩
    l ↩ u˙⌾⊑ l
    Shiftdown 0
    l ↩ n↑l
    •Show "popped"‿l
    v
  }
  ShiftDown ← { 𝕊 m: 
    # ⟨n1, n2⟩ ← ⟨¯1+2⋆𝕩, 2⋆𝕩⟩
    ⟨n1, n2⟩ ← Children m
    {
      (≠l)≤n1 ? •Show " - case0" ⋄ @;
      (≠l)=1+n1 ? •Show " - case1" ⋄ ⟨p, c⟩ ← ⟨m⊑l, n1⊑l⟩ ⋄ l ↩ p˙⌾(n1⊸⊑) c˙⌾(m⊸⊑) l; 
        ⟨p, c1, c2⟩ ← ⟨m⊑l, n1⊑l, n2⊑l⟩
        {
          c1≤c2 ? l ↩ p˙⌾(n1⊸⊑) c1˙⌾(m⊸⊑) l ⋄ ShiftDown n1; l ↩ p˙⌾(n2⊸⊑) c2˙⌾(m⊸⊑) l ⋄ ShiftDown n2
        }
    }
  }
}

h ← Heap @
•Show h.Dump @
h.Push 1
h.Push 10
h.Push 50
h.Push 4
h.Push 20
h.Push 3
h.Push 8
h.Push 2
•Show h.Dump @
! 1 = h.Pop @
•Show h.Dump @
! 2 = h.Pop @
! 3 = h.Pop @
! 4 = h.Pop @
! 8 = h.Pop @
•Show h.Dump @
! 10 = h.Pop @
! 20 = h.Pop @
! 50 = h.Pop @
•Show h.Dump @



