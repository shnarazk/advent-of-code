Heap ← {𝕤
  l ← ⟨0⟩
  Dump ⇐ { 𝕤 ⋄ l }
  Push ⇐ {
    k ← ≠l
    l ↩ l∾⟨𝕩⟩
    •Show "last index "‿k
    ShiftUp k
  }
  ShiftUp ← {
    𝕊 1: @;
    𝕊 n: {
      r ← 2|n
      m ← 2÷˜n-r
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
    # TODO: use swapping with the last element approarch
    v ← ⊑l
    l ↩ 1↓l
    Shiftdown 1
    v
  }
  ShiftDown ← { 
    ⟨n1, n2⟩ ← ⟨¯1+2⋆𝕩, 2⋆𝕩⟩
    {
      (≠l)<n1 ? @;
      (≠l)=n1 ? ⟨p, c⟩ ← ⟨𝕩⊑l, n1⊑l⟩ ⋄ l ↩ c˙⌾(𝕩⊸⊑) p˙⌾(n1⊸⊑) l; 
        ⟨c1, c2⟩ ← ⟨n1⊑l, n2⊑l⟩
        {
          c1≤c2 ? l ↩ c1˙⌾(𝕩⊸⊑) l ⋄ 𝕊 n1; l ↩ c2˙⌾(𝕩⊸⊑) l ⋄ 𝕊 n2
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
