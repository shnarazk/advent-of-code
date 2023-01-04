#
# O(log(N)) heap constructed from order function: version 0.2.0
#
# Note
# A heap is created from a comparing _dyadic_ function.
# So if, for example, you want to compare the first elements, use `Over` like:
#
#  H ← (≤○⊑)_to_heap
#
* You can write as follow, but this is more expensive to compare all elements:
#
#  H ← (⊑≤)_to_heap
#
# And you will get a rank error by:
#
#  H ← (≤⊑)_to_heap
#

Parent ← {! 0<𝕩⋄  ¯1+2÷˜(1+𝕩)-2|1+𝕩}
Children ← {⟨¯1+2×˜(1+𝕩),2×˜(1+𝕩)⟩}

_to_heap ⇐ {𝔽_𝕣:
  l ← ⟨⟩
  Ord ← 𝔽
  Dump ⇐ {𝕤 ⋄ l}
  Push ⇐ {k ← ≠l ⋄ l ↩ l∾⟨𝕩⟩ ⋄ ShiftUp k}
  ShiftUp ← {
    𝕊 0: @;
    𝕊 n: {
      m ← Parent n
      ⟨p,c⟩ ← ⟨m⊑l,n⊑l⟩
      {c (Ord○⊑) p ? l ↩ p˙⌾(n⊸⊑)c˙⌾(m⊸⊑)l ⋄ ShiftUp m; @}
    }
  }
  Empty ⇐ { 𝕤
    0=≠l
  }
  Peek ⇐ { 𝕤 ⋄ ⊑⊑l }
  Pop ⇐ { 𝕤
    n ← ¯1+≠l
    ⟨v,u⟩ ← ⟨⊑⊑l,n⊑l⟩
    l ↩ u˙⌾⊑ l ⋄ Shiftdown 0 ⋄ l ↩ n↑l ⋄ v
  }
  ShiftDown ← { 𝕊 m:
    ⟨n1,n2⟩ ← Children m
    {
      (≠l)≤n1 ? @;
      (≠l)=1+n1 ? ⟨p,c⟩ ← ⟨m⊑l,n1⊑l⟩ ⋄ l ↩ p˙⌾(n1⊸⊑)c˙⌾(m⊸⊑)l;
        ⟨p,c1,c2⟩ ← ⟨m⊑l,n1⊑l,n2⊑l⟩
        {c1 (Ord○⊑) c2 ? l ↩ p˙⌾(n1⊸⊑)c1˙⌾(m⊸⊑)l ⋄ ShiftDown n1; l ↩ p˙⌾(n2⊸⊑)c2˙⌾(m⊸⊑)l ⋄ ShiftDown n2}
    }
  }
}

# H ← (⊑≤)_to_heap
# h.Push<⟨1⟩
# h.Push<⟨10⟩
# h.Push<⟨50⟩
# h.Push<⟨4⟩
# h.Push<⟨20⟩
# h.Push<⟨3⟩
# h.Push<⟨8⟩
# h.Push<⟨2⟩
# h.Dump @
# # •Show h.Dump @
# # •Show h.Peek @
# ! ⟨1⟩ ≡ h.Pop @
# ! ⟨2⟩ ≡ h.Pop @
# ! ⟨3⟩ ≡ h.Pop @
# ! ⟨4⟩ ≡ h.Pop @
# ! ⟨8⟩ ≡ h.Pop @
# ! ⟨10⟩ ≡ h.Pop @
# ! ⟨20⟩ ≡ h.Pop @
# ! ⟨50⟩ ≡ h.Pop @
# # •Show h.Dump @

# G ← (⊑≥)_to_heap
# g.Push<⟨1⟩
# g.Push<⟨10⟩
# g.Push<⟨50⟩
# g.Push<⟨4⟩
# g.Push<⟨20⟩
# g.Push<⟨3⟩
# g.Push<⟨8⟩
# g.Push<⟨2⟩
# # •Show g.Dump @
# ! ⟨50⟩ ≡ g.Pop @
# ! ⟨20⟩ ≡ g.Pop @
# ! ⟨10⟩ ≡ g.Pop @
# ! ⟨8⟩ ≡ g.Pop @
# ! ⟨4⟩ ≡ g.Pop @
# ! ⟨3⟩ ≡ g.Pop @
# ! ⟨2⟩ ≡ g.Pop @
# ! ⟨1⟩ ≡ g.Pop @
# # •Show g.Dump @
