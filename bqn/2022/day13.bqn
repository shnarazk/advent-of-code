#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lib.term.Println nest_in‿nest_ut ← @⊸-¨ '['‿']'
problems ← (2⊸↑˘)∘‿3⥊∾⟜ ⟨⟨⟩⟩ •FLines "data/2022/input-day13.txt" lib.DataFile •args
•Show 10↑problems
Reform ← { ch 𝕊 out‿digits:
  {
    ch=',' ? { 0<≠digits ? (out∾(•BQN digits))‿⟨⟩; out‿⟨⟩ };
    ch='[' ? { 0<≠digits ? (out∾⟨•BQN digits,nest_in⟩)‿⟨⟩; (out∾(nest_in))‿⟨⟩ };
    ch=']' ? { 0<≠digits ? (out∾⟨•BQN digits,nest_ut⟩)‿⟨⟩; (out∾(nest_ut))‿⟨⟩ };
    out‿(digits∾ch)
  }
}
lib.color.blue lib.term.Println problems {⊑(⟨⟩‿⟨⟩) Reform´ ⌽𝕩 }¨˘ ↩
•Show 10↑problems
