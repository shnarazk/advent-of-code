#!/usr/bin/env cbqn
lib ← •Import "../lib.bqn"
lib.term.Println nest_in‿nest_ut ← @⊸-¨ '['‿']'
problems ← (2⊸↑˘)∘‿3⥊∾⟜ ⟨⟨⟩⟩ •FLines "data/2022/input-day13.txt" lib.DataFile •args
"problem string" lib.Debug ⊑problems
Reform ← { ch 𝕊 out‿digits:
  {
    ch=',' ? { 0<≠digits ? (out∾(•BQN digits))‿⟨⟩; out‿⟨⟩ };
    ch='[' ? { 0<≠digits ? (out∾⟨•BQN digits,'['⟩)‿⟨⟩; (out∾('['))‿⟨⟩ };
    ch=']' ? { 0<≠digits ? (out∾⟨•BQN digits,']'⟩)‿⟨⟩; (out∾(']'))‿⟨⟩ };
    out‿(digits∾ch)
  }
}
Enlist ← { token 𝕊 stack:
  {
      # "enlist.token" lib.Debug token "enlist.stack" lib.Debug stack
      token='[' ? stack∾⟨⟨⟩⟩;
      (token=']')∧(1=≠stack) ? stack;
      token=']' ? last ← ¯1⊑stack⋄ (∾⟜⟨last⟩)⌾(¯1⊸⊑) ¯1↓stack;
      (∾⟜⟨token⟩)⌾(¯1⊸⊑) stack
  }
}
problems { ⊑ ⟨⟩ Enlist´⌽ ⊑(⟨⟩‿⟨⟩) Reform´ ⌽𝕩 }¨˘ ↩
"problem listed" lib.Debug ⊑problems
InOrder ← {
  w‿x ← ⟨⊑𝕨, ⊑𝕩⟩
  {
    𝕨=⟨⟩ ? 1;
    𝕩=⟨⟩ ? ¯1;

    # If both values are lists,
    (x∊⟨nest_in,nest_ut⟩)∧(w∊⟨nest_in,nest_ut⟩) ? {
      x_head‿x_tail ← @
      w_head‿w_tail ← @
      bool ← w_head InOrder x_head
      { 1=|bool ? bool; w_tail InOrder x_tail } 
    };

    # If both values are intergers,
    (¬x∊⟨nest_in,nest_ut⟩)∧(¬w∊⟨nest_in,nest_ut⟩) ? { w<⊑x ? 1; x<⊑𝕨 ? ¯1; 𝕨 InOrder○(1⊸↓) 𝕩 };
 
    (x∊⟨nest_in,nest_ut⟩) ? { w<⊑x ? 1; x<⊑𝕨 ? ¯1; 𝕨 InOrder○(1⊸↓) 𝕩 }
  }
}
