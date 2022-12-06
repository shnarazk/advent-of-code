#!/usr/bin/env cbqn
⟨ParseInts, DataFile⟩ ← •Import "../lib.bqn"
⟨init, input⟩ ← {
  0 < ≠•args ? ⟨
                ⟨⟨⟩, "NZ","DCM", "P"⟩,
				"data/2022/input-day05-0.txt"
			⟩;
			⟨
				⟨⟨⟩, "GJZ", "CVFWPRLQ", "RGLCMPF", "MHPWBFL", "QVSFCG", "LTQMZJHW", "VBSFH", "SZJF", "TBHFPDCM"⟩,
				"data/2022/input-day05.txt"
			⟩
}
num_stacks ← ¯1+≠init
header_size ← 2+⌈´≠¨ init
lines ← •FLines input DataFile ⟨⟩
"Wrong assumption on num_stacks" ! num_stacks = 4÷˜1+≠⊑ lines
"Wrong assumption on header_size" ! header_size = 1+⊑0⊐˜≠¨ lines
actions ← ParseInts¨ header_size ↓ lines
# •Show ⊑actions

Part1 ← {
	⟨0, from, to⟩ F state: state;
	⟨amount, from, to⟩ F state: {
		stack1 ← from⊑state
		⟨val, dropped⟩ ← (⊑⋈(1⊸↓)) stack1
		stack2 ← to⊑state
		pushed ← (<val)∾stack2
		state ← pushed˙⌾(to⊸⊑) dropped˙⌾(from⊸⊑) state 
		# •Show state
		⟨1-˜amount, from, to⟩ F state
	}
}
•Show (⊑¨1⊸↓) (init Part1´ ⌽actions)
