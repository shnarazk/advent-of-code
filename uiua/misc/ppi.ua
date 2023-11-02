# π-calculation in parallel 
# NumThreads ← - 4 NumProcs
# Step ← ×NumThreads 4
# x ← now
# /+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙'+Step+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵'+1_3×4⇡NumThreads
# &p - x now

NumThreads ← 1
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 2
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 3
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 4
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 5
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 6
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now

NumThreads ← 7
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙(+Step)+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵(+1_3)×4⇡NumThreads
&p ⊂ NumThreads - x now
