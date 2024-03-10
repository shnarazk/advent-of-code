# Experimental!

# Ackermann(0, n)    = n+1
# Ackermann(m+1,0)   = Ackermann(m,1)
# Ackermann(m+1,n+1) = Ackermann(m,Ackermann(m+1,n))

Ackermann ← ↬(|2 (1;|+1;||2 ↫ ⊃(-1∘)(1;;)||2 ↫ ⊃(-1)(|2 ↫ ⊙(-1))) +×2∩(≠0),,)
⍤:≍,1 Ackermann 0 0
⍤:≍,2 Ackermann 0 1
⍤:≍,3 Ackermann 0 2
⍤:≍,2 Ackermann 1 0
⍤:≍,3 Ackermann 1 1
⍤:≍,4 Ackermann 1 2
⍤:≍,3 Ackermann 2 0
⍤:≍,5 Ackermann 2 1
⍤:≍,7 Ackermann 2 2
⍤:≍,5 Ackermann 3 0
⍤:≍,13 Ackermann 3 1
⍤:≍,29 Ackermann 3 2
⍤:≍,61 Ackermann 3 3
⍤:≍,125 Ackermann 3 4
&p Ackermann 3 5
