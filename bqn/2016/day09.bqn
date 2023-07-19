#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1⊸↓∘↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜@)˝v}}
⟨ParseInts,StartsWith⟩ ← •Import"/util.bqn"∾˜∾env.Var<"BQN_LIB"

Decode ← {F x :
    lpi‿rpi ← x ⊐ '('‿')'
    {
        lpi = rpi ? ⟨rpi, ""⟩ ;
        ⟨n, m⟩ ← ParseInts lpi↓rpi↑x
        post ← ⊑Decode(1+n+rpi)↓x
        ⟨post+lpi+n×m,(1+n+rpi)↓x⟩
    }
}
example ← ⟨
    0‿""
    6‿"ADVENT"
    7‿"A(1x5)BC"
    9‿"(3x3)XYZ"
    11‿"A(2x2)BCD(2x2)EFG"
    6‿"(6x1)(1x3)A"
    18‿"X(8x2)(3x3)ABCY"
⟩
•Show ≍⟜(Decode∘(1⊸⊑)¨)example
# Part 1: #####################################
Decode1 ← {F x :
    lpi‿rpi ← x⊐'('‿')'
    {
        lpi = rpi ? rpi ;
        ⟨n,m⟩ ← ParseInts lpi↓rpi↑x
        post ← F(1+n+rpi)↓x
        post+lpi+n×m
    }
}
# Part 2: #####################################
Decode2 ← {
    F x : 1 F x ;
  k F x :
    lpi‿rpi ← x⊐'('‿')'
    {
        lpi = rpi ? k×rpi ;
        ⟨n, m⟩ ← ParseInts lpi↓rpi↑x
        target ← (k×m) F n↑(1+rpi)↓x
        post ← k F (1+n+rpi)↓x
        post+target
    }
}
Solve ⇐ {env‿part 𝕊 data :
   {1=part ? +´Decode1¨⥊data ;
    2=part ? +´Decode2¨⥊data
   }
}