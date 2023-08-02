#!/usr/bin/env cbqn
numKinds ← 2
numStates ← 4⋆1+2×numKinds
# Element layout:
# - cost (0<)
MakeState ← ∞`(↕(4⊸⋆(1⊸+(2⊸×))))
states ← MakeState numKinds
start ← 0
ToIndex ← (+⟜(4⊸×))´⌽
ToState ← {
    (¯1+¯2×numKinds)↑ {
        F 0 : ⟨0⟩ ;
        F n : {(F(n-𝕩)÷4)∾𝕩} 4|n
    } 𝕩
}
# Return 1 if 𝕩 is safe for all microtips
IsSafe ← {
         F state : ⌊´state⊸(F˜)¨↕numKinds ;
    kind F state :
        floor ← (2+2×kind)⊑state
        generator ← 1+2×kind
        (floor=generator⊑state)∨(∧´{floor ≠ 𝕩⊑state}¨1+2×↕numKinds)
}
# Returns the set of objects which you can move with elevator from the current floor.
NextObjectsStates ← {F state :
    Mask ← {
        (¯2×numKinds)↑ {
            F 0 : ⟨0⟩ ;
            F n : {(F(n-𝕩)÷2)∾𝕩} 2|n
        } 𝕩
    }
    objects ← {(⊑𝕩)⊸=¨1↓𝕩}state
    cands ← ({⌈´𝕩 ∧ objects=𝕩}¨)⊸/⍷(objects×Mask)¨↕2⋆2×numKinds
    {2 ≥ +´}¨⊸/cands
    {s ← +´𝕩⋄ (1≤s)∧(s≤2)}¨⊸/cands
}
# Returns the set of valid and safe states transited from the current state.
NextStates ← {F state :
    elevator ← ⊑state
    objects ← 1↓state
    w ← NextObjectsStates state
    nextFloors ← {(0≤𝕩)∧(𝕩<4)}¨⊸/⟨¯1+elevator,1+elevator⟩
    # •Show ⥊ nextFloors {𝕨∾ 𝕨×𝕩}⌜ w
    cands ← ⥊ nextFloors{𝕨∾((¬𝕩)×objects)+𝕨×𝕩}⌜w
    # •Show IsSafe¨ cands
    results ← IsSafe¨⊸/cands
    # •Show ⟨>≠cands," => ",>≠results⟩
    results
}
SeekStep ← {cost F ii :
    init ← ToState ii
    {
        # •Show ⟨"expand",ii,ii⊑states⟩
        nexts ← NextStates init
        # •Show ≠ nexts
        {
            i ← ToIndex 𝕩
            ∞ = i⊑states ?
                states ↩ cost˙⌾(i⊸⊑)states
                # •Show ⟨"update",i,i⊑states⟩
            ; @
        }¨ nexts
    }
}
Seek ← { 𝕤
    len ← ≠states
    indexes ← ↕len
    # cost ← 0
    p ← 0
    ⊑{𝕊 cost :
        # •Show "cost"‿cost‿(p÷len)
        {cost=𝕩⊑states ? (1+cost) SeekStep 𝕩 ⋄ p + ↩ 1 ; @}¨indexes
        1+cost
    }•_while_{𝕤⋄ ∞=¯1⊑states}0
}
# Part 1 Description: #####################################
# - 0: a hydrogen M, a lithium M.
# - 1: a hydrogen G.
# - 2: a lithium G.
# - 3: nothing relevant.
# Encode: hydrogen, lithium
# naive coding:
#     0‿0‿0‿0‿0
#     0‿0‿0‿1‿0
#     0‿1‿0‿0‿0
#     1‿0‿1‿0‿1
numKinds ↩ 2
states ↩ MakeState numKinds
start_state ← ⟨0, 1, 0, 2, 0⟩
•Show (<"IsSafe")∾IsSafe start_state
start ↩ ToIndex start_state
states ↩ 0˙⌾(start⊸⊑)states
•Show {(ToState 𝕩)‿𝕩‿(ToIndex ToState 𝕩)}start
"Fail to build the 1-arrow"!(ToState∘ToIndex)⊸(∧´=)start_state
# •Show NextStates ToState start
•Show Seek @
# •Show ToState 15
# •Show 15⊑states
# •Show ToState 975
# •Show 975⊑states
# •Show ToState 327
# •Show 327⊑states
# •Show ToState 847
# •Show 847⊑states
# Part 1: #####################################
# - 0: a strontium G, a strontium M, a plutonium G, a plutonium M.
# - 1: a thulium G, a ruthenium G, a ruthenium M, a curium G, a curium M.
# - 2: a thulium M.
# - 3: nothing relevant.
# Encode: strontium, plutonium, thulium, ruthenium, curium
# numKinds ↩ 5
# states ↩ MakeState numKinds
# start ↩ ToIndex ⟨0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1⟩
# states ↩ 0˙⌾(start⊸⊑) states
# •Show Seek @
# Part 2: #####################################
numKinds ↩ 1
states ↩ MakeState numKinds
start ↩ ToIndex⟨0,0,0⟩
states ↩ 0˙⌾(start⊸⊑)states
•Show Seek @
numKinds ↩ 2
states ↩ MakeState numKinds
start ↩ ToIndex⟨0,0,0,0,0⟩
states ↩ 0˙⌾(start⊸⊑)states
•Show Seek @
numKinds ↩ 3
states ↩ MakeState numKinds
start ↩ ToIndex⟨0,0,0,0,0,0,0⟩
states ↩ 0˙⌾(start⊸⊑)states
•Show Seek @
numKinds ↩ 4
states ↩ MakeState numKinds
start ↩ ToIndex⟨0,0,0,0,0,0,0,0,0⟩
states ↩ 0˙⌾(start⊸⊑)states
•Show Seek@
