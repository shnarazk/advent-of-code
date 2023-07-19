#!/usr/bin/env cbqn
DecodeSetToken ← {
    ⟨'v', l⟩ F pn: ⟨•BQN 0⊑l, •BQN 4⊑l⟩ SetToken pn;
    i F x: x
}
SetToken ← { ⟨val, idx⟩ F pn:
    fst ← 1⊑idx⊑pn
    {
        fst = ¯∞ ?
            val˙⌾(1⊸⊑idx⊸⊑) pn
        ;
            # •Show "Ready "‿idx
            ⟨mi, ma⟩ ← ⟨fst⌊val, fst⌈val⟩
            (1‿mi‿ma)˙⌾(idx⊸⊑) pn
    }
}
Unpropagated ← {1=0⊑𝕩⊑𝕨} # ∧ (1⊑record ≠ ¯∞) ∧ (2⊑record ≠ ¯∞)

# example ← ⟨
#     "value 5 goes to bot 2"
#     "bot 2 gives low to bot 1 and high to bot 0"
#     "value 3 goes to bot 1"
#     "bot 1 gives low to output 1 and high to bot 0"
#     "bot 0 gives low to output 2 and high to output 0"
#     "value 2 goes to bot 2"
#     ⟩
# •Show ≍⟜(Decode¨) example

Solve ⇐ {env‿part S data :
    ⟨StartsWith,Switch,Tokenize⟩ ← •Import"/util.bqn"∾˜∾env.Var<"BQN_LIB"
    Decode ← {
        l ← Tokenize 𝕩
        Switch ⟨⊑l
            "value" ⋄  { 𝕤⋄ 'v'‿(1↓l)}
            "bot"   ⋄  { 𝕤⋄ 'b'‿(1↓l)}
        ⟩
    }
    Link ← {
        ⟨'b',l⟩ F n : 
            min‿max ← ⟨•BQN 5⊑l,•BQN 10⊑l⟩
            {(4⊑l) StartsWith "out" ? min ↩ ¯1×1+min ; @}
            {(9⊑l) StartsWith "out" ? max ↩ ¯1×1+max ; @}
            min‿max⌾((•BQN ⊑l)⊸⊑)n ;
        i F x       : x
    }
    insts ← ⌽Decode¨data
    network ← (¯∞‿¯∞˙¨↕220)Link´insts
    petri ← (0‿¯∞‿¯∞˙¨↕220)DecodeSetToken´insts
    {1=part ? 
        Propagate ← {F pn:
            len ← ≠pn
            target ← ⊑ (<1)⊒˜(pn⊸Unpropagated)¨↕len
            {
                target<len ?
                    ⟨lo,hi⟩ ← target⊑network
                    ⟨mi,ma⟩ ← 1↓target⊑pn
                    pn ↩ 0˙⌾(⊑target⊸⊑)pn
                    {lo<0 ? @ ; pn ↩ ⟨mi,lo⟩ SetToken pn}
                    {hi<0 ? @ ; pn ↩ ⟨ma,hi⟩ SetToken pn}
                    F pn
                ;
                    pn
            }
        }
        ⊑⊑{17‿61≡1‿2⊸⊏}¨⊸/{⟨1+⊑𝕨, 1⊑𝕩, 2⊑𝕩⟩}`Propagate petri;
     2=part ?
        total ← 1
        Propagate2 ← {F pn :
            len ← ≠pn
            target ← ⊑(<1)⊒˜(pn⊸Unpropagated)¨↕len
            {
                target<len ?
                    ⟨lo,hi⟩ ← target⊑network
                    ⟨mi,ma⟩ ← 1↓target⊑pn
                    pn ↩ 0˙⌾(⊑target⊸⊑)pn
                    {0≤lo ? pn ↩ ⟨mi,lo⟩ SetToken pn ; ¯3≤lo ? total× ↩ mi ; @}
                    {0≤hi ? pn ↩ ⟨ma,hi⟩ SetToken pn ; ¯3≤hi ? total× ↩ ma ; @}
                    F pn
                ;
                    pn
            }
        }
        Propagate2(0‿¯∞‿¯∞˙¨↕220)DecodeSetToken´insts
        total
    }
}
