#!/usr/bin/env BQNLIBDIR=/.config/bqn BQNLIB=/lib.bqn cbqn
env ← {v←(⊑'='⊐˜⊢)⊸(↑⋈(1⊸↓↓))¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env",Var⇐{(@∾˜1⊑¨v)⊏˜⊐⟜𝕩˜⊑¨v}}
⟨Min, Max, StartsWith, Switch, Tokenize⟩ ← •Import∾env.Var"HOME"‿"BQNLIBDIR"‿"BQNLIB"
Decode ← {
    l ← Tokenize 𝕩
    Switch ⟨⊑l
        "value" ⋄  { 𝕤⋄ 'v'‿(1↓l)}
        "bot"   ⋄  { 𝕤⋄ 'b'‿(1↓l)}
    ⟩
}
# Part 1: #####################################
Link ← {
    ⟨'b', l⟩ F n: {
        ⟨min, max⟩ ← ⟨•BQN 5⊑l, •BQN 10⊑l⟩
        { (4⊑l) StartsWith "out" ? min ↩ ¯1×1+min;@ }
        { (9⊑l) StartsWith "out" ? max ↩ ¯1×1+max;@ }
        min‿max⌾((•BQN ⊑l)⊸⊑) n
    };
    i F x: x
}
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
            ⟨mi, ma⟩ ← ⟨fst Min val, fst Max val⟩
            (1‿mi‿ma)˙⌾(idx⊸⊑) pn
    }
}
Unpropagated ← { pn F idx:
    record ← idx⊑pn
    (0⊑record = 1) # ∧ (1⊑record ≠ ¯∞) ∧ (2⊑record ≠ ¯∞)
}
Propagate ← { F pn:
    len ← ≠pn
    target ← ⊑ (<1)⊒˜(pn⊸Unpropagated)¨ ↕len
    {
        (target < len) ?
            # •Show "Fire "‿target
            ⟨lo, hi⟩ ← target⊑network
            ⟨mi, ma⟩ ← 1↓target⊑pn
            pn ↩ 0˙⌾(⊑target⊸⊑) pn
            { lo < 0 ? @; pn ↩ ⟨mi, lo⟩ SetToken pn }
            { hi < 0 ? @; pn ↩ ⟨ma, hi⟩ SetToken pn }
            F pn
        ;
            pn
    }
}

example ← ⟨
    "value 5 goes to bot 2"
    "bot 2 gives low to bot 1 and high to bot 0"
    "value 3 goes to bot 1"
    "bot 1 gives low to output 1 and high to bot 0"
    "bot 0 gives low to output 2 and high to output 0"
    "value 2 goes to bot 2"
    ⟩
•Show ≍⟜(Decode¨) example
data ← ⥊ •FLines "../../data/2016/input-day10.txt"
•Show ≍⟜(Decode¨) 2↑ data
insts ← ⌽ Decode¨ data
network ← (¯∞‿¯∞˙¨ ↕220) Link´ insts
petri ← (0‿¯∞‿¯∞˙¨ ↕220) DecodeSetToken´ insts
•Show network
•Show petri
petri ↩ Propagate petri
•Show petri
•Show petri ⊐ ⟨0‿17‿61⟩
# petri2 ← ⟨0, 0, 0⟩ {⟨1+⊑𝕨, "1⊑𝕩", 2⊑𝕨⟩}` petri
petri ↩ {⟨1+⊑𝕨, 1⊑𝕩, 2⊑𝕩⟩}` petri
•Show petri
# Part 2: #####################################
total ← 1
Propagate2 ← { F pn:
    len ← ≠pn
    target ← ⊑ (<1)⊒˜(pn⊸Unpropagated)¨ ↕len
    {
        (target < len) ?
            # •Show "Fire "‿target
            ⟨lo, hi⟩ ← target⊑network
            ⟨mi, ma⟩ ← 1↓target⊑pn
            pn ↩ 0˙⌾(⊑target⊸⊑) pn
            {
                0  ≤ lo ? pn ↩ ⟨mi, lo⟩ SetToken pn;
                ¯3 ≤ lo ? total×↩mi;
                @
            }
            {
                0  ≤ hi ? pn ↩ ⟨ma, hi⟩ SetToken pn;
                ¯3 ≤ hi ? total×↩ma;
                @
            }
            F pn
        ;
            pn
    }
}
petri2 ← Propagate2 (0‿¯∞‿¯∞˙¨ ↕220) DecodeSetToken´ insts
•Show total
