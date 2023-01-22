#!/usr/bin/env cbqn

StartsWith ← { (≠𝕨) < (≠𝕩) ? 0 ; 0 = (<˘(≠𝕩)↕𝕨) ⊑∘⊐⟜< 𝕩 }
Encode ← {
    line ← > 𝕩
    {
        (line StartsWith "forward") ? 'F'‿(•BQN 7↓line);
        (line StartsWith "down"   ) ? 'D'‿(•BQN 5↓line);
        (line StartsWith "up"     ) ? 'U'‿(•BQN 3↓line);
        '?'‿0
    }
}
Part1Move ← { ⟨key, val⟩ F ⟨x, y⟩ :
    {
        'D' = key ? x       ‿ (y+val);
        'U' = key ? x       ‿ (y-val);
        'F' = key ? (x+val) ‿ y;
        key‿val ! 0
    }
}
Part2Move ← {⟨key, val⟩ F ⟨x, y, aim⟩ :
    {
        'D' = key ? x       ‿ y           ‿ (aim+val);
        'U' = key ? x       ‿ y           ‿ (aim-val);
        'F' = key ? (x+val) ‿ (y+aim×val) ‿ aim;
        key‿val ! 0
    }
}

input ← ⟨
    "forward 5",
    "down 5",
    "forward 8",
    "up 3",
    "down 8",
    "forward 2",
⟩

•Show input
# •Show (⊑ input) StartsWith "forward "
orders ← (<Encode)˘ input
•Show orders
•Show ×´ 0‿0 Part1Move´ ⌽ orders
•Show ×´ 0‿0 Part1Move´ ⌽ (<Encode)˘ •FLines "../data/2021/input-day02.txt"
•Show ×´ 2↑ 0‿0‿0 Part2Move´ ⌽ (<Encode)˘ •FLines "../data/2021/input-day02.txt"
