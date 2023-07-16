Part1Move ← {
    'D'‿val F x‿y : x      ‿(y+val) ;
    'U'‿val F x‿y : x      ‿(y-val) ;
    'F'‿val F x‿y : (x+val)‿y
}
Part2Move ← {
    'D'‿val F x‿y‿aim : x      ‿y          ‿(aim+val) ;
    'U'‿val F x‿y‿aim : x      ‿y          ‿(aim-val) ;
    'F'‿val F x‿y‿aim : (x+val)‿(y+aim×val)‿aim
}

Solve ⇐ {env‿part 𝕊 data :
    lib ← •Import"/util.bqn"∾˜∾env.Var<"BQN_LIB"
    Encode ← {
        𝕩 lib.StartsWith "forward" ? 'F'‿(•BQN 7↓𝕩) ;
        𝕩 lib.StartsWith "down"    ? 'D'‿(•BQN 5↓𝕩) ;
        𝕩 lib.StartsWith "up"      ? 'U'‿(•BQN 3↓𝕩) ;
                                     𝕩!0
    }
    {
        1=part ? ×´     0‿0 Part1Move´⌽Encode¨data ;
        2=part ? ×´ 2↑0‿0‿0 Part2Move´⌽Encode¨data ;
                 !0
    }
}
