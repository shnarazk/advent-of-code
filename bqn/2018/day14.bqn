Solve ⇐ {env‿part 𝕊 data :
  util‿⟨ref⟩ ← •Import¨"/util.bqn"‿"/ref.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  start ← 3‿7
  # pass_as_arg ← 2 (passing a vanilla list)
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  198.73s user 0.28s system 99% cpu 3:19.20 total
  # pass_as_arg ← 0 (using a global var)
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  0.47s user 0.02s system 98% cpu 0.492 total
  # Comparsion with Bup.Ref
  # pass_as_arg ← 0 (global var)
    # | day 14 |  60 |    0.284 |   11.385 |
  # pass_as_arg ← 1 (Bup.Ref)
    # | day 14 |  60 |    0.320 |   11.996 |
  {
    1=part ?
      Process ← {indexes‿start :
        (0=1000⊸|)◶⟨⊢,util.Progress⟩≠start.ref
        ∾start._apply util.Digits+´ current ← indexes⊏start.ref
        ⟨(≠start.ref)|indexes+1+current,start⟩
      }
      10↑data↓{(1⊑𝕩).ref}Process•_while_{(10+data)>≠(1⊑𝕩).ref}⟨0‿1,Ref start⟩
      ;
    2=part ?
      l ← 1+ k ← ≠ data util.Digits ↩
      !(¯2⊑data)≠⊑ d ← ⋈¯1⊑data
      Process ← {indexes‿ref‿check :
        (0=10000⊸|)◶⟨⊢,util.Progress⟩≠ref.ref
        ∾ref._apply dd ← util.Digits+´ current ← indexes⊏ref.ref
        ⟨(≠ref.ref)|indexes+1+current,ref,dd∊d⟩
      }
      Shape ← {(≠(1⊑𝕩).ref)-((1‿0⊸≢∨1‿1⊸≢)2⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {
         𝕨 𝕊 0‿0 : 1 ;
         𝕨 𝕊 0‿1 : data≢(-k)↑𝕨.ref ;
         𝕨 𝕊 1‿x : data≢¯1↓(-l)↑𝕨.ref ;
         𝕨 𝕊 ⟨0⟩ : 1 ;
         𝕨 𝕊 ⟨1⟩ : data≢(-k)↑𝕨.ref
      }
      Shape Process•_while_(Check´1⊸↓)⟨0‿1,Ref start,⟨0⟩⟩
    # (0=pass_as_arg)∧1=part ?
    #   Process ← {𝕊 indexes :
    #     (0=1000⊸|)◶⟨⊢,util.Progress⟩≠start
    #     start ∾ ↩ util.Digits+´ current ← indexes⊏start
    #     (≠start)|indexes+1+current
    #   }
    #   Process•_while_{𝕤 ⋄ (10+data)>≠start}0‿1
    #   10↑data↓start
    #   ;
    # (2=pass_as_arg)∧1=part ?
    #   Process ← {indexes‿start :
    #     (0=1000⊸|)◶⟨⊢,util.Progress⟩≠start
    #     dd ← util.Digits+´ current ← indexes⊏start
    #     start ∾⟜dd ↩
    #     ⟨(≠start)|indexes+1+current,start⟩
    #   }
    #   10↑data↓1⊑Process•_while_{(10+data)>≠1⊑𝕩}⟨0‿1,start⟩
    #   ;
    # (0=pass_as_arg)∧2=part ?
    #   l ← 1+ k ← ≠ data util.Digits ↩
    #   !(¯2⊑data)≠⊑ d ← ⋈¯1⊑data
    #   Process ← {indexes‿to_check :
    #     (0=10000⊸|)◶⟨⊢,util.Progress⟩≠start
    #     dd ← util.Digits+´ current ← indexes⊏start
    #     start ∾⟜dd ↩
    #     ⟨(≠start)|indexes+1+current,dd∊d⟩
    #   }
    #   Shape ← {(≠start)-((1‿0⊸≢∨1‿1⊸≢)1⊑𝕩)◶⟨⊢,1⊸+⟩k}
    #   Check ← {
    #      0‿0 : 1 ;
    #      0‿1 : data≢(-k)↑start ;
    #      1‿x : data≢¯1↓(-l)↑start ;
    #      ⟨0⟩ : 1 ;
    #      ⟨1⟩ : data≢(-k)↑start
    #   }
    #   Shape Process•_while_(Check 1⊸⊑)⟨0‿1,⟨0⟩⟩
    #   ;
    # (2=pass_as_arg)∧2=part ?
    #   "not implemented"!0
    #   ;
  }
}
