Solve ⇐ {env‿part 𝕊 data :
  util‿⟨ref⟩ ← •Import¨"/util.bqn"‿"/ref.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  record ← 3‿7
  pass_as_arg ← 1    # is as fast as 0
  # pass_as_arg ← 2
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  198.73s user 0.28s system 99% cpu 3:19.20 total
  # pass_as_arg ← 0
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  0.47s user 0.02s system 98% cpu 0.492 total
  # Comparsion with Bup.Ref
  # pass_as_arg ← 0 (global var)
    # | day 14 |  60 |    0.284 |   11.385 |
  # pass_as_arg ← 1 (Bup.Ref)
    # | day 14 |  60 |    0.320 |   11.996 |
  {
    (0=pass_as_arg)∧1=part ?
      Process ← {𝕊 indexes :
        (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record
        record ∾ ↩ util.Digits+´ current ← indexes⊏record
        (≠record)|indexes+1+current
      }
      Process•_while_{𝕤 ⋄ (10+data)>≠record}0‿1
      10↑data↓record
      ;
    (1=pass_as_arg)∧1=part ?
      Process ← {indexes‿record :
        (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record.ref
        ∾record._apply util.Digits+´ current ← indexes⊏record.ref
        ⟨(≠record.ref)|indexes+1+current,record⟩
      }
      10↑data↓{(1⊑𝕩).ref}Process•_while_{(10+data)>≠(1⊑𝕩).ref}⟨0‿1,Ref 3‿7⟩
      ;
    # (2=pass_as_arg)∧1=part ?
    #   Process ← {indexes‿record :
    #     (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record
    #     dd ← util.Digits+´ current ← indexes⊏record
    #     record ∾⟜dd ↩
    #     ⟨(≠record)|indexes+1+current,record⟩
    #   }
    #   10↑data↓1⊑Process•_while_{(10+data)>≠1⊑𝕩}⟨0‿1,3‿7⟩
    #   ;
    (0=pass_as_arg)∧2=part ?
      l ← 1+ k ← ≠ data util.Digits ↩
      !(¯2⊑data)≠⊑ d ← ⋈¯1⊑data
      Process ← {indexes‿to_check :
        (0=10000⊸|)◶⟨⊢,util.Progress⟩≠record
        dd ← util.Digits+´ current ← indexes⊏record
        record ∾⟜dd ↩
        ⟨(≠record)|indexes+1+current,dd∊d⟩
      }
      Shape ← {(≠record)-((1‿0⊸≢∨1‿1⊸≢)1⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {
         0‿0 : 1 ;
         0‿1 : data≢(-k)↑record ;
         1‿x : data≢¯1↓(-l)↑record ;
         ⟨0⟩ : 1 ;
         ⟨1⟩ : data≢(-k)↑record
      }
      Shape Process•_while_(Check 1⊸⊑)⟨0‿1,⟨0⟩⟩
      ;
    (1=pass_as_arg)∧2=part ?
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
      Shape Process•_while_(Check´1⊸↓) ⟨0‿1,Ref record,⟨0⟩⟩
    # (2=pass_as_arg)∧2=part ?
    #   "not implemented"!0
    #   ;
  }
}
