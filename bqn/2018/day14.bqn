Solve ⇐ {env‿part 𝕊 data :
  util‿⟨ref⟩ ← •Import¨"/util.bqn"‿"/ref.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  record ← 3‿7
  pass_as_arg ← 1
  # pass_as_arg ← 1
    # nix$ time 2018 14 1
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  198.73s user 0.28s system 99% cpu 3:19.20 total
  # pass_as_arg ← 0
    # nix$ time 2018 14 1
    #  ⍟ Year 2018 Day 14 → data/2018/input-day14.txt
    # Part1: ⟨ 1 1 5 0 5 1 1 3 8 2 ⟩
    # 2018 14 1  0.47s user 0.02s system 98% cpu 0.492 total
  {
    pass_as_arg∧1=part ?
      util.Debug data
      # record ← Ref 3‿7
      # Process ← {𝕊 indexes :
      #   (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record.ref
      #   ∾ record._apply util.Digits+´ current ← indexes⊏record.ref
      #   (≠record.ref)|indexes+1+current
      # }
      # Process•_while_{𝕤 ⋄ (10+data)>≠record.ref}0‿1
      # 10↑data↓record.ref
      Process ← {indexes‿record :
        (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record.ref
        ∾record._apply util.Digits+´ current ← indexes⊏record.ref
        ⟨(≠record.ref)|indexes+1+current,record⟩
      }
      10↑data↓{(1⊑𝕩).ref}Process•_while_{(10+data)>≠(1⊑𝕩).ref}⟨0‿1,Ref 3‿7⟩
      # Process ← {indexes‿record :
      #   (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record
      #   dd ← util.Digits+´ current ← indexes⊏record
      #   record ∾⟜dd ↩
      #   ⟨(≠record)|indexes+1+current,record⟩
      # }
      # 10↑data↓1⊑Process•_while_{(10+data)>≠1⊑𝕩}⟨0‿1,3‿7⟩
      ;
    pass_as_arg ?
      l ← 1+ k ← ≠ data util.Digits ↩
      d ← ⋈¯1⊑data
      !(⊑d)≠¯2⊑data
      Process ← {indexes‿to_check :
        (0=10000⊸|)◶⟨⊢,util.Progress⟩≠record
        dd ← util.Digits+´ current ← indexes⊏record
        record ∾⟜dd ↩
        ⟨(≠record)|indexes+1+current,dd∊d⟩
      }
      Shape ← {(≠record)-((1‿0⊸≢∨1‿1⊸≢)1⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {n‿check :
        {
           0‿0 : 1 ;
           0‿1 : data≢(-k)↑record ;
           1‿x : data≢¯1↓(-l)↑record ;
           ⟨0⟩ : 1 ;
           ⟨1⟩ : data≢(-k)↑record
        }check
      }
      Shape Process•_while_ Check ⟨0‿1,⟨0⟩⟩
      ;
    1=part ?
      Process ← {𝕊 indexes :
        (0=1000⊸|)◶⟨⊢,util.Progress⟩≠record
        dd ← util.Digits+´ current ← indexes⊏record
        record ∾⟜dd ↩
        (≠record)|indexes+1+current
      }
      Process•_while_{𝕤 ⋄ (10+data)>≠record}0‿1
      10↑data↓record
    ;
      l ← 1+ k ← ≠ data util.Digits ↩
      d ← ⋈¯1⊑data
      !(⊑d)≠¯2⊑data
      Process ← {indexes‿to_check :
        (0=10000⊸|)◶⟨⊢,util.Progress⟩≠record
        dd ← util.Digits+´ current ← indexes⊏record
        record ∾⟜dd ↩
        ⟨(≠record)|indexes+1+current,dd∊d⟩
      }
      Shape ← {(≠record)-((1‿0⊸≢∨1‿1⊸≢)1⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {n‿check :
        {
           0‿0 : 1 ;
           0‿1 : data≢(-k)↑record ;
           1‿x : data≢¯1↓(-l)↑record ;
           ⟨0⟩ : 1 ;
           ⟨1⟩ : data≢(-k)↑record
        }check
      }
      Shape Process•_while_ Check ⟨0‿1,⟨0⟩⟩
  }
}
