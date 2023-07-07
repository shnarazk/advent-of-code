lib ← •Import "../lib.bqn"

Solve ⇐ { part Solve data:
  { 1=part ?
      Facets ← {x‿y‿z:
        [
          ⟨x-0.5,y,z⟩,⟨x+0.5,y,z⟩
          ⟨x,y-0.5,z⟩,⟨x,y+0.5,z⟩
          ⟨x,y,z-0.5⟩,⟨x,y,z+0.5⟩
        ]
      }
      "fs" lib.Debug ≠fs ← ⥊<˘∾Facets¨ cubes ← lib.ParseInts¨data
      # (1⊸=·+´˘(∧´=)⌜˜)⊸/ fs out of memory
      (≠-(2⊸×∘(-○≠⟜⍷)))fs
      # if you need not only the number of facets but also facets themselves.
      # "lib.Debug ≠envelop ← {1=+´∧´¨fs=<𝕩}¨⊸/ fs
      ;
    2=part ?
      # we need 'direction'
      Facets ← ∾¨⟜(1+↕6)<
      # lib.Debug Facets 0‿0‿0
      "5↑all" lib.Debug 5↑all ← ∾Facets¨ lib.ParseInts¨data
      Mirrored ← {a𝕊b:
        {
          ⟨ 0, 0, 1⟩: 1‿2≡a∾○(3⊸⊑)b;
          ⟨ 0, 0,¯1⟩: 2‿1≡a∾○(3⊸⊑)b;
          ⟨ 0, 1, 0⟩: 3‿4≡a∾○(3⊸⊑)b;
          ⟨ 0,¯1, 0⟩: 4‿3≡a∾○(3⊸⊑)b;
          ⟨ 1, 0, 0⟩: 5‿6≡a∾○(3⊸⊑)b;
          ⟨¯1, 0, 0⟩: 6‿5≡a∾○(3⊸⊑)b;
                𝕩: 0
        } b-○(3⊸↑)a
      }
      # {∨´checked Mirrored¨ <cand ? checked; checked ∾ cand}
      ! ⟨0,0,0,1⟩Mirrored⟨0,0,1,2⟩
      "matrix1" lib.Debug ×˜≠all
      # "matrix" +˝ Mirrored⌜˜all  ## out of memory
      "facets" lib.Debug ≠fs ← ⟨⟩{cand𝕊checked:
        matches ← checked Mirrored¨<cand
        {∨´matches ? (¬matches)/checked ; checked∾<cand}
      }´all
        # (<cand)∾⍟(¬∨´checked Mirrored¨<cand)checked}´all
      "5↑fs" lib.Debug 5↑fs
      Adjacent ← {a𝕊b:
        { 1‿¯1‿0≡b-○(3⊸↑)a ? lib.Debug a‿b; @}
        {
          𝕊 ⟨ 0, 0, 1⟩: (a=○(3⊸⊑)b)∧1≠⌊2÷⁼3⊑a;
          𝕊 ⟨ 0, 0,¯1⟩: (a=○(3⊸⊑)b)∧1≠⌊2÷⁼3⊑a;
          𝕊 ⟨ 0, 1, 0⟩: (a=○(3⊸⊑)b)∧2≠⌊2÷⁼3⊑a;
          𝕊 ⟨ 0,¯1, 0⟩: (a=○(3⊸⊑)b)∧2≠⌊2÷⁼3⊑a;
          𝕊 ⟨ 1, 0, 0⟩: (a=○(3⊸⊑)b)∧3≠⌊2÷⁼3⊑a;
          𝕊 ⟨¯1, 0, 0⟩: (a=○(3⊸⊑)b)∧3≠⌊2÷⁼3⊑a;

          𝕊 ⟨ 0, 1, 1⟩: 3‿2≡a∾○(3⊸⊑)b;
          𝕊 ⟨ 0, 1,¯1⟩: 4‿2≡a∾○(3⊸⊑)b;
          𝕊 ⟨ 0,¯1, 1⟩: 3‿1≡a∾○(3⊸⊑)b;
          𝕊 ⟨ 0,¯1,¯1⟩: 4‿1≡a∾○(3⊸⊑)b;

          𝕊 ⟨ 1, 0, 1⟩: 5‿2≡a∾○(3⊸⊑)b;
          𝕊 ⟨ 1, 0,¯1⟩: 5‿1≡a∾○(3⊸⊑)b;
          𝕊 ⟨¯1, 0, 1⟩: 5‿1≡a∾○(3⊸⊑)b;
          𝕊 ⟨¯1, 0,¯1⟩: 6‿1≡a∾○(3⊸⊑)b;

          𝕊 ⟨ 1, 1, 0⟩: 5‿4≡a∾○(3⊸⊑)b;
          𝕊 ⟨ 1,¯1, 0⟩: 5‿3≡a∾○(3⊸⊑)b; # !!
          𝕊 ⟨¯1, 1, 0⟩: 6‿4≡a∾○(3⊸⊑)b;
          𝕊 ⟨¯1,¯1, 0⟩: 6‿3≡a∾○(3⊸⊑)b;
          𝕊          𝕩: 0
        } b-○(3⊸↑)a
      }
      ! 0‿0‿0‿5 Adjacent 1‿¯1‿0‿3
      "outers" lib.Debug ≠out ← ⟨⟩ {
        checked Rec ⟨⟩‿remain: checked;
        checked Rec new‿remain:
          "≠remain" lib.Debug ≠remain
          match ← {∨´new Adjacent¨<𝕩}¨remain
          "new" lib.Debug match
          (checked∾new) Rec match ⊔ remain;
        checked Rec new: checked∾new
      } 1(↑⋈↓)fs
    ;
      ⟨1 Solve data, 2 Solve data⟩
  }
}
