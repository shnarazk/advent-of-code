lib ← •Import "../lib.bqn"

Solve ⇐ { part Solve data:
  Facets ← {x‿y‿z :
    [⟨x-0.5,y,z⟩,⟨x+0.5,y,z⟩,⟨x,y-0.5,z⟩,⟨x,y+0.5,z⟩,⟨x,y,z-0.5⟩,⟨x,y,z+0.5⟩]
  }
  "≠all" lib.Debug≠ all ← ⥊<˘∾Facets¨lib.ParseInts¨data
  { 1=part ? (≠-(2⊸×∘(-○≠⟜⍷)))all ;
    2=part ?
      # {
      #   "all facets" lib.Debug a ← ⟨⟨0,0⟩,⟨1,0⟩,⟨0,0⟩,⟨2,0⟩,⟨2,0⟩⟩
      #   "a's non-firsts mask" lib.Debug m ← ¬∊a
      #   "a's non-firsts" lib.Debug c ← m/a
      #   "remains" lib.Debug (¬a∊c)/a
      #   !0
      # }
      "5↑dup faces" lib.Debug 5↑dup ← (¬∊)⊸/all
      # Change to a directed space
      Lift ← {𝕊 x‿y‿z :
        {
          x≠⌊x ? ⟨x+0.5,y,z,3⟩‿⟨x-0.5,y,z,2⟩ ;
          y≠⌊y ? ⟨x,y+0.5,z,5⟩‿⟨x,y-0.5,z,4⟩ ;
          z≠⌊z ? ⟨x,y,z+0.5,7⟩‿⟨x,y,z-0.5,6⟩ ;
          !0
        }
      }
      DirectedFacets ← ∾¨⟜(2+↕6)<
      "5↑dir¯all" lib.Debug 5↑dir¯all ← ∾DirectedFacets¨ lib.ParseInts¨data
      "≠mask" lib.Debug +´mask ← dir¯all∊∾Lift¨ dup
      "≠surface" lib.Debug ≠surface ← (¬mask)/dir¯all
      Propagate ← {x‿y‿z‿s 𝕊 set :
        # {1‿¯1‿0≡b-○(3⊸↑)a ? lib.Debug a‿b; @}
        cands ← {
          𝕊 2 : [
            ⟨⟨x+1,y+1,z  ,5⟩,⟨x  ,y+1,z  ,2⟩,⟨x  ,y  ,z  ,4⟩⟩
            ⟨⟨x+1,y-1,z  ,4⟩,⟨x  ,y-1,z  ,2⟩,⟨x  ,y  ,z  ,5⟩⟩
            ⟨⟨x+1,y  ,z+1,7⟩,⟨x  ,y  ,z+1,2⟩,⟨x  ,y  ,z  ,6⟩⟩
            ⟨⟨x+1,y  ,z-1,6⟩,⟨x  ,y  ,z-1,2⟩,⟨x  ,y  ,z  ,7⟩⟩
          ] ;
          𝕊 3 : [
            ⟨⟨x-1,y+1,z  ,5⟩,⟨x  ,y+1,z  ,3⟩,⟨x  ,y  ,z  ,4⟩⟩
            ⟨⟨x-1,y-1,z  ,4⟩,⟨x  ,y-1,z  ,3⟩,⟨x  ,y  ,z  ,5⟩⟩
            ⟨⟨x-1,y  ,z+1,7⟩,⟨x  ,y  ,z+1,3⟩,⟨x  ,y  ,z  ,6⟩⟩
            ⟨⟨x-1,y  ,z-1,6⟩,⟨x  ,y  ,z-1,3⟩,⟨x  ,y  ,z  ,7⟩⟩
          ] ;
          𝕊 4 : [
            ⟨⟨x+1,y+1,z  ,3⟩,⟨x+1,y  ,z  ,4⟩,⟨x  ,y  ,z  ,2⟩⟩
            ⟨⟨x-1,y+1,z  ,2⟩,⟨x-1,y  ,z  ,4⟩,⟨x  ,y  ,z  ,3⟩⟩
            ⟨⟨x  ,y+1,z+1,7⟩,⟨x  ,y  ,z+1,4⟩,⟨x  ,y  ,z  ,6⟩⟩
            ⟨⟨x  ,y+1,z-1,6⟩,⟨x  ,y  ,z-1,4⟩,⟨x  ,y  ,z  ,7⟩⟩
          ] ;
          𝕊 5 : [
            ⟨⟨x+1,y-1,z  ,3⟩,⟨x+1,y  ,z  ,5⟩,⟨x  ,y  ,z  ,2⟩⟩
            ⟨⟨x-1,y-1,z  ,2⟩,⟨x-1,y  ,z  ,5⟩,⟨x  ,y  ,z  ,3⟩⟩
            ⟨⟨x  ,y-1,z+1,7⟩,⟨x  ,y  ,z+1,5⟩,⟨x  ,y  ,z  ,6⟩⟩
            ⟨⟨x  ,y-1,z-1,6⟩,⟨x  ,y  ,z-1,5⟩,⟨x  ,y  ,z  ,7⟩⟩
          ] ;
          𝕊 6 : [
            ⟨⟨x+1,y  ,z+1,3⟩,⟨x+1,y  ,z  ,6⟩,⟨x  ,y  ,z  ,2⟩⟩
            ⟨⟨x-1,y  ,z+1,2⟩,⟨x-1,y  ,z  ,6⟩,⟨x  ,y  ,z  ,3⟩⟩
            ⟨⟨x  ,y+1,z+1,5⟩,⟨x  ,y+1,z  ,6⟩,⟨x  ,y  ,z  ,4⟩⟩
            ⟨⟨x  ,y-1,z+1,4⟩,⟨x  ,y-1,z  ,6⟩,⟨x  ,y  ,z  ,5⟩⟩
          ] ;
          𝕊 7 : [
            ⟨⟨x+1,y  ,z-1,3⟩,⟨x+1,y  ,z  ,7⟩,⟨x  ,y  ,z  ,2⟩⟩
            ⟨⟨x-1,y  ,z-1,2⟩,⟨x-1,y  ,z  ,7⟩,⟨x  ,y  ,z  ,3⟩⟩
            ⟨⟨x  ,y+1,z-1,5⟩,⟨x  ,y+1,z  ,7⟩,⟨x  ,y  ,z  ,4⟩⟩
            ⟨⟨x  ,y-1,z-1,4⟩,⟨x  ,y-1,z  ,7⟩,⟨x  ,y  ,z  ,5⟩⟩
          ] ;
          𝕊 n : !0
        } s
        # lib.Debug cands
        # "cands" lib.Debug cands
        # "4 dirs" lib.Debug (∊⟜set)˘cands
        # "4 dirs" lib.Debug ∾(<(∊⟜set)⊸/)˘cands
        # ⥊((0⊸<≠)⊸↑(∊⟜set)⊸/)˘cands
        ∾(<(∊⟜set)⊸/)˘cands
      }
      "outers" lib.Debug 0{
        checked Rec remain‿⟨⟩  : checked;
        checked Rec remain‿new :
          "≠prop" lib.Debug ≠prop ← ⍷∾Propagate⟜remain˜¨new
          # "new furfaces" lib.Debug prop ← ⍷ ∾remain Propagate¨ new
          # "5↑r" lib.Debug r ← (⊣remain∊○(<¨)prop)/remain
          "≠r" lib.Debug ≠r ← (¬remain∊prop)/remain
          "≠remain → ≠new + ≠remain" lib.Debug⟨≠remain,≠prop,≠r⟩
          ! (≠remain) = r +○≠ prop
          (checked+≠new) Rec r‿prop;
        checked Rec remain     : checked
      }1(↓⋈↑)∧surface
    ;
      ⟨1 Solve data, 2 Solve data⟩
  }
}
