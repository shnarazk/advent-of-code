Solve ⇐ {env‿part Solve data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  Facets ← {x‿y‿z :
    [⟨x-0.5,y,z⟩,⟨x+0.5,y,z⟩,⟨x,y-0.5,z⟩,⟨x,y+0.5,z⟩,⟨x,y,z-0.5⟩,⟨x,y,z+0.5⟩]
  }
  "≠all" lib.Debug≠ all ← ⥊<˘∾Facets¨lib.ParseInts¨data
  {1=part ? (≠-(2⊸×∘(-○≠⟜⍷)))all ;
   2=part ?
     dup ← (¬∊)⊸/all
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
     dir¯all ← ∾DirectedFacets¨lib.ParseInts¨data
     mask ← dir¯all∊∾Lift¨dup
     "≠surface" lib.Debug≠surface ← (¬mask)/dir¯all
     Propagate ← {
       𝕊 𝕩 : surface 𝕊 𝕩 ;
       set 𝕊 x‿y‿z‿s :
         cands ← ⥊<˘{
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
         ∾((0<≠)⊸↑(∊⟜set)⊸/)¨cands
     }
     "statrt at" lib.Debug 1↑∧surface
     ⟨⟩{
       checked Rec ⟨⟩  : ≠⍷checked ;
       checked Rec new :
         np ← ≠prop ← ⍷∾Propagate¨new
         checked (⍷new⊸∾)↩
         lib.Progress ≠prop ↩ ⍷(¬∊⟜checked˜)⊸/prop
         checked Rec prop
     }1↑∧surface
   ;
     !0
  }
}
