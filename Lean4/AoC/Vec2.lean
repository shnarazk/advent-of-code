namespace Vec2

abbrev Vec2 := Int64 × Int64

instance : ToString Vec2 where toString v := s!"({v.1},{v.2})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec2 where hash a := hash (a.1)

instance : HAdd Vec2 Vec2 Vec2 where
  hAdd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)

instance : HAdd Vec2 Int64 Vec2 where
  hAdd (v : Vec2) (a : Int64) : Vec2 := (v.1 + a, v.2 + a)

instance : HSub Vec2 Vec2 Vec2 where
  hSub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)

instance : HSub Vec2 Int64 Vec2 where
  hSub (v : Vec2) (a : Int64) : Vec2 := (v.1 - a, v.2 - a)

/-
instance : LT Vec2 where
  lt (a b : Vec2) := a.1 < b.1 && a.2 < b.2

noncomputable instance instDecidableLtVec2 (a b : Vec2) : Decidable (a < b) := by
  rw [LT.lt]
  sorry

#eval ((0, 0) : Vec2) < ((8, 2) : Vec2)
-/

def contains (size pos : Vec2) : Bool :=
  0 ≤ pos.1 && pos.1 < size.1 && 0 ≤ pos.2 && pos.2 < size.2

end Vec2
