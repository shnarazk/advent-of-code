namespace Vec2

abbrev Vec2 := Int64 × Int64

instance : BEq Vec2 where beq a b := a.1 == b.1 && a.2 == b.2
-- #eval (0, 0) == (1, 0)
instance : ToString Vec2 where toString v := s!"({v.1},{v.2})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec2 where hash a := hash (a.1)o

instance : HAdd Vec2 Vec2 Vec2 where
  hAdd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)

instance : HAdd Vec2 Int64 Vec2 where
  hAdd (v : Vec2) (a : Int64) : Vec2 := (v.1 + a, v.2 + a)

instance : HSub Vec2 Vec2 Vec2 where
  hSub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)

instance : HSub Vec2 Int64 Vec2 where
  hSub (v : Vec2) (a : Int64) : Vec2 := (v.1 - a, v.2 - a)

instance : LT Vec2 where
  lt (a b : Vec2) := a.1 < b.1 ∧ a.2 < b.2

instance instDecidableLtVec2 (a b : Vec2) : Decidable (a < b) := by
  dsimp [instLTVec2]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec2) < ((8, 2) : Vec2)

instance : LE Vec2 where
  le (a b : Vec2) := a.1 ≤ b.1 ∧ a.2 ≤ b.2

instance instDecidableLeVec2 (a b : Vec2) : Decidable (a ≤ b) := by
  dsimp [instLEVec2]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec2) ≤ ((8, 2) : Vec2)

def geZeroAndLe (size pos : Vec2) : Bool := (0, 0) ≤ pos && pos ≤ size

syntax:50 term:51 " ≤₀ " term:50 : term
macro_rules | `($a ≤₀ $b) => `(geZeroAndLe $b $a)

def geZeroAndLt (size pos : Vec2) : Bool := (0, 0) ≤ pos && pos < size

syntax:50 (name := syntaxInfixGeZeroAndLt) term:51 " <₀ " term:50 : term
macro_rules | `($a <₀ $b) => `(geZeroAndLt $b $a)

-- #eval ((0, 0) : Vec2) < (3, 2)
-- #eval geZeroAndLt (5, 5) (3, 2)
-- #eval (3, 2) <₀ (5, 5)

def Vec2.toUInt64 (v : Vec2) : (UInt64 × UInt64) := (v.1.toUInt64, v.2.toUInt64)

end Vec2
