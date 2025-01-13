import Mathlib.Tactic.Coe
namespace Vec2

abbrev Vec₂ := Int64 × Int64

instance : BEq Vec₂ where beq a b := a.1 == b.1 && a.2 == b.2
-- #eval (0, 0) == (1, 0)
instance : ToString Vec₂ where toString v := s!"({v.1},{v.2})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec₂ where hash a := hash (a.1)o

instance : HAdd Vec₂ Vec₂ Vec₂ where
  hAdd (a b : Vec₂) : Vec₂ := (a.1 + b.1, a.2 + b.2)

instance : HAdd Vec₂ Int64 Vec₂ where
  hAdd (v : Vec₂) (a : Int64) : Vec₂ := (v.1 + a, v.2 + a)

instance : HSub Vec₂ Vec₂ Vec₂ where
  hSub (a b : Vec₂) : Vec₂ := (a.1 - b.1, a.2 - b.2)

instance : HSub Vec₂ Int64 Vec₂ where
  hSub (v : Vec₂) (a : Int64) : Vec₂ := (v.1 - a, v.2 - a)

instance : LT Vec₂ where
  lt (a b : Vec₂) := a.1 < b.1 ∧ a.2 < b.2

instance instDecidableLtVec₂ (a b : Vec₂) : Decidable (a < b) := by
  dsimp [instLTVec₂]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec₂) < ((8, 2) : Vec₂)

instance : LE Vec₂ where
  le (a b : Vec₂) := a.1 ≤ b.1 ∧ a.2 ≤ b.2

instance instDecidableLeVec₂ (a b : Vec₂) : Decidable (a ≤ b) := by
  dsimp [instLEVec₂]
  exact instDecidableAnd

-- #eval ((0, 0) : Vec₂) ≤ ((8, 2) : Vec₂)

def geZeroAndLe (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos ≤ size

syntax:50 term:51 " ≤₀ " term:50 : term
macro_rules | `($a ≤₀ $b) => `(geZeroAndLe $b $a)

def geZeroAndLt (size pos : Vec₂) : Bool := (0, 0) ≤ pos && pos < size

syntax:50 (name := syntaxInfixGeZeroAndLt) term:51 " <₀ " term:50 : term
macro_rules | `($a <₀ $b) => `(geZeroAndLt $b $a)

-- #eval ((0, 0) : Vec₂) < (3, 2)
-- #eval geZeroAndLt (5, 5) (3, 2)
-- #eval (3, 2) <₀ (5, 5)

def Vec₂.toUInt64 (v : Vec₂) : (UInt64 × UInt64) := (v.1.toUInt64, v.2.toUInt64)

end Vec2

open Vec2

/--
  A valid index in 2D space.
-/
def Idx₂ := { v : Vec₂ // 0 ≤ v.1 ∧ 0 ≤ v.2 }

instance : Coe Idx₂ Vec₂ where coe v := v.1

def v : Vec₂ := (1, 1)
def d : Idx₂ := ⟨(1, 1), by exact ⟨rfl, rfl⟩⟩

#check ((↑ d) : Vec₂)
#check ((↑ d) : Idx₂)

def w : Vec₂ := (-1, -1)
#eval (↑ w)
