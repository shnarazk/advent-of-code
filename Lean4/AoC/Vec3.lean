module

public import Std.Data.HashMap

@[expose] public section

namespace Dim3

variable {α β γ : Type}

/-- 3D vector: `Int × Int` -/
structure Vec₃ where
  z : Int
  y : Int
  x : Int
deriving BEq, Hashable, Repr

-- instance : BEq Vec₃ where beq a b := a.z == b.z && a.2 == b.2
-- #eval (0, 0) == (1, 0)
instance : ToString Vec₃ where toString v := s!"({v.z},{v.y},{v.x})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec₃ where hash a := hash (a.1)o

instance : HAdd Vec₃ Vec₃ Vec₃ where
  hAdd (a b : Vec₃) : Vec₃ := Vec₃.mk (a.z + b.z) (a.y + b.y) (a.x + b.x)

instance : HAdd Vec₃ Int Vec₃ where
  hAdd (v : Vec₃) (a : Int) : Vec₃ := Vec₃.mk (v.z + a) (v.y + a) (v.x + a)

instance : HSub Vec₃ Vec₃ Vec₃ where
  hSub (a b : Vec₃) : Vec₃ := Vec₃.mk (a.z - b.z) (a.y - b.y) (a.x - b.x)

instance : HSub Vec₃ Int Vec₃ where
  hSub (v : Vec₃) (a : Int) : Vec₃ := Vec₃.mk (v.z - a) (v.y - a) (v.x - a)

-- /-- One of definitions of LT on Vec₃ -/
-- instance : LT Vec₃ where
--   lt (a b : Vec₃) := a.1 < b.1 ∧ a.2 < b.2

-- instance instDecidableLtVec₃ (a b : Vec₃) : Decidable (a < b) := by
--   dsimp [instLTVec₃]
--   exact instDecidableAnd

-- #eval ((0, 0) : Vec₃) < ((8, 2) : Vec₃)

-- instance : LE Vec₃ where
--   le (a b : Vec₃) := a.1 ≤ b.1 ∧ a.2 ≤ b.2

-- instance instDecidableLeVec₃ (a b : Vec₃) : Decidable (a ≤ b) := by
--   dsimp [instLEVec₃]
--   exact instDecidableAnd

-- #eval ((0, 0) : Vec₃) ≤ ((8, 2) : Vec₃)

-- /-- return `(0, 0) ≤ pos ∧ ≤ size` -/
-- def geZeroAndLe (size pos : Vec₃) : Bool := (0, 0) ≤ pos && pos ≤ size

-- /-- return `(0, 0) ≤ pos ∧ < size` -/
-- def geZeroAndLt (size pos : Vec₃) : Bool := (0, 0) ≤ pos && pos < size

-- /-- Subtype of `Vec₃` as valid index for `Rect`. -/
-- def Idx₃ := { v : Vec₃ // (0, 0) ≤ v }
-- deriving BEq, Hashable, Repr

-- instance : ToString Idx₃ where toString v := toString v.val
-- instance : Coe Idx₃ Vec₃ where coe v := v.1
-- instance : Coe Idx₃ (Nat × Nat) where coe v := (v.1.1.toNat, v.1.2.toNat)
-- instance : Coe (Nat × Nat) Idx₃ where coe v :=
--   ⟨
--     (((↑ v.1) : Int), ((↑ v.2) : Int)),
--     by
--       constructor <;> { simp }
--   ⟩
-- -- def v : Vec₃ := (1, 1)
-- -- def v : Idx₃ := (1, 1)
-- -- def d : Idx₃ := ⟨(1, 1), by exact ⟨rfl, rfl⟩⟩
-- -- #check ((↑ d) : Vec₃)
-- -- #check ((↑ d) : Idx₃)
-- -- def w : Vec₃ := (-1, -1)
-- -- #eval (↑ w)

-- -- namespace Idx₃

-- def Idx₃.fst (i : Idx₃) : Int := i.1.fst
-- def Idx₃.snd (i : Idx₃) : Int := i.1.snd

end Dim3
