-- import Init.Data.Array.Subarray
import mathlib.Tactic
import Std.Data.HashMap

/-
# An index to point a posiition in an infinite 2D space
-/
structure Dim2 where
  y : Int
  x : Int
deriving Repr
instance : BEq Dim2 where
  beq a b := a.y == b.y && a.x == b.x
instance : Hashable Dim2 where
  hash a := hash (a.y, a.x)

instance : Coe (Nat × Nat) Dim2 where coe p := Dim2.mk ↑p.1 ↑p.2
instance : Coe (Int × Int) Dim2 where coe p := Dim2.mk p.1 p.2
instance : Inhabited Dim2 where default := Dim2.mk 0 0
instance : ToString Dim2 where toString s := s!"2D({s.1}, {s.2})"
instance : LawfulBEq Dim2 where
  eq_of_beq {a b} (h : a.y == b.y && a.x == b.x):= by
    cases a; cases b
    simp at h
    simp
    exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable Dim2 where
  hash_eq := by
    intro a b H
    cases a; cases b
    simp at H
    simp [H]

instance : EquivBEq Dim2 where
  symm := by intro a b h ; exact BEq.symm h
  trans:= by intro a b h ; exact PartialEquivBEq.trans
  refl := by intro a ; exact beq_iff_eq.mpr rfl

instance : HAdd Dim2 Dim2 Dim2 where
  hAdd (a b : Dim2) := Dim2.mk (a.y + b.y) (a.x + b.x)
instance : HAdd Dim2 Int Dim2 where
  hAdd (a : Dim2) (c : Int) := Dim2.mk (a.y + c) (a.x + c)
instance : HAdd Int Dim2 Dim2 where
  hAdd (c : Int) (a : Dim2)  := Dim2.mk (a.y + c) (a.x + c)
instance : HSub Dim2 Dim2 Dim2 where
  hSub (a b : Dim2) := Dim2.mk (a.y - b.y) (a.x - b.x)
instance : HSub Dim2 Int Dim2 where
  hSub (a : Dim2) (c : Int) := Dim2.mk (a.y - c) (a.x - c)
instance : HSub Int Dim2 Dim2 where
  hSub (c : Int) (a : Dim2)  := Dim2.mk (a.y - c) (a.x - c)
instance : HMul Dim2 Int Dim2 where
  hMul (a : Dim2) (c : Int) := Dim2.mk (a.y * c) (a.x * c)
instance : HDiv Dim2 Int Dim2 where
  hDiv (a : Dim2) (c : Int) := Dim2.mk (a.y / c) (a.x / c)

private def Dim2.lt (a b : Dim2) := a.1 < b.1 ∧ a.2 < b.2
instance : LT Dim2 where lt := Dim2.lt

private def Dim2.le (a b : Dim2) := a.1 ≤ b.1 ∧ a.2 ≤ b.2
instance : LE Dim2 where le := Dim2.le

example : Dim2.mk 3 (-2) = ({ x := -2, y := 3 } : Dim2) := by rfl
example : ((3, 5) : Dim2) = Dim2.mk 3 5 := by rfl
example : (((3 : Int), (5 : Int)) : Dim2) = Dim2.mk 3 5 := by rfl
example : ((-2, -2) : Dim2) < ((5, 4) : Dim2) := by
  simp
  constructor <;> simp
example : ((-2, (4 : Int)) : Dim2) ≤ ((5, 4) : Dim2) := by
  simp
  constructor <;> simp

class AsDim2 (α : Type) where
  asDim2 : α → Dim2

instance : AsDim2 Dim2 where asDim2 := (·)
instance : AsDim2 (Int × Int) where asDim2 := Coe.coe
instance : AsDim2 (Nat × Nat) where asDim2 := Coe.coe

namespace Dim2

def area (a : Dim2) : Nat := (a.y * a.x).toNat
example : ((5, 4) : Dim2).area = 20 := by rfl

def double (a : Dim2) : Dim2 := Dim2.mk (2 * a.1) (2 * a.2)

example (y x : Nat) : Dim2.mk (2 * y) (2 * x) = Dim2.double (Dim2.mk y x) := by
  simp [Dim2.mk, Dim2.double]

end Dim2

namespace TwoDimentionalVector
open Std.HashMap Dim2

variable (α : Type)

/-
# A Presentation of infinite 2D space
-/
structure Plane (α : Type) [BEq α] [Hashable α] [Inhabited α] where
  mapping : Std.HashMap Dim2 α
deriving Repr

/-
instance (α : Type) [BEq α] [Hashable α] [Inhabited α] [LE α] [LE (Dim2 × α)]
    : BEq (Plane α) where
    beq a b := BEq.beq a.mapping.toArray b.mapping.toArray
-/

instance {α : Type} [BEq α] [Hashable α] [Inhabited α] :
    Inhabited (Plane α) where
  default := Plane.mk Std.HashMap.empty

def Plane.empty {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (capacity : optParam Nat 8) : Plane α :=
  { mapping := Std.HashMap.empty capacity }

example : (Plane.empty : Plane Nat) = (default : Plane Nat) := by
  simp [default, Plane.empty]

def Plane.get {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (self : Plane α) (p : Dim2) : α :=
  self.mapping.getD (AsDim2.asDim2 p) (default : α)

def Plane.set {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (self : Plane α) (p : Dim2) (a : α) : Plane α :=
  { self with mapping := self.mapping.insert (AsDim2.asDim2 p) a }

def Plane.modify {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (self : Plane α) (p : Dim2) (f : α → α) : Plane α :=
  { self with mapping := self.mapping.insert p (f (self.mapping.get! p)) }

example [BEq α] [Hashable α] [Inhabited α]
    (p : Plane α) (y x : Nat) (a : α) :
    p.set (Dim2.mk y x) a = p.set (y, x) a := by simp

example [BEq α] [Hashable α] [Inhabited α]
    (p : Plane α) (q : Dim2) (a : α) : (p.set q a).get q = a  := by
  simp [default, Plane.set, AsDim2.asDim2, Plane.get]


/-
# A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`

-/
structure BoundedPlane (α : Type) [BEq α] [Inhabited α] where
  shape  : Dim2
  vector : Array α
  -- neZero : shape ≠ default ∧ NeZero vector.size
  validShape : shape.area = vector.size
deriving Repr

instance (α : Type) [BEq α] [Inhabited α]: BEq (BoundedPlane α) where
  beq a b := a.shape == b.shape && a.vector == b.vector

instance [ToString α] [BEq α] [Inhabited α] : ToString (BoundedPlane α) where
  toString bp := s!"{bp.shape}{toString bp.vector}"

namespace BoundedPlane

/-
return a new BoundedPlane
-/
def new {α : Type} [BEq α] [Inhabited α]
    (g : Dim2) (vec : Array α) (h : g.area = vec.size): BoundedPlane α :=
  BoundedPlane.mk g vec h

/--
return an optional new instance of Mat1 of an 2D array
-/
def of2DMatrix {α : Type} [BEq α] [Inhabited α]
  (a : Array (Array α)) (h w : Nat) : BoundedPlane α :=
  match h, w with
  | 0, _ | _, 0 =>
    let d := Dim2.mk 0 0
    BoundedPlane.mk d #[] (by rfl : d.area = #[].size)
  | _, _ =>
    let v : Array α := a.foldl Array.append #[]
    if hw : h * w = v.size then
      BoundedPlane.mk (Dim2.mk h w) v hw
    else
      let d := Dim2.mk 0 0
      BoundedPlane.mk d #[] (by rfl : d.area = #[].size)

/--
return the `(i,j)`-th element of Mat1 instance
-/
def get {α : Type} [BEq α] [Inhabited α]
    (self : BoundedPlane α) (i j : Nat) : α :=
  if h : 0 < self.vector.size then
    have : NeZero self.vector.size := by exact NeZero.of_pos h
    self.vector.get (Fin.ofNat' self.vector.size (i * self.shape.x.toNat + j))
  else
    default

def validIndex? {α : Type} [BEq α] [Inhabited α]
    (self : BoundedPlane α) (i j : Nat) : Bool :=
  0 ≤ i && i < self.shape.y && 0 ≤ j && j < self.shape.x

def getD {α : Type} [BEq α] [Inhabited α] (self : BoundedPlane α) (i j : Nat) : α :=
 if self.validIndex? i j then self.get i j else default

/--
set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def set {α : Type} [BEq α] [Inhabited α]
    (self : BoundedPlane α) (i j : Nat) (val : α) : BoundedPlane α :=
  let ix := i * self.shape.x.toNat + j
  let v := self.vector.set! ix val
  if h : self.shape.area = v.size
    then BoundedPlane.new self.shape v h
    else self

-- def x := new #[true, false, true, false] 2
-- def y := of2DMatrix #[#[1,2,3], #[4,5,6]]

-- #eval x
-- #check x
-- #eval y
-- #check y
-- #check get

-- #eval get x 0 0
-- #eval get y 0 1

/--
modify the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def modify {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i j : Nat) (f : α → α) : Mat1 α :=
  let ix := i * self.width + j
  let v := self.vector.modify ix f
  if h : v.size ≠ 0
  then
    have : NeZero v.size := by simp [neZero_iff, h]
    ({width := self.width, vector := v, neZero := this } : Mat1 α)
  else self

/--
search an element that satisfies the predicate and return indices or none
-/
def findIdx? {α : Type} [BEq α] [Inhabited α] (mat : Mat1 α) (f : α → Bool) : Option (Nat × Nat) :=
  match mat.vector.findIdx? f with
  | some i => some (i / mat.width, i % mat.width)
  | none => none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdx? (· == 6) else none

private partial def findIdxOnSubarray {α : Type} [BEq α] [Inhabited α]
    (sa : Subarray α) (limit : Fin sa.size) (sub1 : Fin sa.size) (pred : α → Bool)
    : Option Nat :=
  if pred (sa.get limit)
  then some limit
  else
    match (limit : Nat) with
    | 0 => none
    | _ => findIdxOnSubarray sa (limit.sub sub1) sub1 pred

/--
search an element in a specific row
-/
def findIdxInRow? {α : Type} [BEq α] [Inhabited α]
    (mat : Mat1 α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * mat.width
  let t := (i + 1) * mat.width
  let sa := mat.vector.toSubarray f t
  if h : sa.size ≠ 0
  then
    have : NeZero sa.size := by simp [neZero_iff, h]
    match findIdxOnSubarray sa (Fin.ofNat' sa.size (t - f - 1)) (Fin.ofNat' sa.size 1) pred with
    | some j => some (i, j)
    | none => none
  else none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdxInRow? 1 (· == 4) else none

def foldl {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {α : Type} [BEq α] [Inhabited α]
    (self : Mat1 α) (f : β → α → β) (init : β ): Array β :=
  Array.range (self.vector.size / self.width)
    |> .map (fun i => self.vector.toSubarray i (i + self.width)
      |> Array.ofSubarray
      |>.foldl f init)

def mapRows {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.width)
    |> .map (fun i => self.vector.toSubarray i (i + self.width) |> Array.ofSubarray |> f)

def row {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i : Nat) : Subarray α :=
  let j := i % (self.vector.size % self.width)
  let f := j * self.width
  let t := f + self.width
  self.vector.toSubarray f t

def column {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i : Nat) : Array α :=
  Array.range (self.vector.size / self.width) |> .map (self.get · i)

-- def shape {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) : Nat × Nat :=
--   (self.vector.size / self.width, self.width)

def area {α : Type} [BEq α] [Inhabited α] (self : BoundedPlane α) : Nat :=
  self.shape.area

end BoundedPlane

-- def x := Mat1.new #[true, false, true, false] 2
-- def y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]]

-- #eval x
-- #check x
-- #eval y
-- #check y
-- #check get

-- #eval x.get 0 0
-- #eval y.get 0 1
-- #eval y.get 100 100

-- #eval x.set 0 0 false
-- #eval y.set 1 1 10000
