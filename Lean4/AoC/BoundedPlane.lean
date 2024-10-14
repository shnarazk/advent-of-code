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

example : (Dim2.mk 3 7) * (8 : Int) = Dim2.mk 24 56 := by rfl

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
instance : AddMonoid Dim2 where
  zero := Dim2.mk 0 0
  add := HAdd.hAdd
  add_assoc a b c := by
    simp [HAdd.hAdd]
    constructor
    { exact add_assoc (a.y) (b.y) (c.y) }
    { exact add_assoc (a.x) (b.x) (c.x) }
  zero_add a := by
    simp [HAdd.hAdd]
    sorry
  add_zero a := by
    sorry
  nsmul (n : Nat) (a : Dim2) := Dim2.mk (n * a.y) (n * a.x)
  nsmul_zero := by simp ; rfl
  nsmul_succ := by
    intro n a
    simp [Dim2.mk]
    sorry
-- instance : AddGroup Dim2 where
--  neg a := Dim2.mk (-a.y) (-a.x)
--  zsmul n a := Dim2.mk (n * a.y) (n * a.x)
--  neg_add_cancel a := by
--    simp [HAdd.hAdd, neg_add_cancel]
--    sorry

def area (a : Dim2) : Nat := (a.y * a.x).toNat
example : ((5, 4) : Dim2).area = 20 := by rfl

def double (a : Dim2) : Dim2 := Dim2.mk (2 * a.1) (2 * a.2)

example (y x : Nat) : Dim2.mk (2 * y) (2 * x) = Dim2.double (Dim2.mk y x) := by
  simp [Dim2.mk, Dim2.double]

def index (frame self : Dim2) : Nat :=
  self.y.toNat * frame.x.toNat + self.x.toNat

def index' (frame : Dim2) (n : Nat) : Dim2 :=
  Dim2.mk (n / frame.x) (n % frame.x)

end Dim2

namespace TwoDimentionalVector
open Std.HashMap Dim2

variable (α : Type)

/-
# A Presentation of infinite 2D space
-/
structure Plane (α : Type) [BEq α] [Hashable α] where
  mapping : Std.HashMap Dim2 α
deriving Repr

instance {α : Type} [BEq α] [Hashable α] :
    Inhabited (Plane α) where
  default := Plane.mk Std.HashMap.empty

def Plane.empty {α : Type} [BEq α] [Hashable α]
    (capacity : optParam Nat 8) : Plane α :=
  { mapping := Std.HashMap.empty capacity }

example : (Plane.empty : Plane Nat) = (default : Plane Nat) := by
  simp [default, Plane.empty]

def Plane.get {α : Type} [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (default : α) : α :=
  self.mapping.getD (AsDim2.asDim2 p) (default : α)

def Plane.set {α : Type} [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (a : α) : Plane α :=
  { self with mapping := self.mapping.insert (AsDim2.asDim2 p) a }

def Plane.modify {α : Type} [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (f : α → α) (default : α): Plane α :=
  { self with
    mapping := self.mapping.insert p (f (self.mapping.getD p default)) }

example [BEq α] [Hashable α]
    (p : Plane α) (y x : Nat) (a : α) :
    p.set (Dim2.mk y x) a = p.set (y, x) a := by simp

example [BEq α] [Hashable α]
    (p : Plane α) (q : Dim2) (a default : α) :
      (p.set q a).get q default = a  := by
  simp [Plane.set, AsDim2.asDim2, Plane.get]

/-
# A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`

-/
structure BoundedPlane (α : Type) [BEq α] where
  shape  : Dim2
  vector : Array α
  -- neZero : shape ≠ default ∧ NeZero vector.size
  validShape: 0 ≤ shape
  validArea : shape.area = vector.size
deriving Repr

instance (α : Type) [BEq α] : BEq (BoundedPlane α) where
  beq a b := a.shape == b.shape && a.vector == b.vector

instance [ToString α] [BEq α] : ToString (BoundedPlane α) where
  toString bp := s!"{bp.shape}{toString bp.vector}"

namespace BoundedPlane

/-
- return a new BoundedPlane
-/
def new {α : Type} [BEq α]
    (g : Dim2) (vec : Array α) (h1 : 0 ≤ g) (h2 : g.area = vec.size): BoundedPlane α :=
  BoundedPlane.mk g vec h1 h2

/--
- return a new instance of BoundedPlane by converting from an 2D array
-/
def of2DMatrix {α : Type} [BEq α]
  (a : Array (Array α)) (h w : Nat) : BoundedPlane α :=
  have zero_def : (0 : Dim2) = { y := 0, x := 0 } := by rfl
  match h, w with
  | 0, _ | _, 0 =>
    let d := Dim2.mk 0 0
    have : 0 ≤ d := by rw [zero_def] ; constructor <;> rfl
    BoundedPlane.mk d #[] this (by rfl : d.area = #[].size)
  | _, _ =>
    let v : Array α := a.foldl Array.append #[]
    if hw : h * w = v.size then
      let d := Dim2.mk h w
      have : 0 ≤ d := by rw [zero_def] ; constructor <;> simp
      BoundedPlane.mk (Dim2.mk h w) v this hw
    else
      let d := Dim2.mk 0 0
      have : 0 ≤ d := by rw [zero_def] ; constructor <;> rfl
      BoundedPlane.mk d #[] this (by rfl : d.area = #[].size)

/--
- return the `(i,j)`-th element of Mat1 instance
-/
def get {α : Type} [BEq α]
    (self : BoundedPlane α) (p : Dim2) (default : α) : α :=
  if h : 0 < self.vector.size then
    have : NeZero self.vector.size := by exact NeZero.of_pos h
    self.vector.get (Fin.ofNat' self.vector.size (self.shape.index p))
  else
    default

def validIndex? {α : Type} [BEq α]
    (self : BoundedPlane α) (p : Dim2) : Bool :=
  0 ≤ p.y && p.y < self.shape.y && 0 ≤ p.x && p.x < self.shape.x

/--
- set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def set {α : Type} [BEq α]
    (self : BoundedPlane α) (p : Dim2) (val : α) : BoundedPlane α :=
  let ix := self.shape.index p
  let v := self.vector.set! ix val
  if h : self.shape.area = v.size
    then BoundedPlane.new self.shape v self.validShape h
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
- modify the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def modify {α : Type} [BEq α]
  (self : BoundedPlane α) (p : Dim2) (f : α → α) (default : α) : BoundedPlane α :=
  self.set p <| f <| self.get p default

/--
- search an element that satisfies the predicate and return indices or none
-/
def findIdx? {α : Type} [BEq α] (p : BoundedPlane α) (f : α → Bool) : Option Dim2 :=
  match p.vector.findIdx? f with
  | some i => some (Dim2.mk (i / p.shape.x) (i % p.shape.x))
  | none => none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdx? (· == 6) else none

private partial def findIdxOnSubarray {α : Type} [BEq α]
    (sa : Subarray α) (limit : Fin sa.size) (sub1 : Fin sa.size) (pred : α → Bool)
    : Option Nat :=
  if pred (sa.get limit)
  then some limit
  else
    match (limit : Nat) with
    | 0 => none
    | _ => findIdxOnSubarray sa (limit.sub sub1) sub1 pred

/--
- search an element in a specific row
-/
def findIdxInRow? {α : Type} [BEq α]
    (p : BoundedPlane α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * p.shape.x.toNat
  let t := (i + 1) * p.shape.x.toNat
  let sa := p.vector.toSubarray f t
  if h : sa.size ≠ 0 then
    have : NeZero sa.size := by simp [neZero_iff, h]
    match findIdxOnSubarray sa (Fin.ofNat' sa.size (t - f - 1)) (Fin.ofNat' sa.size 1) pred with
    | some j => some (i, j)
    | none => none
  else
    none

-- #eval if let some y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]] then y.findIdxInRow? 1 (· == 4) else none

def foldl {α β : Type} [BEq α] (self : BoundedPlane α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {α β : Type} [BEq α]
    (self : BoundedPlane α) (f : β → α → β) (init : β) : Array β :=
  Array.range self.shape.y.toNat
    |> .map (fun i =>
      self.vector.toSubarray i (i + self.shape.x.toNat)
        |> Array.ofSubarray
        |>.foldl f init)

def mapRows {α β : Type} [BEq α]
    (self : BoundedPlane α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.shape.x.toNat)
    |> .map (fun i => self.vector.toSubarray i (i + self.shape.x.toNat) |> Array.ofSubarray |> f)

def row {α : Type} [BEq α] (self : BoundedPlane α) (i : Nat) : Subarray α :=
  let j : Nat := i % (self.vector.size % self.shape.x.toNat)
  let f : Nat := j * self.shape.x.toNat
  let t := f + self.shape.x.toNat
  self.vector.toSubarray f t

def column {α : Type} [BEq α] (self : BoundedPlane α) (j : Nat) (default : α) : Array α :=
  Array.range self.shape.y.toNat
    |>.map (fun i ↦ self.get (↑(i, j) : Dim2) default)

def area {α : Type} [BEq α] (self : BoundedPlane α) : Nat :=
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
