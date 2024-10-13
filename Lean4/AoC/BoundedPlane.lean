import Init.Data.Array.Subarray

/-
 Index to designate a point in infinite 2D space
-/
structure Dim2 where
  y : Int
  x : Int
deriving BEq, Hashable, Repr

instance : Coe (Nat × Nat) Dim2 where coe p := Dim2.mk ↑p.1 ↑p.2
instance : Coe (Int × Int) Dim2 where coe p := Dim2.mk p.1 p.2
instance : Inhabited Dim2 where default := Dim2.mk 0 0
instance : ToString Dim2 where toString s := s!"2D({s.1}, {s.2})"

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

example : Dim2.mk 3 (-2) = ({ x := -2, y := 3 } : Dim2) := by rfl
example : ((3, 5) : Dim2) = Dim2.mk 3 5 := by rfl
example : (((3 : Int), (5 : Int)) : Dim2) = Dim2.mk 3 5 := by rfl
example : ((-2, -2) : Dim2) < ((5, 4) : Dim2) := by
  simp
  constructor <;> simp

namespace Dim2

def area (a : Dim2) : Nat := (a.y * a.x).toNat
example : ((5, 4) : Dim2).area = 20 := by rfl

def double (a : Dim2) : Dim2 := Dim2.mk (2 * a.1) (2 * a.2)

example (y x : Nat) : Dim2.mk (2 * y) (2 * x) = Dim2.double (Dim2.mk y x) := by
  simp [Dim2.mk, Dim2.double]

end Dim2

namespace TwoDimentionalVector

structure BoundedPlane (α : Type) [BEq α] [Inhabited α] where
  shape  : Dim2
  vector : Array α
  neZero : shape ≠ default ∧ NeZero vector.size
  validShape : shape.area = vector.size
deriving Repr

instance [ToString α] [BEq α] [Inhabited α] : ToString (BoundedPlane α) where
  toString bp := s!"{bp.shape}{toString bp.vector}"

namespace BoundedPlane
/--
return an optional new instance of Mat1 of an array
-/
def new {α : Type} [BEq α] [Inhabited α] (vec : Array α) (w : Nat) : Option (Mat1 α) :=
  if h : vec.size ≠ 0
  then
    have : NeZero vec.size := by simp [neZero_iff, h]
    ({width := w, vector := vec, neZero := this } : Mat1 α) |> some
  else none

/--
return an optional new instacne of Mat1 of an 2D array
-/
def of2DMatrix {α : Type} [BEq α] [Inhabited α] (m : Array (Array α)) : Option (Mat1 α) :=
  new (m.foldl Array.append #[]) (m.getD 1 #[]).size

/--
return the `(i,j)`-th element of Mat1 instance
-/
def get {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i j : Nat) : α :=
  self.vector.get (@Fin.ofNat' self.vector.size self.neZero (i * self.width + j))

def validIndex? {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i j : Nat) : Bool :=
  0 < i && i < self.width && 0 < j && j * self.width < self.vector.size

def get? {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i j : Nat) : Option α :=
 if self.validIndex? i j then self.get i j |> some else none

/--
set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def set {α : Type} [BEq α] [Inhabited α] (self : Mat1 α) (i j : Nat) (val : α) : Mat1 α :=
  let ix := i * self.width + j
  let v := self.vector.set! ix val
  if h : v.size ≠ 0 then
    have : NeZero v.size := by simp [neZero_iff, h]
    { self with vector := v, neZero := this }
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
