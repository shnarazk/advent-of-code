import Init.Data.Array.Subarray

structure Mat1 (α : Type) [Inhabited α] where
  width  : Nat
  vector : Array α
deriving Repr

instance [ToString α] [Inhabited α] : ToString (Mat1 α) where
  toString m := s!"{m.width}{toString m.vector}"

namespace Mat1
/--
return a new instance of Mat1 of an array
-/
def new {α : Type} [Inhabited α] (vec : Array α) (w : Nat) : Mat1 α :=
  ({width := w, vector := vec} : Mat1 α)

/--
return a new instacne of Mat1 of an 2D array
-/
def of2DMatrix {α : Type} [Inhabited α] (m : Array (Array α)) : Mat1 α :=
  ({width := (m.getD 1 #[]).size, vector := m.foldl Array.append #[]} : Mat1 α)

/--
return the `(i,j)`-th element of Mat1 instance
-/
def get {α : Type} [Inhabited α] (mat : Mat1 α) (i j : Nat) : α :=
  let ix := i * mat.width + j
  if h : mat.vector.size > 0
  then mat.vector.get (Fin.ofNat' ix h)
  else (default : α)

/--
set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def set {α : Type} [Inhabited α] (mat : Mat1 α) (i j : Nat) (val : α) : Mat1 α :=
  let ix := i * mat.width + j
  if h : mat.vector.size > 0
  then { mat with vector := mat.vector.set (Fin.ofNat' ix h) val}
  else mat

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
def modify {α : Type} [Inhabited α] (mat : Mat1 α) (i j : Nat) (f : α → α) : Mat1 α :=
  let ix := i * mat.width + j
  if h : mat.vector.size > 0
  then { mat with vector := mat.vector.modify (Fin.ofNat' ix h) f}
  else mat

/--
search an element that satisfies the predicate and return indices or none
-/
def findIdx? {α : Type} [Inhabited α] [BEq α] (mat : Mat1 α) (f : α → Bool) : Option (Nat × Nat) :=
  match mat.vector.findIdx? f with
  | some i => some (i / mat.width, i % mat.width)
  | none => none

def y := Mat1.of2DMatrix #[#[1,2,3], #[4,5,6]]
#eval y.findIdx? (· == 6)

private partial def findIdxOnSubarray {α : Type} [Inhabited α] [BEq α]
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
def findIdxInRow? {α : Type} [Inhabited α] [BEq α]
    (mat : Mat1 α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
  let f := i * mat.width
  let t := (i + 1) * mat.width
  let sa := mat.vector.toSubarray f t
  if h : sa.size > 0
  then
    match findIdxOnSubarray sa (Fin.ofNat' (t - f - 1) h) (Fin.ofNat' 1 h) pred with
    | some j => some (i, j)
    | none => none
  else none

#eval y.findIdxInRow? 1 (· == 4)

def foldl {α : Type} [Inhabited α] [BEq α] (self : Mat1 α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {α : Type} [Inhabited α] [BEq α]
    (self : Mat1 α) (f : β → α → β) (init : β ): Array β :=
  Array.range (self.vector.size / self.width)
    |> .map (fun i => self.vector.toSubarray i (i + self.width)
      |> Array.ofSubarray
      |>.foldl f init)

def mapRows {α : Type} [Inhabited α] [BEq α] (self : Mat1 α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.width)
    |> .map (fun i => self.vector.toSubarray i (i + self.width) |> Array.ofSubarray |> f)

def row {α : Type} [Inhabited α] [BEq α] (self : Mat1 α) (i : Nat) : Subarray α :=
  let j := i % (self.vector.size % self.width)
  let f := j * self.width
  let t := f + self.width
  self.vector.toSubarray f t

def column {α : Type} [Inhabited α] [BEq α] (self : Mat1 α) (i : Nat) : Array α :=
  Array.range (self.vector.size / self.width) |> .map (self.get · i)

end Mat1

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
