-- import Init.Data.Array.Subarray
import Mathlib.Tactic
import Std.Data.HashMap

/--
### An index to point a posiition in an infinite 2D space
-/
structure Dim2 where
  y : Int
  x : Int
deriving Repr

instance : BEq Dim2 where beq a b           := a.y == b.y && a.x == b.x
instance : Hashable Dim2 where hash a       := hash (a.y, a.x)
instance : Coe (Nat × Nat) Dim2 where coe p := Dim2.mk ↑p.1 ↑p.2
instance : Coe (Int × Int) Dim2 where coe p := Dim2.mk p.1 p.2
instance : Inhabited Dim2 where default     := Dim2.mk 0 0
instance : ToString Dim2 where toString s   := s!"2D({s.1}, {s.2})"
instance : LawfulBEq Dim2 where
  eq_of_beq {a b} (h : a.y == b.y && a.x == b.x):= by
    cases a; cases b
    simp at h
    simp
    exact h
  rfl := by simp [BEq.beq]

instance : LawfulHashable Dim2 where
  hash_eq := by intro a b H ; cases a; cases b ; simp at H ; simp [H]

instance : EquivBEq Dim2 where
  symm  := by intro a b h ; exact BEq.symm h
  trans := by intro a b h ; exact PartialEquivBEq.trans
  refl  := by intro a ; exact beq_iff_eq.mpr rfl

def dim2_add_dim2 (a b : Dim2) : Dim2 := Dim2.mk (a.y + b.y) (a.x + b.x)
instance instHAdddDim2 : HAdd Dim2 Dim2 Dim2 where hAdd := dim2_add_dim2
instance : HAdd Dim2 Int Dim2 where
  hAdd (a : Dim2) (c : Int) := Dim2.mk (a.y + c) (a.x + c)
instance : HAdd Int Dim2 Dim2 where
  hAdd (c : Int) (a : Dim2)  := Dim2.mk (c + a.y) (c + a.x)
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

example : (8 : Int) + (Dim2.mk 3 1) = Dim2.mk 11 9  := by rfl
lemma dim2_zero_add (p : Dim2) : (0 : Int) + p = p  := by simp [(· + ·)] ; simp [Add.add]
lemma dim2_add_zero (p : Dim2) : p + (0 : Int) = p  := by simp [(· + ·)] ; simp [Add.add]
example : (Dim2.mk 3 7) * (8 : Int) = Dim2.mk 24 56 := by rfl

private def Dim2.lt (a b : Dim2) := a.1 < b.1 ∧ a.2 < b.2
instance : LT Dim2 where lt := Dim2.lt

private def Dim2.le (a b : Dim2) := a.1 ≤ b.1 ∧ a.2 ≤ b.2
instance : LE Dim2 where le := Dim2.le

example : Dim2.mk 3 (-2) = ({ x := -2, y := 3 } : Dim2) := by rfl
example : ((3, 5) : Dim2) = Dim2.mk 3 5                 := by rfl
example : (((3 : Int), (5 : Int)) : Dim2) = Dim2.mk 3 5 := by rfl
example : ((-2, -2) : Dim2) < ((5, 4) : Dim2)           := by simp ; constructor <;> simp
example : ((-2, (4 : Int)) : Dim2) ≤ ((5, 4) : Dim2)    := by simp ; constructor <;> simp

class AsDim2 (α : Type) where asDim2 : α → Dim2

instance : AsDim2 Dim2 where asDim2        := (·)
instance : AsDim2 (Int × Int) where asDim2 := Coe.coe
instance : AsDim2 (Nat × Nat) where asDim2 := Coe.coe

def NonNegDim (d : Dim2) := 0 ≤ d.y ∧ 0 ≤ d.x

example : NonNegDim (Dim2.mk 1 1) := by simp [NonNegDim]
-- #check NonNegDim (Dim2.mk 1 1)
-- #eval if _ : NonNegDim (Dim2.mk (-1) (-1)) then "OK" else "No"

namespace Dim2

instance : AddMonoid Dim2 where
  zero := default -- Dim2.mk 0 0
  add a b := Dim2.mk (a.y + b.y) (a.x + b.x)
  add_assoc a b c := by
    simp [(· + ·), dim2_add_dim2]
    constructor
    { exact add_assoc (a.y) (b.y) (c.y) }
    { exact add_assoc (a.x) (b.x) (c.x) }
  zero_add := by exact dim2_zero_add
  add_zero := by exact dim2_add_zero
  nsmul (n : Nat) (a : Dim2) := Dim2.mk (n * a.y) (n * a.x)
  nsmul_zero := by simp ; rfl
  nsmul_succ := by intro n a ; simp [Dim2.mk] ; group ; rfl

instance : SubNegMonoid Dim2 where
  neg a := Dim2.mk (-a.y) (-a.x)
  zsmul n a := Dim2.mk (n * a.y) (n * a.x)
  zsmul_zero' := by intro a ; simp ; rfl
  zsmul_succ' := by intro a b ; simp [add_mul] ; constructor
  zsmul_neg' := by
    intro a b
    simp
    constructor
    {
      symm
      calc
        -((↑a + 1) * b.y) = -(↑a + 1) * b.y
          := by exact Int.neg_mul_eq_neg_mul (↑a + 1) b.y
        _ = Int.negSucc a * b.y := by exact rfl
    }
    {
      symm
      calc
        -((↑a + 1) * b.x) = -(↑a + 1) * b.x
          := by exact Int.neg_mul_eq_neg_mul (↑a + 1) b.x
        _ = Int.negSucc a * b.x := by exact rfl
    }

instance : AddCommMonoid Dim2 where
  add_comm := by intro a b ; simp [HAdd.hAdd] ; simp [Add.add] ; constructor <;> rw [add_comm]

instance : AddGroup Dim2 where
  neg_add_cancel a := by
    simp [(· + · )]
    simp [Add.add]
    rw [add_comm] -- , SubNegMonoid.sub_eq_add_neg]
    have cancel_y : (-a).y = -(a.y) := by exact rfl
    have cancel_x : (-a).x = -(a.x) := by exact rfl
    simp [cancel_y, cancel_x]
    exact rfl

def area (a : Dim2) : Nat := (a.y * a.x).toNat
example : ((5, 4) : Dim2).area = 20 := by rfl

def double (a : Dim2) : Dim2 := Dim2.mk (2 * a.1) (2 * a.2)

example (y x : Nat) : Dim2.mk (2 * y) (2 * x) = Dim2.double (Dim2.mk y x) := by
  simp [Dim2.mk, Dim2.double]

def index (frame self : Dim2) : Nat := self.y.toNat * frame.x.toNat + self.x.toNat
def index' (frame : Dim2) (n : Nat) : Dim2 := Dim2.mk (n / frame.x) (n % frame.x)

open Nat
/--
This is identitcal to `List.range`. But it is much much simple to prove something.
-/
def range_list : Nat → List Nat
  | 0 => []
  | n + 1 => range_list n ++ [n]

lemma range_list_length_is_n (n : Nat) : (range_list n).length = n := by
  induction' n with n h
  { rw [range_list] ; simp }
  { rw [range_list] ; rw [List.length_append] ; simp ; exact h }

lemma zero_lt_range_list_length : ∀ n : Nat, 0 < (range_list (n + 1)).length := by
  intro n
  induction' n with n₀ _
  { simp ; rw [range_list] ; simp }
  { rw [range_list] ; rw [List.length_append] ; simp }

/--
これが使いたかった。h₂はどうしても消せない。
-/
lemma getElem_append' (l l' : List α) (n : Nat) (h₁ : n < l.length) (h₂ : n < (l ++ l').length) :
    (l ++ l')[n] = l[n] := by
  simp [List.getElem_append, h₁]

/-
さらにrange_listに特化させたもの。帰納法用。
-/
lemma range_list_induction
    (n i : Nat)
    (h₁ : i < (range_list n).length)
    (h₂ : i < (range_list (n + 1)).length) :
    (range_list (n + 1))[i] = (range_list n)[i] := by
  have : (range_list (n + 1))[i] = (range_list n ++ [n])[i] := by exact rfl
  rw [this]
  rw [getElem_append']

lemma range_list_trim (n k i : Nat) (h₁ : i < (range_list (n + k)).length) (h₂ : i < (range_list n).length) :
    (range_list (n + k))[i] = (range_list n)[i] := by
  induction' k with k₀ ih
  { simp }
  {
    simp [←Nat.add_assoc]
    have h1 : i < (range_list (n + k₀)).length := by
      rw [range_list_length_is_n] at h₂
      rw [range_list_length_is_n]
      exact Nat.lt_add_right k₀ h₂
    have h2 : i < (range_list (n + k₀ + 1)).length := by
      rw [range_list_length_is_n] at h₂
      rw [range_list_length_is_n]
      have h2 : i < n + k₀ := by exact Nat.lt_add_right k₀ h₂
      exact Nat.lt_add_right 1 h2
    rw [range_list_induction (n + k₀) i h1 h2]
    apply ih
  }

lemma range_index_index_zero_eq_zero (n : Nat) (h : 0 < (range_list (n + 1)).length) :
    (range_list (n + 1))[0] = 0 := by
  have : (range_list (n + 1))[0] = (range_list 1)[0] := by
    simp [add_comm n 1]
    rw [range_list_trim 1 n 0]
  rw [this]
  simp [range_list]

lemma range_index_eq_index (n : Nat) (h : n < (range_list (n + 1)).length) : (range_list (n + 1))[n] = n := by
  simp [range_list]
  have h' : ¬n < (range_list n).length := by rw [range_list_length_is_n] ; simp
  rw [List.getElem_append n h]
  simp [h']

-- ここまでOK

lemma range_list_n1_contains_n (n : Nat) : n ∈ range_list (n + 1) := by
  rw [range_list.eq_def] ; simp

lemma range_list_length_is_invariant (n : Nat) : (range_list n).length = n := by
  induction' n with n0 ih ; { simp [range_list] } ; { simp [range_list, ih] }

lemma append_range_list_get_nth (n : Nat) (l : List Nat) (k : Nat) (h₀ : 0 < l.length) (h₁ : k < l.length) (h₂ : n + k < (range_list n ++ l).length):
    (range_list n ++ l)[n + k] = l[k] := by
  have h0 : n = (range_list n).length := by exact Eq.symm (range_list_length_is_n n)
  have h1 : n < (range_list n ++ l).length := by
    rw [List.length_append]
    rw [←h0]
    exact Nat.lt_add_of_pos_right h₀
  have h2 : n + k ≥ (range_list n).length := by
    rw [←h0]
    exact Nat.le_add_right n k
  have h2' : ¬ n + k < (range_list n).length := by exact Nat.not_lt.mpr h2
  rw [@List.getElem_append Nat (range_list n) l (n + k) h₂]
  simp [h2']
  have : n + k - (range_list n).length = k := by
    exact Eq.symm (Nat.eq_sub_of_add_eq' (congrFun (congrArg HAdd.hAdd (symm h0)) k))
  simp [this]

def join' {α : Type} : List (List α) → List α
  | [] => []
  | a :: l => a ++ join' l

def cartesian_product (y x : Nat) : List (Nat × Nat) :=
  let rec embedded (y : Nat) (x : Nat) :=
    match x with
    | 0      => []
    | x' + 1 => embedded y x' ++ [(y, x')]
  match y with
  | 0      => []
  | y' + 1 => cartesian_product y' x ++ embedded y' x

/-
#eval cartesian_product 3 2
#eval cartesian_product 4 0
#eval cartesian_product 0 3

lemma cartesian_product_covers_dim2nat (y x : Nat) :
    ∀ i : Nat, ∀ j : Nat, i < y → j < x → List.contains (cartesian_product y x) (i, j) == true := by
  intro i j Hy Hx
  simp [List.contains]
  induction' y with y hy
  { contradiction }
  {
    simp [cartesian_product]
    by_cases ih: i = y
    {
      right
      rw [ih]
      rw [cartesian_product.embedded.eq_def]
      induction' x with x hx
      { simp ; exact Nat.not_succ_le_zero j Hx }
      {
        simp
        by_cases J : j < x
        {
          simp [ih] at *
          left
          obtain AA := hx J

        }
      }
    }
    {
      have : i ≤ y := by exact Nat.le_of_lt_succ Hy
      have : i < y := by exact Nat.lt_of_le_of_ne this ih
      exact Or.symm (Or.inr (hy this))
    }
  }
-/

def toList (base : Dim2) : List Dim2 :=
  join'
    (List.map
      (fun y ↦ (range_list base.x.toNat).map (Dim2.mk y ·))
      (range_list base.y.toNat))

/-
lemma length_is_invariant_under_map {α β : Type} (l : List α) (f : α → β) :
    List.length l = (List.map f l).length := by
  induction' l with _ ln _ ; { simp } ; { simp [(· :: ·)] }

lemma map_induction {α β : Type} (a : α) (l : List α) (f : α → β) :
  List.map f (l ++ [a]) = List.map f l ++ [f a] := by simp

lemma append_length {α : Type} (a b : List α) :
    (a ++ b).length = a.length + b.length := by
  simp [(· ++ ·)] ; simp [Append.append]

lemma length_is_invariant_under_join' {α : Type} (l : List (List α)) :
    (List.map List.length l).sum = (join' l).length := by
  induction' l with l₀ l ih
  { simp [join'] }
  {
    simp [map_induction]
    rw [ih]
    rw [←append_length]
    simp [join']
  }

lemma range_list_generates_same_lenth_list {α : Type} (n : Nat) (f : Nat → α)
: (List.map f (range_list n)).length = n := by
  induction' n with n₀ ih
  { simp [range_list] }
  {
    rw [range_list]
    rw [map_induction]
    rw [List.length_append]
    rw [ih]
    simp [List.length]
  }

lemma length_is_invariant_under_join'' {α : Type} (l : List (List α)) :
    (join' l).length = (List.map List.length l).sum := by
  induction' l with l₀ l ih ; { simp [join'] } ; { simp [join'] ; exact ih }

lemma to_list_length_is_invariant {α : Type} (p : Dim2) : p.toList.length = p.area := by
  rw [toList]
  rw [length_is_invariant_under_join'']
  sorry

-- lemma range_length_eq_self {α : Type} (n : Nat) (f : Nat → α) :
--    n = ((List.range n).map f).length := by induction' n with n₀ _ ih <;> simp

lemma range_range_eq_mul {α : Type} (n m : Nat) (f : Nat × Nat → α) :
    ((List.range n).map (fun i ↦ (List.range m).map f)).length = n := by
  induction' n with n₀ ih
  { simp }
  {
    have induction_on_range (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
      induction' n with n₀ ih2 ih3
      { simp ; rfl }
      {
        rw [List.range] at ih2
        -- nth_rewrite 1 [List.range]
        nth_rewrite 2 [List.range]
        rw [ih2]
        rw [List.append_assoc]
        simp
        rw [List.range]
        rw [List.range.loop]
        sorry
      }
    sorry
  }

example (p : Dim2) : 0 ≤ p → p.area = p.toList.length := by
  intro q
  have : ∀ y : Nat, ∀ x : Nat, (Dim2.mk y x).area = (Dim2.mk y x).toList.length := by
    intro y x
    induction' y with y₀ hy
    { simp [Dim2.area] ; simp [Dim2.toList] }
    {
      simp [Dim2.area] at *
      simp [add_mul]
      have toInt_toNAt_cancel (n : Nat) : (↑n : Int).toNat = n := by rfl
      have toInt_add_toInt (i j k : Nat) :
          (↑i * ↑j + (↑k : Int)).toNat = ((↑i : Int) * ↑j).toNat + k := by rfl
      simp [toInt_add_toInt]
      simp [Dim2.toList]
      simp [toInt_toNAt_cancel] at *
      sorry
    }
  rw [toList]
  sorry
-/

end Dim2

namespace TwoDimensionalVector

open Std.HashMap Dim2

variable {α : Type}

/--
### A Presentation of infinite 2D space
-/
structure Plane (α : Type) [BEq α] [Hashable α] where
  mapping : Std.HashMap Dim2 α
deriving Repr

instance [BEq α] [Hashable α] :
    Inhabited (Plane α) where default := Plane.mk Std.HashMap.empty

def Plane.empty [BEq α] [Hashable α]
    (capacity : optParam Nat 8) : Plane α :=
  { mapping := Std.HashMap.empty capacity }

example : (Plane.empty : Plane Nat) = (default : Plane Nat) := by simp [default, Plane.empty]

def Plane.get [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (default : α) : α :=
  self.mapping.getD (AsDim2.asDim2 p) (default : α)

def Plane.set [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (a : α) : Plane α :=
  { self with mapping := self.mapping.insert (AsDim2.asDim2 p) a }

def Plane.modify [BEq α] [Hashable α]
    (self : Plane α) (p : Dim2) (f : α → α) (default : α): Plane α :=
  { self with
    mapping := self.mapping.insert p (f (self.mapping.getD p default)) }

example [BEq α] [Hashable α] (p : Plane α) (y x : Nat) (a : α) :
    p.set (Dim2.mk y x) a = p.set (y, x) a := by simp

example [BEq α] [Hashable α] (p : Plane α) (q : Dim2) (a default : α) :
      (p.set q a).get q default = a  := by
  simp [Plane.set, AsDim2.asDim2, Plane.get]

/--
### A Presentation of bounded 2D spaces

Note: this implementation accept zero space for now.
And It returns the `default` by `·.get (0, 0)`
-/
structure Rect (α : Type) [BEq α] where
  shape  : Dim2
  vector : Array α
  -- neZero : shape ≠ default ∧ NeZero vector.size
  validShape: NonNegDim shape
  validArea : shape.area = vector.size
deriving Repr

instance [BEq α] : BEq (Rect α) where
  beq a b := a.shape == b.shape && a.vector == b.vector

instance [ToString α] [BEq α] : ToString (Rect α) where
  toString bp := s!"{bp.shape}{toString bp.vector}"

namespace Rect

/--
- return a new Rect
-/
def new [BEq α]
    (g : Dim2) (vec : Array α) (h1 : NonNegDim g) (h2 : g.area = vec.size): Rect α :=
  Rect.mk g vec h1 h2

/--
- return a new instance fitting to the given Dim2
-/
def ofDim2 [BEq α] (g : Dim2) (h : NonNegDim g) (default : α) : Rect α :=
  let v := Array.mkArray (g.area) default
  have p : v.size = g.area := by exact Array.size_mkArray g.area default
  Rect.mk g v h (symm p)

/--
- return a new instance of Rect by converting from an 2D array
-/
def of2DMatrix [BEq α]
  (a : Array (Array α)) : Rect α :=
  have h : Nat := a.size
  match h with
  | 0 =>
    let d := Dim2.mk 0 0
    have : NonNegDim d := by simp [NonNegDim]
    Rect.mk d #[] this (by rfl : d.area = #[].size)
  | _ =>
    let total : Nat := a.foldl (fun acc vec ↦ acc + vec.size) 0
    let w := total / h
    let v : Array α := a.foldl Array.append #[]
    if hw : h * w = v.size then
      let d := Dim2.mk h w
      have : NonNegDim d := by simp [NonNegDim]
      Rect.mk d v this hw
    else
      let d := Dim2.mk 0 0
      have : NonNegDim d := by simp [NonNegDim]
      Rect.mk d #[] this (by rfl : d.area = #[].size)

/--
- return the `(i,j)`-th element of Mat1 instance
-/
def get [BEq α]
    (self : Rect α) (p : Dim2) (default : α) : α :=
  if h : 0 < self.vector.size then
    have : NeZero self.vector.size := by exact NeZero.of_pos h
    self.vector.get (Fin.ofNat' self.vector.size (self.shape.index p))
  else
    default

def validIndex? [BEq α]
    (self : Rect α) (p : Dim2) : Bool :=
  0 ≤ p.y && p.y < self.shape.y && 0 ≤ p.x && p.x < self.shape.x

/--
- set the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def set [BEq α]
    (self : Rect α) (p : Dim2) (val : α) : Rect α :=
  let ix := self.shape.index p
  let v := self.vector.set! ix val
  if h : self.shape.area = v.size
    then Rect.new self.shape v self.validShape h
    else self

/--
- modify the `(i,j)`-th element to `val` and return the modified Mat1 instance
-/
def modify [BEq α]
  (self : Rect α) (p : Dim2) (f : α → α) (default : α) : Rect α :=
  self.set p <| f <| self.get p default

/--
- search an element that satisfies the predicate and return indices or none
-/
def findIdx? [BEq α] (p : Rect α) (f : α → Bool) : Option Dim2 :=
  match p.vector.findIdx? f with
  | some i => some (Dim2.mk (i / p.shape.x) (i % p.shape.x))
  | none => none

private partial def findIdxOnSubarray [BEq α]
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
def findIdxInRow? [BEq α]
    (p : Rect α) (i : Nat) (pred : α → Bool) : Option (Nat × Nat) :=
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

def foldl {β : Type} [BEq α] (self : Rect α) (f : β → α → β) (init : β) : β :=
  self.vector.foldl f init

def foldlRows {β : Type} [BEq α]
    (self : Rect α) (f : β → α → β) (init : β) : Array β :=
  Array.range self.shape.y.toNat
    |> .map (fun i =>
      self.vector.toSubarray i (i + self.shape.x.toNat)
        |> Array.ofSubarray
        |>.foldl f init)

def mapRows {β : Type} [BEq α]
    (self : Rect α) (f : Array α → β) :  Array β :=
  Array.range (self.vector.size / self.shape.x.toNat)
    |> .map (fun i => self.vector.toSubarray i (i + self.shape.x.toNat) |> Array.ofSubarray |> f)

def row [BEq α] (self : Rect α) (i : Nat) : Subarray α :=
  let j : Nat := i % (self.vector.size % self.shape.x.toNat)
  let f : Nat := j * self.shape.x.toNat
  let t := f + self.shape.x.toNat
  self.vector.toSubarray f t

def column [BEq α] (self : Rect α) (j : Nat) (default : α) : Array α :=
  Array.range self.shape.y.toNat
    |>.map (fun i ↦ self.get (↑(i, j) : Dim2) default)

def area [BEq α] (self : Rect α) : Nat := self.shape.area

end Rect

def d := Dim2.mk 2 2
def v := #[true, false, true, false]
example : NonNegDim d := by simp [NonNegDim, d]

def x := Rect.new d v (by simp [NonNegDim, d]) (by rfl : d.area = v.size)
def y := Rect.of2DMatrix #[#[(1 : Int), 2, 3], #[4, 5, 6]]

-- #check x
-- #eval x
-- #check y
-- #eval y
-- #check Rect.get
-- #check x.get

-- #eval x.get (Dim2.mk 0 0) false
-- #eval y.get (0, 1) 808
-- #eval y.get (100, 100) (-1)

-- #eval x.set (0, 0) false
-- #eval y.set (1, 1) 10000

end TwoDimensionalVector
