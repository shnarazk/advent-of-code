
-- structure Mat2 (width : Fin ) (size : Nat × Nat) (α : Type) where
--   vector : Array α

-- instance [ToString α] : ToString (Mat2 size α) where
--   toString m := s!"{size}{toString m.vector}"

def Mat2 (_ : Array (Array α)) (arr : Array α) Nat (_ : Fin (Array.size arr)) :=
  (Array (Array α)) × (arr : Array α) × Nat × (Fin (Array.size arr))

def Mat2T {α : Type} (_ : Array (Array α)) (arr : Array α) (_ : Nat) (_ : arr.size > 0) :=
  (Array (Array α)) × (ar : Array α) × Nat × (_ : ar.size > 0)

-- def Mat2 {α : Type} (mat : Array (Array α)) (arr : Array α) (_ : Fin mat.size) (_ : Fin (Array.size arr))
-- -- def Mat2 (mat : Array (Array α)) (arr : Array α) (p1 : Fin arr.size) (p2 : Fin (Array.size (Array.foldl append #[] arr)))
--  :=
--   (mat : Array (Array α)) × (arr : Array α) × (Fin (Array.size mat)) × (Fin (Array.size arr))

  -- (mat : Array (Array α)) × (arr : Array α) × (Fin (Array.size mat)) × (Fin (Array.size (Array.foldl append #[] mat)))

namespace Mat2

def chec {α : Type u} (a : Array α) : Option Prop := if a.size > 0 then some (a.size > 0) else none

#check chec
#eval @Fin.ofNat 10 6 / 2

/--
the size of genarated object is invalid if the data is empty.
-/
def new_helper {α : Type} (vec : Array α) : Option ((Array α) × Fin vec.size) :=
  if nonZero : vec.size > 0
  then some (vec, Fin.ofNat' 0 nonZero)
  else none

def new_helperT {α : Type} (vec : Array α) : Option ((Array α) × Prop) :=
  if _nonZero : vec.size > 0
  then some (vec, vec.size > 0)
  else none

-- def new_helper2 {α : Type} (vec : Array α) : Option ((Array α) × vec.size) :=
--   if nonZero : vec.size > 0
--   then some (vec, vec.size)
--   else none

#check new_helperT #[true]

def new {α : Type} (vecs : Array (Array α)) :=
  if nonZeroHeight : vecs.size > 0
  then
    let len := (vecs[0]'nonZeroHeight).size
    if _nonZeroWidth : len > 0
    then
      match new_helper (vecs.foldl Array.append #[]) with
      | some (a, p) => some (a, len, p)
      | none => none
    else none
  else none

def get {α : Type} (mat : (arr: Array α) × Nat × (Fin arr.size)) (i j : Nat) : α :=
  let w := mat.snd.fst
  let l := mat.snd.snd
  let idx := i * w + j
  if h : mat.fst.size > 0
  then mat.fst.get (Fin.ofNat' idx h)
  else mat.fst.get l

-- def get1 {α : Type} (mat : (arr: Array α) × Nat × (p : arr.size > 0)) (i j : Nat) : α :=
--   let arr := mat.fst
--   let w := mat.snd.fst
--   let l := mat.snd.snd
--   let idx := i * w + j
--   mat.fst.get (Fin.ofNat' idx l)

-- def get2 {α : Type} (mat : (arr: Array α) × Nat × (Fin (Array.size arr))) (i j : Nat) : α :=
--   let arr := mat.fst
--   let w := mat.snd.fst
--   let l := mat.snd.snd.isLt
--   let idx := i * w + j
--   if h : arr.size > 0
--   then
--   if idx > l
--   then arr.get l
--   else mat.fst.get (Fin.ofNat' idx l.isLt)

def x := @Fin.ofNat 10 1
-- #eval Fin.ofNat' (333 : Nat) x.isLt

  -- arr.get ((i * w + j) + t)

-- def get {α : Type} (mat : Mat2 (_ : Array (Array α)) (arr : Array α) Nat (_ : Fin (Array.size arr))) (i j : Nat) : α :=
--   let (_, arr, w, t) := mat
--   arr.get ((i * w + j) + t)

-- def get {α : Type} (mat : Mat2 (_ : Array (Array α)) (arr : Array α) (f1 : Nat)
--     (f2 : Fin (Array.size arr))) (i j : Nat) : α :=
--   arr.get[i * f1 + j: f2]

-- #eval new #[#[true]]
#check new #[#[true]]

-- def get {α : Type} ited α] (vecs : Array (Array α)) :=

-- #eval Mat2.new #[#[2, 3], #[8, 9]]
-- #check Mat2.new #[#[2, 3], #[8, 9]]

end Mat2
