
structure Mat1 (α : Type) [Inhabited α] where
  width  : Nat
  vector : Array α
deriving Repr

instance [ToString α] [Inhabited α] : ToString (Mat1 α) where
  toString m := s!"{m.width}{toString m.vector}"

namespace Mat1
def new {α : Type} [Inhabited α] (vec : Array α) (w : Nat) : Mat1 α :=
  ({ width := w, vector := vec } : Mat1 α)

def get {α : Type} [Inhabited α] (mat : Mat1 α) (i j : Nat) : α :=
  let ix := i * mat.width + j
  if h : mat.vector.size > 0
  then mat.vector.get (Fin.ofNat' ix h)
  else (default : α)

def x := new #[true, false, true, false] 2

#eval x
#check x
#check get

def y := get x 0 0
#eval y


end Mat1
