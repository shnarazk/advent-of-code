
structure Mat2 (size : Nat × Nat) (α : Type) where
  height : Fin (size.fst)
  width  : Fin (size.snd)
  values : Array α
deriving Repr

instance [ToString α] : ToString (Mat2 size α) where
  toString m := s!"{size}{toString m.values}"

namespace Mat2

/--
the size of genarated object is invalid if the data is empty.
-/
def new {α : Type} [Inhabited α] (vecs : Array (Array α)) :=
  let size := (max 1 vecs.size, max 1 vecs[0]!.size)
  let H : size.fst > 0 := by apply Nat.le_max_left
  let W : size.snd > 0 := by apply Nat.le_max_left
  let array := vecs.foldl Array.append #[]
  ({
    height := Fin.ofNat' size.fst H,
    width  := Fin.ofNat' size.snd W,
    values := array } : Mat2 size (array.size > 0) α)

#eval Mat2.new #[#[2, 3], #[8, 9]]
#check Mat2.new #[#[2, 3], #[8, 9]]
#eval 10 % 0

def get (self : Mat2 size α) (y x : Nat) : α :=
  let i := min ((y * self.width + x) % self.values.size) self.values.size
  self.values.get[i % self.values.size]

end Mat2
