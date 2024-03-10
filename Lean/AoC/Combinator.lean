-- set_option autoImplicit true
import Std

/-
@inproceedings{10.1145/3520306.3534504,
    author = {Hoekstra, Conor},
    title = {Combinatory logic and combinators in array languages},
    year = {2022},
    isbn = {9781450392693},
    publisher = {Association for Computing Machinery},
    url = {https://doi.org/10.1145/3520306.3534504},
    doi = {10.1145/3520306.3534504},
    abstract = {The array language paradigm began in the 1960s when Ken Iverson created APL. After spending over 30 years working on APL, he moved on to his second array language J, a successor to APL which embeds a significant subset of combinatory logic in it. This paper will look at the existence of combinators in the modern array languages Dyalog APL, J and BQN and how the support for them differs between these languages. The paper will also discuss how combinators can be a powerful language feature as they exist in modern array languages.},
    booktitle = {Proceedings of the 8th ACM SIGPLAN International Workshop on Libraries, Languages and Compilers for Array Programming},
    pages = {46–57},
    numpages = {12},
    series = {ARRAY 2022}
}
-/
namespace CiCL -- Combinators in Combinatory Logic

def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
def before (y : α → β) (x : β → α → γ) (z : α) : γ := x (y z) z
def after  (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
def train (x : α → β) (z : β → γ → ε) (y : α → γ) (a : α) : ε := z (x a) (y a)
@[inline]
def uncurry (f : α → β → γ) : (α × β) → γ := fun (a, b) => f a b

infix:80    " ⊸ " => before
infixl:80   " ⟜ " => after

notation:80 " ◀️ " lhs:80 " | " mhs:80 " | " rhs:80 " ▶️ " => train lhs mhs rhs

end CiCL

namespace CoP -- combinators on pair

def both (f : α → β) (x : α × α) : β × β := (f x.fst, f x.snd)
def both2 (f : α → β → γ) (x : α × α) (y : β × β) : γ × γ := (f x.fst y.fst, f x.snd y.snd)
def join (f : α → α → β) (x : α × α) : β := f x.fst x.snd

end CoP
