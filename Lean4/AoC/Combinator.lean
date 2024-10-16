-- set_option autoImplicit true
import Batteries

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

@[inline]
def I (a : α) := a
@[inline]
def K (a : α) (_b : β) := a
@[inline]
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
def uncurry (f : α → β → γ) : (α × β) → γ := fun (a, b) => f a b

end CiCL

namespace BQN

@[inline]
def before (y : α → β) (x : β → α → γ) (z : α) : γ := x (y z) z
@[inline]
def after (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
@[inline]
def train (x : α → β) (z : β → γ → ε) (y : α → γ) (a : α) : ε := z (x a) (y a)
@[inline]

infixr:80 " ⊸ " => before
infixr:80 " ⟜ " => after

notation:60 " ⎊" lhs:60 "‿" mhs:60 "‿" rhs:60 => train lhs mhs rhs
notation:100 "¯" val => (- val)

-- #eval 4 + ¯80

end BQN

namespace CoP -- combinators on pair

@[inline]
def both (f : α → β) (x : α × α) : β × β := (f x.fst, f x.snd)
@[inline]
def both2 (f : α → β → γ) (x : α × α) (y : β × β) : γ × γ := (f x.fst y.fst, f x.snd y.snd)
@[inline]
def join (f : α → α → β) (x : α × α) : β := f x.fst x.snd

end CoP
