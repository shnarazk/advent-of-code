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

/--
- Identity: λa. a
-/
@[inline]
def I (a : α) := a

/--
- Constant: λa b. a
-/
@[inline]
def K (a : α) (_b : β) := a

/--
- Dyandic application
-/
@[inline]
def W (f : α → α → β) (a : α) := f a a

/--
- Swap λf a b. f b a
-/
@[inline]
def C (f : α → β → γ) (b : β) (a : α) : γ := f a b

@[inline]
def B (f : β → γ) (g : α → β) (a : α) := f (g a)

/--
- Monadic After: λa b c. (a c) (b c)
-/
@[inline]
def S (f : α → β → γ) (b : α → β) (a : α) := f a (b a)

/--
- Dyadic After
-/
@[inline]
def D (f : α → γ → δ) (a : α) (g : β → γ) (b : β) := f a (g b)

@[inline]
def B₁ (f : γ → δ) (g : α → β → γ) (a : α) (b :β) := f (g a b)

/--
- Psi
-/
def Ψ (f : β → β → γ) (g : α → β) (a b : α) := f (g a) (g b)

/--
- Phi
-/
def Φ (f : β → δ → ε) (g : α → β) (h : α → δ) (a : α) := f (g a) (h a)

def D₂ (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a : α) (b : β) := f (g a) (h b)

def E (f : α → δ → ε) (a : α) (g : β → γ → δ) (b : β) (c : γ) := f a (g b c)

/--
- Dyadic 3-train
-/
def Φ₁ (f : γ → γ → δ) (g h : α → β → γ) (a : α) (b : β) := f (g a b) (h a b)

def E' (f : γ → ζ → η) (g : α → β → γ) (h : δ → ε → ζ) (a : α) (b : β) (c : δ) (d : ε) := f (g a b) (h c d)

@[inline]
def uncurry (f : α → β → γ) : (α × β) → γ := fun (a, b) => f a b

end CiCL

namespace BQN

/--
g ⟜ f = λa. g (f a) a
-/
@[inline]
def before (g : β → α → γ) (f : α → β) (a : α) : γ := g (f a) a
infixr:80 " ⟜ " => before

/--
f ⊸ g = λa. g a (f a)
-/
@[inline]
def after (f : α → β) (g :α → β → γ) (a : α) : γ := g a (f a)
infixr:80 " ⊸ " => after

/--
Three train
-/
@[inline]
def train (x : α → β) (z : β → γ → ε) (y : α → γ) (a : α) : ε := z (x a) (y a)
notation:60 " ⎊" lhs:60 "‿" mhs:60 "‿" rhs:60 => train lhs mhs rhs

-- notation:100 " ¯" val => (- val)
-- #eval (· + (1 : Int)) ¯8

end BQN

namespace CoP -- combinators on pair

@[inline]
def both (f : α → β) (x : α × α) : β × β := (f x.fst, f x.snd)
@[inline]
def both2 (f : α → β → γ) (x : α × α) (y : β × β) : γ × γ := (f x.fst y.fst, f x.snd y.snd)
@[inline]
def join (f : α → α → β) (x : α × α) : β := f x.fst x.snd

end CoP
