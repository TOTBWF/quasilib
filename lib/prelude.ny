` ----------------------------------------
` Prelude
` ----------------------------------------

` Gel Types
def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A :=
  A' ↦ sig #(transparent) x ↦ (ungel : A' x)

` Unit type
` Marked as #(transparent) to always print elements of the unit
` type as `()`.
def ⊤ : Type := sig #(transparent) ()

` Empty type.
def ⊥ : Type := data []

` Coproduct types.
def Either (A B : Type) : Type :=
data [
| inl. : A → Either A B
| inr. : B → Either A B
]

notation 5 Either : A "⊎" B := Either A B

` Identity types.
def Path (A : Type) (x : A) : A → Type :=
data [
| refl. : Path A x x
]

` Transport along a path.
def subst (A : Type) (P : A → Type) (x y : A) (p : Path A x y) (x' : P x) : P y :=
match p [
| refl. ↦ x'
]

` Path induction.
def J (A : Type) (x : A) (P : (y : A) → Path A x y → Type) (x' : P x refl.)
  (y : A) (p : Path A x y) : P y p :=
match p [
| refl. ↦ x'
]

` Congruence.
def cong (A B : Type) (f : A → B) (x y : A) (p : Path A x y) : Path B (f x) (f y) :=
match p [
| refl. ↦ refl.
]

` ----------------------------------------
` Natural numbers
` ----------------------------------------

` The type of natural numbers
def Nat : Type :=
data [
| zero. : Nat
| suc.  : Nat → Nat
]

` Degenerate a natural number.
def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n :=
match n [
| zero.  ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

` Addition.
def Nat.add (k n : Nat) : Nat :=
match k [
| zero. ↦ n
| suc. k ↦ suc. (Nat.add k n)
]

` Ordering on natural numbers.
def Nat.lte (k n : Nat) : Type :=
match k , n [
| zero.  , n      ↦ ⊤
| suc. k , zero.  ↦ ⊥
| suc. k , suc. n ↦ Nat.lte k n
]

` Strict ordering on natural numbers.
def Nat.lt (k n : Nat) : Type := Nat.lte (suc. k) n

notation 5 Nat.lte : k "≤" n := Nat.lte k n
notation 5 Nat.lt : k "<" n := Nat.lt k n
