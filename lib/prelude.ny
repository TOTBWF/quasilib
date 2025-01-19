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

def absurd (A : Type) (ff : ⊥) : A := match ff []

` Product types

` Sigma types.
def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

def Pair (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

notation 6 Pair : A "×" B := Pair A B


` Coproduct types.
def Either (A B : Type) : Type :=
data [
| inl. : A → Either A B
| inr. : B → Either A B
]

notation 5 Either : A "⊎" B := Either A B

section Either :=
  ` Recursion principle for coproducts.
  def recurse (A B X : Type) (f : A → X) (g : B → X) : A ⊎ B → X := [
  | inl. a ↦ f a
  | inr. b ↦ g b
  ]

  ` Elimination principle for coproducts.
  def elim
    (A B : Type) (P : A ⊎ B → Type)
    (f : (a : A) → P (inl. a))
    (g : (b : B) → P (inr. b))
    : (ab : A ⊎ B) → P ab := [
    | inl. a ↦ f a
    | inr. b ↦ g b
    ]
end

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

def J₂
  (A : Type) (P : (x y : A) → Path A x y → Type)
  (r : (x : A) → P x x refl.)
  (x y : A) (p : Path A x y)
  : P x y p :=
match p [
| refl. ↦ r x
]

def Path.sym (A : Type) (x y : A) (p : Path A y x) : Path A x y :=
match p [
refl. ↦ refl.
]

def Path.trans (A : Type) (x y z : A) (p : Path A x y) (q : Path A y z) : Path A x z :=
match p, q [
| refl., refl. ↦ refl.
]

` Congruence.
def cong (A B : Type) (f : A → B) (x y : A) (p : Path A x y) : Path B (f x) (f y) :=
match p [
| refl. ↦ refl.
]

` PathP is defined via transport. This tends to work better than Path⁽ᵈ⁾ in
` practice, as it avoids an annoying 'Gel'.
def PathP
  (A : Type) (B : A → Type)
  (a0 : A) (b0 : B a0) (a1 : A) (b1 : B a1)
  (p : Path A a0 a1) : Type :=
  Path (B a1) (subst A B a0 a1 p b0) b1

` ----------------------------------------
` Natural numbers
` ----------------------------------------


` The type of natural numbers
def Nat : Type :=
data [
| zero. : Nat
| suc.  : Nat → Nat
]

section Nat :=

  ` Degenerate a natural number.
  def degen (n : Nat) : Nat⁽ᵈ⁾ n :=
  match n [
  | zero.  ↦ zero.
  | suc. n ↦ suc. (degen n)
  ]

  ` Addition.
  def add (k n : Nat) : Nat :=
  match k [
  | zero. ↦ n
  | suc. k ↦ suc. (add k n)
  ]

  ` Subtraction.
  def sub (n k : Nat) : Nat :=
  match k, n [
  | zero. , n ↦ n
  | suc. k , zero. ↦ zero.
  | suc. k , suc. n ↦ sub n k
  ]

  def pred (n : Nat) : Nat :=
  match n [
  | zero. ↦ zero.
  | suc. n ↦ n
  ]

  ` Ordering on natural numbers.
  def lte (k n : Nat) : Type :=
  match k , n [
  | zero.  , n      ↦ ⊤
  | suc. k , zero.  ↦ ⊥
  | suc. k , suc. n ↦ lte k n
  ]

  ` Strict ordering on natural numbers.
  def lt (k n : Nat) : Type := lte (suc. k) n
end

notation 5 Nat.lte : k "≤" n := Nat.lte k n
notation 5 Nat.lt : k "<" n := Nat.lt k n

` ----------------------------------------
` Booleans
` ----------------------------------------

def Bool : Type :=
data [
| false. : Bool
| true. : Bool
]
