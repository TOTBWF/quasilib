{` This file defines the join of SSTs. `}

{`
# Prelude

Currently, `narya` does not have an import mechanism, so we need to define
a small prelude first.
`}

` Unit type; use `()` to introduce an element.
def ⊤ : Type := sig ()

` Empty type.
def ⊥ : Type := data []

` Elimination principle for `⊥`; useful for when we cannot use an empty pattern
` match directly.
def absurd (A : Type) : ⊥ → A := []

` We define `Prod` as a separate record type to get better goals.
def Prod (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

notation 6 Prod : A "×" B := Prod A B

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

` Coproducts.
def Coprod (A B : Type) : Type := data [
| inl. : A → Coprod A B
| inr. : B → Coprod A B
]

` We will notate coproducts with `A ⊔ B`.
notation 5 Coprod : A "⊔" B := Coprod A B

` Recursion principle for coproducts.
def Coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A ⊔ B → X := [
| inl. a ↦ f a
| inr. b ↦ g b
]

` Natural numbers.
def Nat : Type := data [
| zero. : Nat
| suc. : Nat → Nat
]

` Degenerate a Nat into a Nat⁽ᵈ⁾.
def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

def Path (X : Type) (x : X) : X → Type := data [
| refl. : Path X x x
]

def Path.rec
  (X : Type) (P : X → Type)
  (a b : X)
  (p : Path X a b)
  (a' : P a)
  : P b :=
match p
[
| refl. ↦ a'
]

def Path.elim
  (X : Type) (x₀ : X)
  (P : (x : X) → Path X x₀ x → Type)
  (x₀' : P x₀ refl.)
  (x₁ : X)
  (p : Path X x₀ x₁)
  : P x₁ p :=
match p
[
| refl. ↦ x₀'
]

` The "synthetic" gel operation; classifies `Type⁽ᵈ⁾ A` via a map into the universe.
def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

{`
# "Analytic" semi-simplicial types

In narya (and in dTT more generally), every type synthetically carries the structure
of an augmented semisimplicial type. However, we can also define the type of "analytic"
semisimplicial types via `codata` types.
`}

` The type of semisimplicial types.
def SST : Type := codata [
` Zero Simplicies
| X .z : Type
` Coslice by a zero simplex.
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

` Maps of semisimplicial types.
def SST.Hom (X Y : SST) : Type := codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → SST.Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

{`
## Total Spaces
`}

def ∫ (B : SST) (E : SST⁽ᵈ⁾ B) : SST := [
| .z ↦ Σ (B .z) (b ↦ E .z b)
| .s ↦ ∫e ↦ ∫⁽ᵈ⁾ B (B .s (∫e .fst)) E (sym (E .s (∫e .fst) (∫e .snd)))
]

` Projection out of the total space.
def SST.∫.π (B : SST) (E : SST⁽ᵈ⁾ B) : SST.Hom (∫ B E) B := [
| .z ↦ ∫e ↦ ∫e .fst
| .s ↦ ∫e ↦ SST.∫.π⁽ᵈ⁾ B (B .s (∫e .fst)) E (sym (E .s (∫e .fst) (∫e .snd)))
]


{`
## Sections
`}

` Sections of a displayed SST along a map; these correspond to lifts of the following
` diagram:
`
`           E
`           |
`           |
`       f   v
`   A ----> B
`
def SST.Section (A B : SST) (E : SST⁽ᵈ⁾ B) (f : SST.Hom A B) : Type := codata [
| S .z : (a : A .z) → E .z (f .z a)
| S .s : (a : A .z) →
  SST.Section⁽ᵈ⁾
    A (A .s a)
    B (B .s (f .z a))
    E (sym (E .s (f .z a) (S .z a)))
    f (f .s a)
    S
]

` We can also give sections of E along `f : A → B` as an SST displayed over A;
` intuitively, this is the pullback of `E → B` along `f`.
def SST.Pullback (A B : SST) (f : SST.Hom A B) (E : SST⁽ᵈ⁾ B) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (a ↦ E .z (f .z a))
| .s ↦ a e ↦
  sym (SST.Pullback⁽ᵈ⁾
    A (A .s a)
    B (B .s (f .z a))
    f (f .s a)
    E (sym (E .s (f .z a) (e .ungel))))
]

{`
## The terminal SST
`}

` The terminal SST.
def SST.⊤ : SST := [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

` Universal property of the terminal SST.
def SST.⊤.intro (A : SST) : SST.Hom A SST.⊤ := [
| .z ↦ _ ↦ ()
| .s ↦ a ↦ SST.⊤.intro⁽ᵈ⁾ A (A .s a)
]

{`
## The initial SST
`}

` The initial SST.
def SST.⊥ : SST := [
| .z ↦ ⊥
| .s ↦ ff ↦ SST.⊥⁽ᵈ⁾
]

` Universal property of the initial SST.
def SST.⊥.elim (A : SST) : SST.Hom SST.⊥ A := [
| .z ↦ ff ↦ absurd (A .z) ff
| .s ↦ ff ↦ SST.⊥.elim⁽ᵈ⁾ A (A .s (absurd (A .z) ff))
]

{`
## Discrete SSTs
`}

` The Discrete SST on a type `X`.
def SST.Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ SST.Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

def SST.Disc.elim (X : Type) (A : SST) (a : X → A .z) : SST.Hom (SST.Disc X) A :=
[
| .z ↦ x ↦ a x
| .s ↦ x ↦
  SST.Disc.elim⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (A .s (a x))
    a (x' ff ↦
        absurd
          (A .s (a x) .z (a x'))
          (ff .ungel))
]

def ▲₀ : SST := SST.Disc ⊤

{`
## Constant display
`}

` Trivially display a semisimplicial type over another SST;
` this corresponds to the bundle `A × B → A`.
def SST.Const (A B : SST) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (_ ↦ B .z)
| .s ↦ a b ↦ sym (SST.Const⁽ᵈ⁾ A (A .s a) B (B .s (b .ungel)))
]

` A common pattern is to display `⊤` over `A`; this corresponds to
` the identity bundle `A → A`.
def SST.Id (A : SST) : SST⁽ᵈ⁾ A := SST.Const A SST.⊤

` Maps `Id → B'` over `f : A → B` are given by f-relative sections of `B`.
def SST.Id.of_section
  (A B : SST)
  (B' : SST⁽ᵈ⁾ B)
  (f : SST.Hom A B)
  (s : SST.Section A B B' f)
  : SST.Hom⁽ᵈ⁾ A (SST.Id A) B B' f :=
[
| .z ↦ a tt ↦ s .z a
| .s ↦ a tt ↦
  sym
    (SST.Id.of_section⁽ᵈ⁾
      A (A .s a)
      B (B .s (f .z a))
      B' (sym (B' .s (f .z a) (s .z a)))
      f (f .s a)
      s (s .s a))
]

` Conversely, maps `Id → B'` over `f : A → B` yield sections of `B`.
def SST.Id.to_section
  (A B : SST)
  (B' : SST⁽ᵈ⁾ B)
  (f : SST.Hom A B)
  (f' : SST.Hom⁽ᵈ⁾ A (SST.Id A) B B' f)
  : SST.Section A B B' f :=
[
| .z ↦ a ↦ f' .z a (ungel := ())
| .s ↦ a ↦
  SST.Id.to_section⁽ᵈ⁾
    A (A .s a)
    B (B .s (f .z a))
    B' (sym (B' .s (f .z a) (f' .z a (ungel := ()))))
    f (f .s a)
    f' (sym (f' .s a (ungel := ())))
]

` It is also common to display `⊥` over `A`; this has the effect
` of forming the trivial bundle `⊥ → A`.
def SST.Trivial (A : SST) : SST⁽ᵈ⁾ A := SST.Const A SST.⊥

` Universal property of the trivial bundle.
def SST.Trivial.elim
  (A B : SST) (f : SST.Hom A B)
  (B' : SST⁽ᵈ⁾ B)
  : SST.Hom⁽ᵈ⁾ A (SST.Trivial A) B B' f :=
[
| .z ↦ a ff ↦ match (ff .ungel) []
| .s ↦ a ff ↦ match (ff .ungel) []
]

{`
# Joins
`}

` Attach a pair of maps together.
def SST.Link
  (A B C : SST)
  (f : SST.Hom A C) (g : SST.Hom B C)
  : Type
  :=
codata [
| L .z :
  (a : A .z) →
  SST.Hom⁽ᵈ⁾ B (SST.Id B) C (C .s (f .z a)) g
| L .s :
  (a : A .z) →
  SST.Link⁽ᵈ⁾
    A (A .s a)
    B (SST.Id B)
    C (C .s (f .z a))
    f (f .s a)
    g (L .z a)
    L
]

def SST.Join (X : Type) (A : X → SST) (B : SST) : SST := [
| .z ↦ (Σ X (x ↦ A x .z)) ⊔ B .z
| .s ↦ [
  | inl. xa ↦
    SST.Join⁽ᵈ⁾
      X (Gel X (x ↦ Path X (xa .fst) x))
      A (x p ↦
          Path.rec
            X (x' ↦ SST⁽ᵈ⁾ (A x'))
            (xa .fst) x (p .ungel)
            (A (xa .fst) .s (xa .snd)))
      B (SST.Id B)
  | inr. b ↦
    SST.Join⁽ᵈ⁾
      X (Gel X (_ ↦ ⊥))
      A (x ff ↦
          absurd
            (SST⁽ᵈ⁾ (A x))
            (ff .ungel))
      B (B .s b)
  ]
]

def SST.Join.rec
  (X : Type)
  (A : X → SST)
  (B C : SST)
  (f : (x : X) → SST.Hom (A x) C)
  (g : SST.Hom B C)
  (L : (x : X) → SST.Link (A x) B C (f x) g)
  : SST.Hom (SST.Join X A B) C :=
[
| .z ↦ [
  | inl. xa ↦ f (xa .fst) .z (xa .snd)
  | inr. b ↦ g .z b
  ]
| .s ↦ [
  | inl. xa ↦
    SST.Join.rec⁽ᵈ⁾
      X (Gel X (x ↦ Path X (xa .fst) x))
      A (x p ↦
        Path.rec
          X (x' ↦ SST⁽ᵈ⁾ (A x'))
          (xa .fst) x (p .ungel)
          (A (xa .fst) .s (xa .snd)))
      B (SST.Id B)
      C (C .s (f (xa .fst) .z (xa .snd)))
      f (x p ↦
        Path.elim X (xa .fst)
          (x p ↦
            SST.Hom⁽ᵈ⁾
              (A x)
              (Path.rec X (x' ↦ SST⁽ᵈ⁾ (A x')) (xa .fst) x p (A (xa .fst) .s (xa .snd)))
              C
              (C .s (f (xa .fst) .z (xa .snd)))
              (f x))
          (f (xa .fst) .s (xa .snd))
          x
          (p .ungel))
      g (L (xa .fst) .z (xa .snd))
      L (x p ↦
        Path.elim X (xa .fst)
          (x p ↦
            SST.Link⁽ᵈ⁾
              (A x) (Path.rec X (x' ↦ SST⁽ᵈ⁾ (A x')) (xa .fst) x p (A (xa .fst) .s (xa .snd)))
              B (SST.Id B)
              C (C .s (f (xa .fst) .z (xa .snd))) (f x)
              (Path.elim X (xa .fst)
                 (x0 p0 ↦
                  SST.Hom⁽ᵈ⁾ (A x0)
                    (Path.rec X (x' ↦ SST⁽ᵈ⁾ (A x')) (xa .fst) x0 p0
                       (A (xa .fst) .s (xa .snd))) C
                    (C .s (f (xa .fst) .z (xa .snd))) (f x0))
                 (f (xa .fst) .s (xa .snd)) x p)
              g (L (xa .fst) .z (xa .snd))
              (L x))
          (L (xa .fst) .s (xa .snd))
          x
          (p .ungel))
  | inr. b ↦
    SST.Join.rec⁽ᵈ⁾
      X (Gel X (_ ↦ ⊥))
      A (x ff ↦ absurd (SST⁽ᵈ⁾ (A x)) (ff .ungel))
      B (B .s b)
      C (C .s (g .z b))
      f (x ff ↦
        absurd
          (SST.Hom⁽ᵈ⁾
            (A x) (absurd (SST⁽ᵈ⁾ (A x)) (ff .ungel))
            C (C .s (g .z b))
            (f x))
         (ff .ungel))
      g (g .s b)
      L (x ff ↦
        absurd
          (SST.Link⁽ᵈ⁾
            (A x) (absurd (SST⁽ᵈ⁾ (A x)) (ff .ungel))
            B (B .s b)
            C (C .s (g .z b)) (f x)
            (absurd
               (SST.Hom⁽ᵈ⁾ (A x) (absurd (SST⁽ᵈ⁾ (A x)) (ff .ungel)) C
                  (C .s (g .z b)) (f x)) (ff .ungel)) g (g .s b) (L x))
          (ff .ungel))
  ]
]

def SST.Join.inl
  (X : Type) (A : X → SST) (B : SST) (x : X)
  : SST.Hom (A x) (SST.Join X A B) :=
[
| .z ↦ a ↦ inl. (x, a)
| .s ↦ a ↦
  SST.Join.inl⁽ᵈ⁾
    X (Gel X (x' ↦ Path X x x'))
    A (x' p ↦
        Path.rec
          X (x' ↦ SST⁽ᵈ⁾ (A x'))
          x x' (p .ungel)
          (A x .s a))
    B (SST.Id B)
    x (ungel := refl.)
]

def SST.Join.inr
  (X : Type) (A : X → SST) (B : SST)
  : SST.Hom B (SST.Join X A B) :=
[
| .z ↦ b ↦ inr. b
| .s ↦ b ↦
  SST.Join.inr⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (x ff ↦ absurd (SST⁽ᵈ⁾ (A x)) (ff .ungel))
    B (B .s b)
]

