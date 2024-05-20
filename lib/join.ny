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

def SST.▲₀ : SST := SST.Disc ⊤

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

def SST.Link.disc
  (X : Type) (A B : SST)
  (f : X → B .z)
  (g : SST.Hom A B)
  (l₀ : (x : X) → SST.Hom⁽ᵈ⁾ A (SST.Id A) B (B .s (f x)) g)
  : SST.Link (SST.Disc X) A B (SST.Disc.elim X B f) g :=
[
| .z ↦ x ↦ l₀ x
| .s ↦ x ↦
  SST.Link.disc⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (SST.Id A)
    B (B .s (f x))
    f (x' ff ↦
      absurd
        (B .s (f x) .z (f x'))
        (ff .ungel))
    g (l₀ x) `(g .s (f x))
    l₀ (x' ff ↦
      absurd
        (SST.Hom⁽ᵈᵈ⁾ A (SST.Const A SST.⊤) (SST.Const A SST.⊤)
          (SST.Const⁽ᵈ⁾ A (SST.Const A SST.⊤) SST.⊤ SST.⊤⁽ᵈ⁾) B (B .s (f x))
          (B .s (f x'))
          (B .s (f x) .s (f x') (absurd (B .s (f x) .z (f x')) (ff .ungel))) g
          (l₀ x) (l₀ x'))
        (ff .ungel))
]

def SST.Join (A : SST) (B : SST) : SST := [
| .z ↦
  A .z ⊔ B .z
| .s ↦ [
  | inl. a ↦
    SST.Join⁽ᵈ⁾
      A (A .s a)
      B (SST.Id B)
  | inr. b ↦
    SST.Join⁽ᵈ⁾
      A (SST.Trivial A)
      B (B .s b)
  ]
]

def SST.Join.rec
  (A B C : SST)
  (f : SST.Hom A C)
  (g : SST.Hom B C)
  (l : SST.Link A B C f g)
  : SST.Hom (SST.Join A B) C :=
[
| .z ↦ [
  | inl. a ↦ f .z a
  | inr. b ↦ g .z b
  ]
| .s ↦ [
  | inl. a ↦
    SST.Join.rec⁽ᵈ⁾
      A (A .s a)
      B (SST.Id B)
      C (C .s (f .z a))
      f (f .s a)
      g (l .z a)
      l (l .s a)
  | inr. b ↦
    SST.Join.rec⁽ᵈ⁾
      A (SST.Trivial A)
      B (B .s b)
      C (C .s (g .z b))
      f (SST.Trivial.elim A C f (C .s (g .z b)))
      g (g .s b)
      l ?
  ]
]

` TODO: We think that this is the key!
def SST.Join.rec.section
  (A B C : SST)
  (f : SST.Hom A C)
  (g : SST.Hom B C)
  (l : SST.Link A B C f g)
  (C' : SST⁽ᵈ⁾ C)
  (sf : SST.Section A C C' f)
  (sg : SST.Section B C C' g)
  ` This probably needs to be a special type
  (l' : (a : A .z) (b : B .z) → SST.Link⁽ᵈ⁾ A (A .s a) B (B .s b) C ? f (f .s a) (g .s b) l)
  : SST.Section (SST.Join A B) C C' (SST.Join.rec A B C f g l) := ?

def SST.Cone (A : SST) := SST.Join (SST.▲₀) A
def SST.Cocone (A : SST) := SST.Join A SST.▲₀

def SST.Cone.rec
  (A B : SST)
  (pt : B .z)
  (f : SST.Hom A B)
  (l₀ : SST.Section A B (B .s pt) f)
  `(l₀ : SST.Hom⁽ᵈ⁾ A (SST.Id A) B (B .s (pt x)) f)
  : SST.Hom (SST.Cone A) B :=
SST.Join.rec
  SST.▲₀ A B
  (SST.Disc.elim ⊤ B (_ ↦ pt))
  f
  ?
  `(_ ↦ SST.Link.disc ⊤ A B (_ ↦ pt x) f (_ ↦ l₀ x))

{`
# Boundaries and Fillers
`}

` The type of generalized n-dimensional boundaries in an SST `A`.
def ○ (n : Nat) (A : SST) : Type := match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    (pt : A .z
    , ∂a : ○ n A
    , a : ● n A ∂a
    , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ∂a
    )
]

` The type of generalized n-dimensional boundary fillers in an SST `A`.
and ● (n : Nat) (A : SST) (○a : ○ n A) : Type := match n [
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]


{`
# Yoneda
`}

def SST.▲ : Nat → SST :=
[
| zero. ↦ SST.▲₀
| suc. n ↦ SST.Cone (SST.▲ n)
]

def SST.▲.pt (n : Nat) : SST.▲ n .z :=
match n [
| zero. ↦ ()
| suc. n ↦ inl. ()
]

` SST.▲.elim .s (SST.▲.pt n) = ○a .pt

def SST.▲.elim
  (n : Nat)
  (A : SST)
  (○a : ○ n A)
  (●a : ● n A ○a)
  : SST.Hom (SST.▲ n) A :=
match n [
| zero. ↦ SST.Disc.elim ⊤ A (_ ↦ ●a)
| suc. n ↦
  SST.Cone.rec
    (SST.▲ n) A
    (○a .pt)
    (SST.▲.elim n A (○a .∂a) (○a .a))
    (SST.▲.link n A ○a ●a)
]

and SST.▲.link
  (n : Nat)
  (A : SST)
  (○a : ○ (suc. n) A)
  (●a : ● (suc. n) A ○a)
  : SST.Section (SST.▲ n) A (A .s (○a .pt)) (SST.▲.elim n A (○a .∂a) (○a .a)) :=
match n [
| zero. ↦ ? `Easy: ●a has exactly what we need.
| suc. n ↦

  ` Characterize the sections of Join.rec
  SST.▲.link n A (○a .∂a) (○a .a)
]

` def SST.▲.link
`   (n : Nat)
`   (A : SST)
`   (○a : ○ n A)
`   (●a : ● n A ○a)
`   : SST.Hom⁽ᵈ⁾
` ` [
` ` | .z ↦ v ↦ SST.Disc.elim ⊤
` ` | .s ↦ v ↦ ?
` ]
