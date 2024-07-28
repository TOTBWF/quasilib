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

def SST.Elim (A B : SST) : Type := codata [
| f .z : SST.Hom A B
| f .s : (Mot : SST⁽ᵈ⁾ B) (a : A .z) → SST.Elim⁽ᵈ⁾ A (A .s a) B Mot f
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
` Morally, a section `p : Section Γ A P a` can be thought of as a term of a dependent
` type `Γ ⊢ p : P(a)`.
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
def SST.⊥.rec (A : SST) : SST.Hom SST.⊥ A := [
| .z ↦ ff ↦ absurd (A .z) ff
| .s ↦ ff ↦ SST.⊥.rec⁽ᵈ⁾ A (A .s (absurd (A .z) ff))
]

def SST.⊥.elim (A : SST) : SST.Elim SST.⊥ A := [
| .z ↦ SST.⊥.rec A
| .s ↦ Mot a ↦ SST.⊥.elim⁽ᵈ⁾ A Mot
]

{`
## Discrete SSTs
`}

` The Discrete SST on a type `X`.
def SST.Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ SST.Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

def SST.Disc.rec (X : Type) (A : SST) (a : X → A .z) : SST.Hom (SST.Disc X) A :=
[
| .z ↦ x ↦ a x
| .s ↦ x ↦
  SST.Disc.rec⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (A .s (a x))
    a (x' ff ↦
        absurd
          (A .s (a x) .z (a x'))
          (ff .ungel))
]

def SST.Disc.elim (X : Type) (A : SST) (pt : X → A .z) : SST.Elim (SST.Disc X) A := [
| .z ↦ SST.Disc.rec X A pt
| .s ↦ Mot x ↦
  SST.Disc.elim⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A Mot
    pt (x ff ↦ absurd (Mot .z (pt x)) (ff .ungel))
]

def SST.▲₀ : SST := SST.Disc ⊤

def SST.▲₀.elim (A : SST) (pt : A .z) : SST.Elim SST.▲₀ A :=
  SST.Disc.elim ⊤ A (_ ↦ pt)

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
def SST.Trivial.rec
  (A B : SST) (f : SST.Hom A B)
  (B' : SST⁽ᵈ⁾ B)
  : SST.Hom⁽ᵈ⁾ A (SST.Trivial A) B B' f :=
[
| .z ↦ a ff ↦ match (ff .ungel) []
| .s ↦ a ff ↦ match (ff .ungel) []
]

def SST.Trivial.elim
  (A B : SST)
  (f : SST.Hom A B)
  (P : SST⁽ᵈ⁾ B)
  (e : SST.Elim A B)
  : SST.Elim⁽ᵈ⁾ A (SST.Trivial A) B P e :=
[
| .z ↦ [
  | .z ↦ a ff ↦ match (ff .ungel) []
  | .s ↦ a ff ↦ match (ff .ungel) []
  ]
| .s ↦ Q R a ff ↦ match (ff .ungel) []
]
` def SST.Trivial.elim
`   (A : SST)
`   (B : SST) (B' : SST⁽ᵈ⁾ B)
`   (f : SST.Hom A B)
`   (E : SST⁽ᵈ⁾ B) (E' : SST⁽ᵈᵈ⁾ B B' E)
`   (s : SST.Section A B E f)
`   : SST.Section⁽ᵈ⁾
`     A (SST.Trivial A)
`     B B'
`     E E'
`     f (SST.Trivial.rec A B f B')
`     s
`   :=
` [
` | .z ↦ a ff ↦ match (ff .ungel) []
` | .s ↦ a ff ↦ match (ff .ungel) []
` ]

{`
# Eliminators
`}

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
| l .z :
  (a : A .z) → SST.Section B C (C .s (f .z a)) g
| l .s :
  (a : A .z) →
  SST.Link⁽ᵈ⁾
    A (A .s a)
    B (SST.Id B)
    C (C .s (f .z a))
    f (f .s a)
    g (SST.Id.of_section B C (C .s (f .z a)) g (l .z a))
    l
]

def SST.Link.disc
  (X : Type) (A B : SST)
  (f : X → B .z)
  (g : SST.Hom A B)
  (l₀ : (x : X) → SST.Section A B (B .s (f x)) g)
  : SST.Link (SST.Disc X) A B (SST.Disc.rec X B f) g :=
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
    g (SST.Id.of_section A B (B .s (f x)) g (l₀ x))
    l₀ (x' ff ↦
      absurd
        (SST.Section⁽ᵈ⁾
          A (SST.Id A)
          B (B .s (f x))
          (B .s (f x')) (B .s (f x) .s (f x') (absurd (B .s (f x) .z (f x')) (ff .ungel)))
          g (SST.Id.of_section A B (B .s (f x)) g (l₀ x)) (l₀ x'))
        (ff .ungel))
]

def SST.Link.trivial
  (A : SST)
  (B : SST) (B' : SST⁽ᵈ⁾ B)
  (C : SST) (C' : SST⁽ᵈ⁾ C)
  (f : SST.Hom A C)
  (g : SST.Hom B C) (g' : SST.Hom⁽ᵈ⁾ B B' C C' g)
  (l : SST.Link A B C f g)
  : SST.Link⁽ᵈ⁾
    A (SST.Trivial A)
    B B'
    C C'
    f (SST.Trivial.rec A C f C')
    g g'
    l
  :=
[
| .z ↦ a ff ↦ match (ff .ungel) []
| .s ↦ a ff ↦ match (ff .ungel) []
]

def SST.LinkP
  (A B : SST)
  (C : SST) (C' : SST⁽ᵈ⁾ C)
  (f : SST.Hom A C) (sf : SST.Section A C C' f)
  (g : SST.Hom B C) (sg : SST.Section B C C' g)
  (l : SST.Link A B C f g)
  : Type :=
codata [
| l' .z :
  (a : A .z) →
  SST.Section⁽ᵈ⁾
    B (SST.Id B)
    C (C .s (f .z a))
    C' (sym (C' .s (f .z a) (sf .z a)))
    g (SST.Id.of_section B C (C .s (f .z a)) g (l .z a))
    sg
| l' .s :
  (a : A .z) →
  SST.LinkP⁽ᵈ⁾
    A (A .s a)
    B (SST.Id B)
    C (C .s (f .z a))
    C' (sym (C' .s (f .z a) (sf .z a)))
    f (f .s a)
    sf (sf .s a)
    g (SST.Id.of_section B C (C .s (f .z a)) g (l .z a))
    sg (l' .z a)
    l (l .s a)
    l'
]

def SST.LinkP.disc
  (X : Type)
  (A : SST)
  (B : SST) (B' : SST⁽ᵈ⁾ B)
  (pt : X → B .z) (pt' : (x : X) → B' .z (pt x))
  (f : SST.Hom A B) (sf : SST.Section A B B' f)
  (s : (x : X) →
    SST.Section A B (B .s (pt x)) f)
  (s' : (x : X) →
    SST.Section⁽ᵈ⁾
      A (SST.Id A)
      B (B .s (pt x))
      B' (sym (B' .s (pt x) (pt' x)))
      f (SST.Id.of_section A B (B .s (pt x)) f (s x))
      sf)
  : SST.LinkP
    (SST.Disc X) A
    B B'
    (SST.Disc.rec X B pt)
    (SST.Disc.elim X B B' pt pt')
    f sf
    (SST.Link.disc X A B pt f s)
  :=
[
| .z ↦ x ↦ s' x
| .s ↦ x ↦
  SST.LinkP.disc⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (SST.Id A)
    B (B .s (pt x))
    B' (sym (B' .s (pt x) (pt' x)))
    pt (x' ff ↦ absurd (B .s (pt x) .z (pt x')) (ff .ungel))
    pt' (x' ff ↦
      absurd
        (sym (B' .s (pt x) (pt' x)) .z (pt x') (absurd (B .s (pt x) .z (pt x')) (ff .ungel)) (pt' x'))
        (ff .ungel))
    f (SST.Id.of_section A B (B .s (pt x)) f (s x))
    sf (SST.LinkP.disc X A B B' pt pt' f sf s s' .z x)
    s (x' ff ↦
      absurd
        (SST.Section⁽ᵈ⁾ A (SST.Const A SST.⊤) B (B .s (pt x)) (B .s (pt x'))
         (B .s (pt x) .s (pt x')
            (absurd (B .s (pt x) .z (pt x')) (ff .ungel))) f
         (SST.Id.of_section A B (B .s (pt x)) f (s x)) (s x'))
        (ff .ungel))
     s' (x' ff ↦
       absurd
         (SST.Section⁽ᵈᵈ⁾ A (SST.Const A SST.⊤) (SST.Const A SST.⊤)
         (SST.Const⁽ᵈ⁾ A (SST.Const A SST.⊤) SST.⊤ SST.⊤⁽ᵈ⁾) B (B .s (pt x))
         (B .s (pt x'))
         (B .s (pt x) .s (pt x')
            (absurd (B .s (pt x) .z (pt x')) (ff .ungel))) B'
         (sym (B' .s (pt x) (pt' x))) (sym (B' .s (pt x') (pt' x')))
         (sym (B' .s (pt x) (pt' x)) .s (pt x')
            (absurd (B .s (pt x) .z (pt x')) (ff .ungel)) (pt' x')
            (absurd
               (sym (B' .s (pt x) (pt' x)) .z (pt x')
                  (absurd (B .s (pt x) .z (pt x')) (ff .ungel)) (pt' x'))
               (ff .ungel)))⁽¹³²⁾ f
         (SST.Id.of_section A B (B .s (pt x)) f (s x))
         (SST.Id.of_section A B (B .s (pt x')) f (s x'))
         (SST.Id.of_section⁽ᵈ⁾ A (SST.Const A SST.⊤) B (B .s (pt x))
            (B .s (pt x'))
            (B .s (pt x) .s (pt x')
               (absurd (B .s (pt x) .z (pt x')) (ff .ungel))) f
            (SST.Id.of_section A B (B .s (pt x)) f (s x)) (s x')
            (absurd
               (SST.Section⁽ᵈ⁾ A (SST.Const A SST.⊤) B (B .s (pt x))
                  (B .s (pt x'))
                  (B .s (pt x) .s (pt x')
                     (absurd (B .s (pt x) .z (pt x')) (ff .ungel))) f
                  (SST.Id.of_section A B (B .s (pt x)) f (s x)) (s x'))
               (ff .ungel))) sf (s' x) (s' x'))
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
      g (SST.Id.of_section B C (C .s (f .z a)) g (l .z a))
      l (l .s a)
  | inr. b ↦
    SST.Join.rec⁽ᵈ⁾
      A (SST.Trivial A)
      B (B .s b)
      C (C .s (g .z b))
      f (SST.Trivial.rec A C f (C .s (g .z b)))
      g (g .s b)
      l (SST.Link.trivial A B (B .s b) C (C .s (g .z b)) f g (g .s b) l)
  ]
]

def SST.Join.elim
  (A B C : SST)
  (f : SST.Hom A C)
  (g : SST.Hom B C)
  (l : SST.Link A B C f g)
  (C' : SST⁽ᵈ⁾ C)
  (sf : SST.Section A C C' f)
  (sg : SST.Section B C C' g)
  (l' : SST.LinkP A B C C' f sf g sg l)
  : SST.Section (SST.Join A B) C C' (SST.Join.rec A B C f g l) :=
[
| .z ↦ [
  | inl. a ↦ sf .z a
  | inr. b ↦ sg .z b
  ]
| .s ↦ [
  | inl. a ↦
    SST.Join.elim⁽ᵈ⁾
      A (A .s a)
      B (SST.Id B)
      C (C .s (f .z a))
      f (f .s a)
      g (SST.Id.of_section B C (C .s (f .z a)) g (l .z a))
      l (l .s a)
      C' (sym (C' .s (f .z a) (sf .z a)))
      sf (sf .s a)
      sg (l' .z a)
      l' (l' .s a)
  | inr. b ↦
    SST.Join.elim⁽ᵈ⁾
      A (SST.Trivial A)
      B (B .s b)
      C (C .s (g .z b))
      f (SST.Trivial.rec A C f (C .s (g .z b)))
      g (g .s b)
      l (SST.Link.trivial A B (B .s b) C (C .s (g .z b)) f g (g .s b) l)
      C' (sym (C' .s (g .z b) (sg .z b)))
      sf (SST.Trivial.elim
        A
        C (C .s (g .z b))
        f
        C' (sym (C' .s (g .z b) (sg .z b)))
        sf)
      sg (sg .s b)
      l' ? `(SST.LinkP.disc)
  ]
]

def SST.Cone (A : SST) := SST.Join (SST.▲₀) A
def SST.Cocone (A : SST) := SST.Join A SST.▲₀

def SST.Cone.rec
  (A B : SST)
  (pt : B .z)
  (f : SST.Hom A B)
  (l₀ : SST.Section A B (B .s pt) f)
  : SST.Hom (SST.Cone A) B :=
SST.Join.rec
  SST.▲₀ A B
  (SST.Disc.rec ⊤ B (_ ↦ pt))
  f
  (SST.Link.disc ⊤ A B (_ ↦ pt) f (_ ↦ l₀))

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

def SST.▲.rec
  (n : Nat)
  (A : SST)
  (○a : ○ n A)
  (●a : ● n A ○a)
  : SST.Hom (SST.▲ n) A :=
match n [
| zero. ↦ SST.Disc.rec ⊤ A (_ ↦ ●a)
| suc. n ↦
  SST.Cone.rec
    (SST.▲ n) A
    (○a .pt)
    (SST.▲.rec n A (○a .∂a) (○a .a))
    (SST.▲.elim n A (○a .pt) (○a .∂a) (○a .∂a') (○a .a) ●a)
]

and SST.▲.elim
  (n : Nat)
  (A : SST)
  (pt : A .z)
  (○a : ○ n A)
  (○a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ○a)
  (●a : ● n A ○a)
  (●a' : ●⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ○a ○a' ●a)
  : SST.Section (SST.▲ n) A (A .s pt) (SST.▲.rec n A ○a ●a) :=
match n [
| zero. ↦ SST.Disc.elim ⊤ A (A .s pt) (_ ↦ ●a) (_ ↦ ●a')
| suc. n ↦
  SST.Join.elim
    SST.▲₀ (SST.▲ n) A
    (SST.Disc.rec ⊤ A (_ ↦ ○a .pt))
    (SST.▲.rec n A (○a .∂a) (○a .a))
    (SST.Link.disc ⊤ (SST.▲ n) A
      (_ ↦ ○a .pt)
      (SST.▲.rec n A (○a .∂a) (○a .a))
      (_ ↦ SST.▲.elim n A (○a .pt) (○a .∂a) (○a .∂a') (○a .a) ●a))
    (A .s pt)
    (SST.Disc.elim ⊤ A (A .s pt) (_ ↦ ○a .pt) (_ ↦ ○a' .pt))
    (SST.▲.elim n A pt (○a .∂a) (○a' .∂a) (○a .a) (○a' .a))
    ?
    ` (SST.LinkP.disc ⊤ (SST.▲ n)
    `   A (A .s pt)
    `   (_ ↦ ○a .pt) (_ ↦ ○a' .pt)
    `   (SST.▲.rec n A (○a .∂a) (○a .a))
    `   (SST.▲.elim n A pt (○a .∂a) (○a' .∂a) (○a .a) (○a' .a))
    `   (_ ↦ SST.▲.elim n A (○a .pt) (○a .∂a) (○a .∂a') (○a .a) ●a)
    `   `(_ ↦ ?)
    `   )
]
