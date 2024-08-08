` ----------------------------------------
` Semi-simplicial types.
` ----------------------------------------
import "prelude"

` The type of semi-simplicial types.
` Each `X : SST` has a type of `X .z : Type` zero-simplices,
` a displayed type of lines `X .s x : SST⁽ᵈ⁾ X` originating from `x`, and so on.
`
` Note that one should read the type `X .s x .z y` as a line in `X`
` from `x` to `y`.
def SST : Type :=
codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

section SST :=
  ` Maps of semi-simplicial types.
  def Hom (X Y : SST) : Type := codata [
  | f .z : X .z → Y .z
  | f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
  ]

  ` Total spaces.
  def ∫ (B : SST) (E : SST⁽ᵈ⁾ B) : SST := [
  | .z ↦ Σ (B .z) (b ↦ E .z b)
  | .s ↦ ∫e ↦ ∫⁽ᵈ⁾ B (B .s (∫e .fst)) E (sym (E .s (∫e .fst) (∫e .snd)))
  ]

  ` Projection out of the total space.
  def ∫.π (B : SST) (E : SST⁽ᵈ⁾ B) : Hom (∫ B E) B := [
  | .z ↦ ∫e ↦ ∫e .fst
  | .s ↦ ∫e ↦ ∫.π⁽ᵈ⁾ B (B .s (∫e .fst)) E (sym (E .s (∫e .fst) (∫e .snd)))
  ]

  ` Slices in an SST `A` over a vertex `x`.
  ` Note that the definition of SSTs privileges coslicing
  ` over slicing; this means that we need to define the
  ` displayed SST of slices "by hand".
  def Slice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
  [
  | .z ↦ Gel (A .z) (y ↦ A .s y .z x)
  | .s ↦ y α ↦ sym (Slice⁽ᵈ⁾ A (A .s y) x (α .ungel))
  ]

  ` A global element of an SST.
  ` This consists of a 0-simplex `x : A .z`, a loop `α : A .s x .z x`, and so on.
  def Pt (A : SST) : Type := codata [
  | pt .z : A .z
  | pt .s : Pt⁽ᵈ⁾ A (A .s (pt .z)) pt
  ]

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
  def Section (A B : SST) (f : Hom A B) (E : SST⁽ᵈ⁾ B) : Type := codata [
  | S .z : (a : A .z) → E .z (f .z a)
  | S .s : (a : A .z) →
    Section⁽ᵈ⁾
      A (A .s a)
      B (B .s (f .z a))
      f (f .s a)
      E (sym (E .s (f .z a) (S .z a)))
      S
  ]

  ` We can also give sections of E along `f : A → B` as an SST displayed over A;
  ` intuitively, this is the pullback of `E → B` along `f`.
  def Pullback (A B : SST) (f : Hom A B) (E : SST⁽ᵈ⁾ B) : SST⁽ᵈ⁾ A := [
  | .z ↦ Gel (A .z) (a ↦ E .z (f .z a))
  | .s ↦ a e ↦
    sym (Pullback⁽ᵈ⁾
      A (A .s a)
      B (B .s (f .z a))
      f (f .s a)
      E (sym (E .s (f .z a) (e .ungel))))
  ]


  ` Trivially display a semisimplicial type `B` over another semisimplicial type `A`.
  ` This corresponds to the bundle `A × B → A`.
  def Const (A B : SST) : SST⁽ᵈ⁾ A := [
  | .z ↦ Gel (A .z) (_ ↦ B .z)
  | .s ↦ a b ↦ sym (Const⁽ᵈ⁾ A (A .s a) B (B .s (b .ungel)))
  ]

  ` The terminal SST.
  def Unit : SST := [
  | .z ↦ ⊤
  | .s ↦ _ ↦ Unit⁽ᵈ⁾
  ]

  section Unit :=
    ` The universal map into the terminal SST.
    def intro (A : SST) : Hom A Unit := [
    | .z ↦ _ ↦ ()
    | .s ↦ a ↦ intro⁽ᵈ⁾ A (A .s a)
    ]

    ` Maps from the unit type are given by global elements.
    def recurse (A : SST) (pt : Pt A) : Hom Unit A := [
    | .z ↦ _ ↦ pt .z
    | .s ↦ _ ↦
      recurse⁽ᵈ⁾
        A (A .s (pt .z))
        pt (pt .s)
    ]
  end

  ` A common pattern is to display `Unit` over `A`; this corresponds to
  ` the identity bundle `A → A`.
  def Id (A : SST) : SST⁽ᵈ⁾ A := Const A Unit

  ` The initial SST.
  def Empty : SST := [
  | .z ↦ ⊥
  | .s ↦ _ ↦ Empty⁽ᵈ⁾
  ]

  section Empty :=
    ` Universal property of the initial SST.
    def recurse (A : SST) : Hom Empty A := [
    | .z ↦ ff ↦ absurd (A .z) ff
    | .s ↦ ff ↦ recurse⁽ᵈ⁾ A (A .s (absurd (A .z) ff))
    ]
  end

  ` It is also common to display `Empty` over `A`; this has the effect
  ` of forming the trivial bundle `⊥ → A`.
  def Trivial (A : SST) : SST⁽ᵈ⁾ A := Const A Empty

  section Trivial :=
    def recurse
      (A B : SST) (f : Hom A B)
      (B' : SST⁽ᵈ⁾ B)
      : Hom⁽ᵈ⁾ A (Trivial A) B B' f := [
      | .z ↦ a ff ↦ match (ff .ungel) []
      | .s ↦ a ff ↦ match (ff .ungel) []
      ]
  end

  ` The product of semisimplicial types.
  def Prod (A B : SST) : SST := [
  | .z ↦ sig (fst : A .z, snd : B .z)
  | .s ↦ ab ↦ Prod⁽ᵈ⁾ A (A .s (ab .fst)) B (B .s (ab .snd))
  ]

  section Prod :=
    ` The first projection out of a product.
    def fst (A B : SST) : Hom (Prod A B) A := [
    | .z ↦ ab ↦ ab .fst
    | .s ↦ ab ↦ fst⁽ᵈ⁾ A (A .s (ab .fst)) B (B .s (ab .snd))
    ]

    ` The second projection out of a product.
    def snd (A B : SST) : Hom (Prod A B) B := [
    | .z ↦ ab ↦ ab .snd
    | .s ↦ ab ↦ snd⁽ᵈ⁾ A (A .s (ab .fst)) B (B .s (ab .snd))
    ]

    ` The universal property of the product.
    def intro (X A B : SST) (f : Hom X A) (g : Hom X B) : Hom X (Prod A B) := [
    | .z ↦ x ↦ (fst := f .z x, snd := g .z x)
    | .s ↦ x ↦
      intro⁽ᵈ⁾
        X (X .s x)
        A (A .s (f .z x))
        B (B .s (g .z x))
        f (f .s x)
        g (g .s x)
    ]
  end

  ` The coproduct of two semisimplicial types.
  def Coprod (A B : SST) : SST := [
  | .z ↦ A .z ⊎ B .z
  | .s ↦ [
    | inl. a ↦ Coprod⁽ᵈ⁾ A (A .s a) B (Trivial B)
    | inr. b ↦ Coprod⁽ᵈ⁾ A (Trivial A) B (B .s b)
    ]
  ]

  section Coprod :=
    ` Left inclusion into the coproduct.
    def inl (A B : SST) : Hom A (Coprod A B) := [
    | .z ↦ a ↦ inl. a
    | .s ↦ a ↦ inl⁽ᵈ⁾ A (A .s a) B (Trivial B)
    ]

    ` Right inclusion into the coproduct.
    def inr (A B : SST) : Hom B (Coprod A B) := [
    | .z ↦ b ↦ inr. b
    | .s ↦ b ↦ inr⁽ᵈ⁾ A (Trivial A) B (B .s b)
    ]

    ` Universal property of the coproduct.
    def recurse (A B X : SST) (f : Hom A X) (g : Hom B X) : Hom (Coprod A B) X := [
    | .z ↦ [
      | inl. a ↦ f .z a
      | inr. b ↦ g .z b
      ]
    | .s ↦ [
      | inl. a ↦
          recurse⁽ᵈ⁾
            A (A .s a)
            B (Trivial B)
            X (X .s (f .z a))
            f (f .s a)
            g (Trivial.recurse B X g (X .s (f .z a)))
      | inr. b ↦
          recurse⁽ᵈ⁾
            A (Trivial A)
            B (B .s b)
            X (X .s (g .z b))
            f (Trivial.recurse A X f (X .s (g .z b)))
            g (g .s b)
      ]
    ]
  end

  ` The discrete SST on a type `X`, where every dimension higher than 0 is empty.
  def Disc (X : Type) : SST := [
  | .z ↦ X
  | .s ↦ x ↦ Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
  ]

  section Disc :=
    ` Maps `Disc X → A` are given by maps into the 0-dimensional data of `A`.
    def recurse (X : Type) (A : SST) (f : X → A .z) : Hom (Disc X) A := [
    | .z ↦ x ↦ f x
    | .s ↦ x ↦
      recurse⁽ᵈ⁾
        X (Gel X (_ ↦ ⊥))
        A (A .s (f x))
        f (_ ff ↦ match (ff .ungel) [])
    ]
  end

  ` The codiscrete SST on a type `X`, where every dimension higher than 0 is trivial.
  def Codisc (X : Type) : SST := [
  | .z ↦ X
  | .s ↦ x ↦ Codisc⁽ᵈ⁾ X (Gel X (_ ↦ ⊤))
  ]

  section Codisc :=
    ` Maps `A → Codisc X` are given by maps from the 0-dimensional data of `A`.
    def recurse (A : SST) (X : Type) (f : A .z → X) : Hom A (Codisc X) := [
    | .z ↦ a ↦ f a
    | .s ↦ a ↦
      recurse⁽ᵈ⁾
        A (A .s a)
        X (Gel X (_ ↦ ⊤))
        f (_ _ ↦ (ungel := ()))
    ]
  end

  ` The opposite of an SST.
  def Op (A : SST) : SST :=
  [
  | .z ↦ A .z
  | .s ↦ x ↦ Op⁽ᵈ⁾ A (Slice A x)
  ]
end
