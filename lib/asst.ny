` ----------------------------------------
` Augmented semi-simplicial types.
` ----------------------------------------
import "prelude"
import "sst"

def ASST : Type :=
codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

section ASST :=
  ` Maps of augmented semi-simplicial types.
  def Hom (X Y : ASST) : Type :=
  codata [
  | f .z : X .z → Y .z
  | f .s : Hom⁽ᵈ⁾ X (X .s) Y (Y .s) f
  ]

  section Hom :=
    ` The identity morphism of ASSTs.
    def id (X : ASST) : Hom X X := [
    | .z ↦ x ↦ x
    | .s ↦ id⁽ᵈ⁾ X (X .s)
    ]

    ` Composition of ASST morphisms.
    def ∘ (X Y Z : ASST) (f : Hom Y Z) (g : Hom X Y) : Hom X Z := [
    | .z ↦ x ↦ f .z (g .z x)
    | .s ↦ ∘⁽ᵈ⁾ X (X .s) Y (Y .s) Z (Z .s) f (f .s) g (g .s)
    ]
  end

  def Lift (A B : ASST) (f : Hom A B) (E : ASST⁽ᵈ⁾ B) : Type :=
  codata [
  | l .z : (a : A .z) → E .z (f .z a)
  | l .s : Lift⁽ᵈ⁾ A (A .s) B (B .s) f (f .s) E (sym (E .s)) l
  ]

  ` Morally, an augmented SST is a family of semi-simplicial types.
  ` This means that we can take the fibre of an augmented SST over a (-1)-simplex.
  def Fibre (A : ASST) (i : A .z) : SST :=
  [
  | .z ↦ A .s .z i
  | .s ↦ x ↦ Fibre⁽ᵈ⁾ A (A .s) i x
  ]

  ` Transform a family of SSTs into an augmented SST.
  def Fam (I : Type) (A : I → SST) : ASST :=
  [
  | .z ↦ I
  | .s ↦ Fam⁽ᵈ⁾ I (Gel I (i ↦ A i .z)) A (i a ↦ A i .s (a .ungel))
  ]

  ` In particular, every SST gives rise an ASST with a single (-1)-simplex.
  def Single (A : SST) : ASST := Fam ⊤ (_ ↦ A)

  ` Total spaces of displayed ASSTs.
  def ∫ (B : ASST) (E : ASST⁽ᵈ⁾ B) : ASST := [
  | .z ↦ Σ (B .z) (b ↦ E .z b)
  | .s ↦ ∫⁽ᵈ⁾ B (B .s) E (sym (E .s))
  ]

  ` Projection out of the total space of an augmented SST.
  def ∫.fst (B : ASST) (E : ASST⁽ᵈ⁾ B) : Hom (∫ B E) B := [
  | .z ↦ ∫e ↦ ∫e .fst
  | .s ↦ ∫.fst⁽ᵈ⁾ B (B .s) E (sym (E .s))
  ]

  ` The second projection out of the total space, bundled as a lift.
  ` Diagramatically:
  `
  `             ^ E
  `            /  |
  `           /   |
  `      snd /    |
  `         /     |
  `        /      |
  `       /       |
  `      /   fst  v
  `   ∫ E B ----> B
  `
  def ∫.snd (B : ASST) (E : ASST⁽ᵈ⁾ B) : Lift (∫ B E) B (∫.fst B E) E := [
  | .z ↦ ∫e ↦ ∫e .snd
  | .s ↦ ∫.snd⁽ᵈ⁾ B (B .s) E (sym (E .s))
  ]

  ` Pullback a displayed ASST along a morphism of ASSTs.
  def Pullback (A B : ASST) (f : Hom A B) (E : ASST⁽ᵈ⁾ B) : ASST⁽ᵈ⁾ A := [
  | .z ↦ Gel (A .z) (a ↦ E .z (f .z a))
  | .s ↦ sym (Pullback⁽ᵈ⁾ A (A .s) B (B .s) f (f .s) E (sym (E .s)))
  ]

  ` The slices of an augmented semi-simplicial type.
  def Slice (A : ASST) : ASST⁽ᵈ⁾ A :=
  [
  | .z ↦ A .s .z
  | .s ↦ sym (Slice⁽ᵈ⁾ A (A .s))
  ]

  ` For completeness, we include a synonym for coslices.
  def Coslice (A : ASST) : ASST⁽ᵈ⁾ A := A .s

  ` Opposite ASSTs.
  def Op (A : ASST) : ASST :=
  [
  | .z ↦ A .z
  | .s ↦ Op⁽ᵈ⁾ A (Slice A)
  ]

  notation 20 Op : A "ᵒᵖ" := Op A

  ` Trivially display an augmented semisimplicial type `B` over another augmented
  ` semisimplicial type `A`. This corresponds to the trivial bundle `A × B → A`.
  def Const (A B : ASST) : ASST⁽ᵈ⁾ A := [
  | .z ↦ Gel (A .z) (_ ↦ B .z)
  | .s ↦ sym (Const⁽ᵈ⁾ A (A .s) B (B .s))
  ]

  ` The universe of types as an augmented semisimplicial type.
  def 𝒰 : ASST := [
  | .z ↦ Type
  | .s ↦ 𝒰⁽ᵈ⁾
  ]

  ` Elements of the universe as a displayed semisimplicial type.
  def El : ASST⁽ᵈ⁾ 𝒰 := [
  | .z ↦ Gel Type (A ↦ A)
  | .s ↦ sym El⁽ᵈ⁾
  ]

  ` Products of ASSTs.
  def Prod (A B : ASST) : ASST := [
  | .z ↦ A .z × B .z
  | .s ↦ Prod⁽ᵈ⁾ A (A .s) B (B .s)
  ]

  notation 6 Prod : A "×ᵃ" B := Prod A B

  section Prod :=
    ` First projection out of a product.
    def fst (A B : ASST) : Hom (A ×ᵃ B) A := [
    | .z ↦ ab ↦ ab .fst
    | .s ↦ fst⁽ᵈ⁾ A (A .s) B (B .s)
    ]

    ` Second projection out of a product.
    def snd (A B : ASST) : Hom (A ×ᵃ B) B := [
    | .z ↦ ab ↦ ab .snd
    | .s ↦ snd⁽ᵈ⁾ A (A .s) B (B .s)
    ]

    ` Universal map into the product.
    def intro (X A B : ASST) (f : Hom X A) (g : Hom X B) : Hom X (A ×ᵃ B) := [
    | .z ↦ x ↦ (f .z x , g .z x)
    | .s ↦ intro⁽ᵈ⁾ X (X .s) A (A .s) B (B .s) f (f .s) g (g .s)
    ]
  end
end
