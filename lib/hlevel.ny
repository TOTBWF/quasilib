import "prelude"
import "retract"
import "path"

def IsContr (A : Type) : Type :=
  sig (centre : A, paths : (x : A) → Path A centre x)

def IsProp (A : Type) : Type :=
  (x y : A) → Path A x y

def IsHLevel (A : Type) (n : Nat) : Type :=
match n [
| zero. ↦ IsContr A
| suc. zero. ↦ IsProp A
| suc. (suc. n) ↦ (x y : A) → IsHLevel (Path A x y) (suc. n)
]

def IsSet (A : Type) : Type := IsHLevel A 2

` Every contractible type is a proposition.
def IsContr.prop
  (A : Type)
  (acontr : IsContr A)
  : IsProp A :=
  x y ↦
    Path.trans A x (acontr .centre) y
      (Path.sym A x (acontr .centre) (acontr .paths x))
      (acontr .paths y)


` ----------------------------------------
` HLevels are closed under retracts.
` ----------------------------------------

` Retracts of contractible types are contractible.
def IsContr.retract
  (A B : Type)
  (r : Retraction A B)
  (acontr : IsContr A)
  : IsContr B :=
( centre := r .retr (acontr .centre)
, paths := b ↦
    Path.trans B
      (r .retr (acontr .centre)) (r .retr (r .sect b)) b
      (cong A B (r .retr) (acontr .centre) (r .sect b) (acontr .paths (r .sect b)))
      (r .invl b)
)

` Retracts of propositions are contractible.
def IsProp.retract
  (A B : Type)
  (r : Retraction A B)
  (aprop : IsProp A)
  : IsProp B :=
    b1 b2 ↦ Path.retract A B b1 b2 r .retr (aprop (r .sect b1) (r .sect b2))

` General HLevel closure under retracts.
def IsHLevel.retract
  (A B : Type) (n : Nat)
  (r : Retraction A B)
  (ahl : IsHLevel A n)
  : IsHLevel B n :=
match n [
| zero. ↦ IsContr.retract A B r ahl
| suc. zero. ↦ IsProp.retract A B r ahl
| suc. (suc. n) ↦ x y ↦
  IsHLevel.retract
    (Path A (r .sect x) (r .sect y)) (Path B x y) (suc. n)
    (Path.retract A B x y r)
    (ahl (r .sect x) (r .sect y))
]

` ----------------------------------------
` HLevels of pairs
` ----------------------------------------

def Pair.contr (A B : Type) (acontr : IsContr A) (bcontr : IsContr B) : IsContr (A × B) :=
  ( centre := (acontr .centre , bcontr .centre)
  , paths := ab ↦
    Pair.path
      A B
      (acontr .centre , bcontr .centre) ab
      (acontr .paths (ab .fst)) (bcontr .paths (ab .snd))
  )

def Pair.prop (A B : Type) (aprop : IsProp A) (bprop : IsProp B) : IsProp (A × B) :=
  ab xy ↦ Pair.path A B ab xy (aprop (ab .fst) (xy .fst)) (bprop (ab .snd) (xy .snd))

def Pair.hlevel
  (A B : Type) (n : Nat)
  (ahl : IsHLevel A n) (bhl : IsHLevel B n)
  : IsHLevel (A × B) n :=
match n [
| zero. ↦
  Pair.contr A B ahl bhl
| suc. zero. ↦
  Pair.prop A B ahl bhl
| suc. (suc. n) ↦ x y ↦
  IsHLevel.retract
    (Path A (x .fst) (y .fst) × Path B (x .snd) (y .snd))
    (Path (A × B) x y) (suc. n)
    ( retr := p ↦ Pair.path A B x y (p .fst) (p .snd)
    , sect := p ↦ (cong (A × B) A (xy ↦ xy .fst) x y p, cong (A × B) B (xy ↦ xy .snd) x y p)
    , invl := p ↦ match p [
      | refl. ↦ refl.
      ]
    )
    (Pair.hlevel
      (Path A (x .fst) (y .fst)) (Path B (x .snd) (y .snd)) (suc. n)
      (ahl (x .fst) (y .fst)) (bhl (x .snd) (y .snd)))
]

` ----------------------------------------
` HLevels of gel types
` ----------------------------------------

def Gel.contr
  (A : Type) (B : A → Type)
  (acontr : IsContr A) (bcontr : IsContr (B (acontr .centre)))
  : IsContr⁽ᵈ⁾ A (Gel A B) acontr :=
  ( centre := (ungel := bcontr .centre)
  , paths := a b ↦
    Gel.path A B
      (acontr .centre) (ungel := bcontr .centre)
      a b
      (acontr .paths a)
      (J A (acontr .centre)
        (a p ↦ (b : B a) → Path (B a) (subst A B (acontr .centre) a p (bcontr .centre)) b)
        (bcontr .paths)
        a
        (acontr .paths a)
        (b .ungel)
        )
  )

def Gel.prop
  (A : Type) (B : A → Type)
  (aprop : IsProp A) (bprop : (a : A) → IsProp (B a))
  : IsProp⁽ᵈ⁾ A (Gel A B) aprop :=
  a0 b0 a1 b1 ↦
    Gel.path A B
      a0 b0
      a1 b1
      (aprop a0 a1)
      (J A a0
        (a1 p ↦ (b1 : B a1) → Path (B a1) (subst A B a0 a1 p (b0 .ungel)) b1)
        (bprop a0 (b0 .ungel))
        a1
        (aprop a0 a1)
        (b1 .ungel))

` This proof is problematic!
` The basic problem boils down to an indexing issue:
` We want to use the normal trick of using a retract to
` adjust the path types in the recursive case. In this case,
` we do have a nice equivalence between Path⁽ᵈ⁾ in a Gel type
` and PathP, but IsHLevel.retract⁽ᵈ⁾ puts us over the wrong
` proof of 'IsHLevel (Path A x y) (suc. n)'.
`
` Morally, this is not an issue, as the type 'IsHLevel' should be
` a proposition, so we can transport to solve the problem. However,
` we can't prove that 'IsProp (IsContr A)' without some sort of function
` extensionality. If we had HOTT this would not be a problem, but we don't,
` so it is.

` def Gel.hlevel
`   (A : Type) (B : A → Type) (n : Nat)
`   (ahl : IsHLevel A n) (bhl : (a : A) → IsHLevel (B a) n)
`   : IsHLevel⁽ᵈ⁾ A (Gel A B) n (Nat.degen n) ahl :=
`   match n [
`   | zero. ↦ Gel.contr A B ahl (bhl (ahl .centre))
`   | suc. zero. ↦ Gel.prop A B ahl bhl
`   | suc. (suc. n) ↦ a0 b0 a1 b1 ↦
`     IsHLevel.retract⁽ᵈ⁾
`       (Path A a0 a1) (Gel (Path A a0 a1) (p ↦ PathP A B a0 (b0 .ungel) a1 (b1 .ungel) p))
`       (Path A a0 a1) (Path⁽ᵈ⁾ A (Gel A B) a0 b0 a1 b1)
`       (suc. n) (Nat.degen (suc. n))
`       (Retraction.id (Path A a0 a1)) ?
`       (ahl a0 a1)
`       (Gel.hlevel
`         (Path A a0 a1)
`         (PathP A B a0 (b0 .ungel) a1 (b1 .ungel))
`         (suc. n)
`         (ahl a0 a1)
`         (p ↦ bhl a1 (subst A B a0 a1 p (b0 .ungel)) (b1 .ungel)))
`   ]
