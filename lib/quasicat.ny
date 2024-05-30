` Prelude

def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

def Gel²
  (Ap : Type) (Ax Ay : Type⁽ᵈ⁾ Ap)
  (Aα : (p : Ap) → Ax p → Ay p → Type)
  : Type⁽ᵈᵈ⁾ Ap Ax Ay := sig p x y ↦ (ungel : Aα p x y)

def Path (A : Type) (x : A) : A → Type :=
data
[
| refl. : Path A x x
]

def tr (A : Type) (P : A → Type) (x y : A) (p : Path A x y) (x' : P x) : P y :=
match p
[
| refl. ↦ x'
]

def J (A : Type) (x : A) (P : (y : A) → Path A x y → Type) (x' : P x refl.)
  (y : A) (p : Path A x y) : P y p :=
match p
[
| refl. ↦ x'
]

def cong (A B : Type) (f : A → B) (x y : A) (p : Path A x y) : Path B (f x) (f y) :=
match p
[
| refl. ↦ refl.
]

def ⊥ : Type := data []
def ⊤ : Type := sig ()

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)


def Nat : Type := data [
| zero. : Nat
| suc. : Nat → Nat
]

def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

def Nat.degen² (n : Nat)
  : Path
      (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
      (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
      (Nat.degen⁽ᵈ⁾ n (Nat.degen n)) :=
match n
[
| zero. ↦ refl.
| suc. n ↦
  cong
    (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
    (Nat⁽ᵈᵈ⁾ (suc. n) (Nat.degen (suc. n)) (Nat.degen (suc. n)))
    (n ↦ suc. n)
    (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
    (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
    (Nat.degen² n)
]

def Nat.lte (k n : Nat) : Type := match k [
| zero. ↦ ⊤
| suc. k ↦ match n [
  | zero. ↦ ⊥
  | suc. n ↦ Nat.lte k n
  ]
]

def Nat.lt (k n : Nat) : Type := Nat.lte (suc. k) n

notation 5 Nat.lte : k "≤" n := Nat.lte k n
notation 5 Nat.lt : k "<" n := Nat.lt k n

def Nat.lte.degen
  (k n : Nat)
  (h : k ≤ n)
  : Nat.lte⁽ᵈ⁾ k (Nat.degen k) n (Nat.degen n) h := match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ match h []
  | suc. n ↦ Nat.lte.degen k n h
  ]
]

def Nat.lte.wk (k n : Nat) (h : k ≤ n) : k ≤ suc. n := match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ match h []
  | suc. n ↦ Nat.lte.wk k n h
  ]
]

` Semi-Simplicial Types

def SST : Type := codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def Coslice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (y ↦ A .s y .z x)
| .s ↦ y α ↦ sym (Coslice⁽ᵈ⁾ A (A .s y) x (α .ungel))
]

` Simplex Boundaries and Fillers

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

and ● (n : Nat) (A : SST) (○a : ○ n A) : Type := match n [
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]

` Snoc Variants

def ○₁ (n k : Nat) (A : SST) : Type :=
match k
[
| zero. ↦ ○ n A
| suc. k ↦
  match n
  [
  | zero. ↦ ⊤
  | suc. n ↦
    sig
      ( pt : A .z
      , ∂a : ○₁ n k A
      , a : ●₁ n k A ∂a
      , ∂a' :
          ○₁⁽ᵈ⁾
            n (Nat.degen n)
            k (Nat.degen k)
            A (Coslice A pt)
            ∂a
      )
  ]
]

and ●₁ (n k : Nat) (A : SST) (○a : ○₁ n k A) : Type :=
match k
[
| zero. ↦ ● n A ○a
| suc. k ↦
  match n
  [
  | zero. ↦ A .z
  | suc. n ↦
    ●₁⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      A (Coslice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a)
  ]
]

` Up Conveersion Functions

def ○.↑₂ (n : Nat) (A : SST) (○a : ○ (suc. n) A)
  : ○₁ (suc. n) 1 A :=
( ○.↑.pt n A ○a
, ○.↑.∂a n A ○a
, ○.↑.a n A ○a
, ○.↑.∂a' n A ○a
)

and ○.↑.pt (n : Nat) (A : SST) (○a : ○ (suc. n) A) : A .z :=
match n
[
| zero. ↦ ○a .a
| suc. n ↦ ○.↑.pt n A (○a .∂a)
]

and ○.↑.∂a (n : Nat) (A : SST) (○a : ○ (suc. n) A) : ○ n A :=
match n
[
| zero. ↦ ()
| suc. n ↦
  ( ○a .pt
  , ○.↑.∂a n A (○a .∂a)
  , ○.↑.a n A (○a .∂a)
  , ○.↑.∂a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')
  )
]

and ○.↑.a (n : Nat) (A : SST) (○a : ○ (suc. n) A)
  : ● n A (○.↑.∂a n A ○a) :=
match n
[
| zero. ↦ ○a .pt
| suc. n ↦ ○.↑.a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')
]

and ○.↑.∂a' (n : Nat) (A : SST) (○a : ○ (suc. n) A)
  : ○⁽ᵈ⁾ n (Nat.degen n) A (Coslice A (○.↑.pt n A ○a)) (○.↑.∂a n A ○a) :=
match n
[
| zero. ↦ ()
| suc. n ↦
  ( (ungel := ○.↑.pt⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))
  , ○.↑.∂a' n A (○a .∂a)
  , ●.↑₂ n A (○a .∂a) (○a .a)
  , tr
      (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
      (n'' ↦
        ○⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) n''
          A (Coslice A (○.↑.pt n A (○a .∂a))) (A .s (○a .pt))
          (sym (Coslice⁽ᵈ⁾ A (A .s (○a .pt)) (○.↑.pt n A (○a .∂a))
            (○.↑.pt⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))))
          (○.↑.∂a n A (○a .∂a)) (○.↑.∂a' n A (○a .∂a))
          (○.↑.∂a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')))
      (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
      (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      (Nat.degen² n)
      (sym (○.↑.∂a'⁽ᵈ⁾
        n (Nat.degen n)
        A (A .s (○a .pt))
        (○a .∂a) (○a .∂a')))
  )
]

and ●.↑₂ (n : Nat) (A : SST) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  : ●₁ (suc. n) 1 A (○.↑₂ n A ○a) :=
match n
[
| zero. ↦ (ungel := ●a)
| suc. n ↦
  J
    (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
    (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
    (n'' p ↦
      ●⁽ᵈᵈ⁾
      n (Nat.degen n) (Nat.degen n) n''
      A (Coslice A (○.↑.pt n A (○a .∂a))) (A .s (○a .pt))
      (sym (Coslice⁽ᵈ⁾ A (A .s (○a .pt)) (○.↑.pt n A (○a .∂a))
        (○.↑.pt⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))))
      (○.↑.∂a n A (○a .∂a)) (○.↑.∂a' n A (○a .∂a))
      (○.↑.∂a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))
      (tr
        (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
        (n''' ↦
          ○⁽ᵈᵈ⁾
            n (Nat.degen n) (Nat.degen n) n'''
            A (Coslice A (○.↑.pt n A (○a .∂a))) (A .s (○a .pt))
            (sym (Coslice⁽ᵈ⁾ A (A .s (○a .pt)) (○.↑.pt n A (○a .∂a))
              (○.↑.pt⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))))
            (○.↑.∂a n A (○a .∂a)) (○.↑.∂a' n A (○a .∂a))
            (○.↑.∂a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')))
        (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
        n''
        p
        (sym (○.↑.∂a'⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))))
      (○.↑.a n A (○a .∂a)) (●.↑₂ n A (○a .∂a) (○a .a))
      (○.↑.a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')))
    (sym (●.↑₂⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a) ●a))
    (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
    (Nat.degen² n)
]

def ○.↑₁ (n k : Nat) (h : suc. k ≤ n) (A : SST) (○a : ○₁ n k A)
  : ○₁ n (suc. k) A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ ()
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k
  [
  | zero. ↦
    ( ○.↑.pt n A ○a
    , ○.↑.∂a n A ○a
    , ○.↑.a n A ○a
    , ○.↑.∂a' n A ○a
    )
  | suc. k ↦
    ( ○a .pt
    , ○.↑₁ n k h A (○a .∂a)
    , ●.↑₁ n k h A (○a .∂a) (○a .a)
    , ○.↑₁⁽ᵈ⁾
        n (Nat.degen n)
        k (Nat.degen k)
        h (Nat.lte.degen (suc. k) n h)
        A (Coslice A (○a .pt))
        (○a .∂a) (○a .∂a')
    )
  ]
]

and ●.↑₁ (n k : Nat) (h : suc. k ≤ n) (A : SST) (○a : ○₁ n k A) (●a : ●₁ n k A ○a)
  : ●₁ n (suc. k) A (○.↑₁ n k h A ○a) :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ ●a
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ ●.↑₂ n A ○a ●a
  | suc. k ↦
    ●.↑₁⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen (suc. k) n h)
      A (Coslice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
  ]
]

def ○.↑ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A)
  : ○₁ n k A :=
match k
[
| zero. ↦ ○a
| suc. k ↦
  ○.↑₁
    n k h A
    (○.↑ n k (Nat.lte.wk (suc. k) n h) A ○a)
]

and ●.↑ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  : ●₁ n k A (○.↑ n k h A ○a) :=
match k
[
| zero. ↦ ●a
| suc. k ↦
  ●.↑₁
    n k h A
    (○.↑ n k (Nat.lte.wk (suc. k) n h) A ○a)
    (●.↑ n k (Nat.lte.wk (suc. k) n h) A ○a ●a)
]

` Down Conversion Functions

def ○.↓₂ (n : Nat) (A : SST) (○a : ○₁ (suc. n) 1 A) : ○ (suc. n) A :=
match n [
| zero. ↦ (○a .a, (), ○a .pt, ())
| suc. n ↦
  ( ○a .∂a .pt
  , ○.↓₂ n A (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
  , ●.↓₂ n A (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a)
  , ○.↓₂⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .∂a .pt))
      ( ○a .pt
      , ○a .∂a .∂a
      , ○a .∂a .a
      , ○a .∂a' .∂a
      )
      ( ○a .∂a' .pt .ungel
      , ○a .∂a .∂a'
      , ○a .a
      , tr
          (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
          (n₂ ↦
            ○⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n) n₂
            A (A .s (○a .∂a .pt)) (Coslice A (○a .pt))
            (Coslice⁽ᵈ⁾ A (A .s (○a .∂a .pt)) (○a .pt) (○a .∂a' .pt .ungel))
            (○a .∂a .∂a) (○a .∂a .∂a') (○a .∂a' .∂a))
          (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
          (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
          (Nat.degen² n)
          (sym (○a .∂a' .∂a'))
      )
  )
]

and ●.↓₂ (n : Nat) (A : SST) (○a : ○₁ (suc. n) 1 A)
  (●a : ●₁ (suc. n) 1 A ○a) : ● (suc. n) A (○.↓₂ n A ○a) :=
match n
[
| zero. ↦ ●a .ungel
| suc. n ↦
  ●.↓₂⁽ᵈ⁾
    n (Nat.degen n)
    A (A .s (○a .∂a .pt))
    ( ○a .pt
    , ○a .∂a .∂a
    , ○a .∂a .a
    , ○a .∂a' .∂a
    )
    ( ○a .∂a' .pt .ungel
    , ○a .∂a .∂a'
    , ○a .a
    , tr
        (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
        (n₂ ↦
          ○⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n) n₂
          A (A .s (○a .∂a .pt)) (Coslice A (○a .pt))
          (Coslice⁽ᵈ⁾ A (A .s (○a .∂a .pt)) (○a .pt) (○a .∂a' .pt .ungel))
          (○a .∂a .∂a) (○a .∂a .∂a') (○a .∂a' .∂a))
        (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
        (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
        (Nat.degen² n)
        (sym (○a .∂a' .∂a'))
    )
    (○a .∂a' .a)
    (J
      (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
      (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
      (n₂ p ↦
        ●⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) n₂
          A (A .s (○a .∂a .pt)) (Coslice A (○a .pt))
          (Coslice⁽ᵈ⁾ A (A .s (○a .∂a .pt)) (○a .pt) (○a .∂a' .pt .ungel))
          (○a .∂a .∂a) (○a .∂a .∂a') (○a .∂a' .∂a)
          (tr
            (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
            (n₃ ↦
              ○⁽ᵈᵈ⁾
                n (Nat.degen n) (Nat.degen n) n₃
                A (A .s (○a .∂a .pt)) (Coslice A (○a .pt))
                (Coslice⁽ᵈ⁾ A (A .s (○a .∂a .pt)) (○a .pt)
                  (○a .∂a' .pt .ungel))
                (○a .∂a .∂a) (○a .∂a .∂a') (○a .∂a' .∂a))
            (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
            n₂ p
            (sym (○a .∂a' .∂a')))
            (○a .∂a .a) (○a .a) (○a .∂a' .a))
      (sym ●a)
      (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      (Nat.degen² n))
]

def ○.↓₁ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○₁ (suc. n) (suc. k) A)
  : ○₁ (suc. n) k A :=
match k
[
| zero. ↦ ○.↓₂ n A ○a
| suc. k ↦
  match n
  [
  | zero. ↦ match h []
  | suc. n ↦
    ( ○a .pt
    , ○.↓₁ n k h A (○a .∂a)
    , ●.↓₁ n k h A (○a .∂a) (○a .a)
    , ○.↓₁⁽ᵈ⁾
        n (Nat.degen n)
        k (Nat.degen k)
        h (Nat.lte.degen k n h)
        A (Coslice A (○a .pt))
        (○a .∂a) (○a .∂a')
    )
  ]
]

and ●.↓₁ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○₁ (suc. n) (suc. k) A)
  (●a : ●₁ (suc. n) (suc. k) A ○a) : ●₁ (suc. n) k A (○.↓₁ n k h A ○a) :=
match k
[
| zero. ↦ ●.↓₂ n A ○a ●a
| suc. k ↦
  match n
  [
  | zero. ↦ match h []
  | suc. n ↦
    ●.↓₁⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k n h)
      A (Coslice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
  ]
]

def ○.↓ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○₁ n k A) : ○ n A :=
match k
[
| zero. ↦ ○a
| suc. k ↦
  match n
  [
  | zero. ↦ match h []
  | suc. n ↦ ○.↓ (suc. n) k (Nat.lte.wk k n h) A (○.↓₁ n k h A ○a)
  ]
]

def ●.↓ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○₁ n k A) (●a : ●₁ n k A ○a)
  : ● n A (○.↓ n k h A ○a) :=
match k
[
| zero. ↦ ●a
| suc. k ↦
  match n
  [
  | zero. ↦ match h []
  | suc. n ↦
    ●.↓
      (suc. n) k (Nat.lte.wk k n h) A
      (○.↓₁ n k h A ○a) (●.↓₁ n k h A ○a ●a)
  ]
]

{`
------------------------------
The Theory of Quasi-Categories
------------------------------
`}

` Horns

def Horn (n k : Nat) (h : k ≤ suc. n) (A : SST) : Type := match n [
| zero. ↦ match k [
  | zero. ↦ A .z ` (1, 0) horn
  | suc. k ↦ match k [
    | zero. ↦ A .z ` (1, 1) horn
    | suc. _ ↦ ⊥ ` There are no (1, k+2) horns
    ]
  ]
| suc. n ↦ match k [
  | zero. ↦
      `(n+2, 0) horn
      sig
        (pt : A .z
        , ∂a : ○ (suc. n) A
        , ∂a' : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s pt) ∂a
        )
  | suc. k ↦
    `(n+2, k+1) horn
    sig
      (pt : A .z
      , Λa : Horn n k h A
      , △a : Horn.face n k h A Λa
      , ▲a : Horn.filler n k h A Λa △a
      , Λa' :
        Horn⁽ᵈ⁾
          n (Nat.degen n)
          k (Nat.degen k)
          h (Nat.lte.degen k (suc. n) h)
          A (A .s pt)
          Λa
      )
  ]
]

and Horn.face (n k : Nat) (h : k ≤ suc. n) (A : SST) (Λ : Horn n k h A) : Type :=
match n [
| zero. ↦
  match k [
  | zero. ↦ A .z
  | suc. k ↦
    match k
    [
    | zero. ↦ A .z
    | suc. k ↦ match h []
    ]
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ ● (suc. n) A (Λ .∂a)
  | suc. k ↦
    Horn.face⁽ᵈ⁾
       n (Nat.degen n)
       k (Nat.degen k)
       h (Nat.lte.degen k (suc. n) h)
       A (A .s (Λ .pt))
       (Λ .Λa) (Λ .Λa')
       (Λ .△a)
  ]
]

and Horn.filler (n k : Nat) (h : k ≤ suc. n) (A : SST) (Λ : Horn n k h A)
  (f : Horn.face n k h A Λ) : Type :=
match n [
| zero. ↦ match k [
  | zero. ↦ A .s Λ .z f
  | suc. k ↦ match k [
    | zero. ↦ A .s f .z Λ
    | suc. k ↦ match h []
    ]
  ]
| suc. n ↦ match k [
  | zero. ↦ ● (suc. (suc. n)) A (Λ .pt, Λ .∂a, f, Λ .∂a')
  | suc. k ↦
    Horn.filler⁽ᵈ⁾
       n (Nat.degen n)
       k (Nat.degen k)
       h (Nat.lte.degen k (suc. n) h)
       A (A .s (Λ .pt))
       (Λ .Λa) (Λ .Λa')
       (Λ .△a) f
       (Λ .▲a)
  ]
]


{` Kan Complexes `}

def Kan (A : SST) : Type :=
  (n k : Nat) (h : k ≤ suc. n)(Λ : Horn n k h A)
  → Σ (Horn.face n k h A Λ) (face ↦ Horn.filler n k h A Λ face)


{` If Nat was discrete, these would not need to exist. alas. `}
def Nat.Π.adjust
  (X : (n : Nat) (n' : Nat⁽ᵈ⁾ n) → Type)
  (f : (n : Nat) → X n (Nat.degen n))
  (n : Nat) (n' : Nat⁽ᵈ⁾ n) : X n n' :=
match n' [
| zero. ↦ f 0
| suc. n' ↦ Nat.Π.adjust (n n' ↦ X (suc. n) (suc. n')) (n ↦ f (suc. n)) n'.0 n'.1
]

def Nat.lte.Π.adjust
  (X :
    (n : Nat) (n' : Nat⁽ᵈ⁾ n)
    (k : Nat) (k' : Nat⁽ᵈ⁾ k)
    (h : k ≤ suc. n) (h' : Nat.lte⁽ᵈ⁾ k k' (suc. n) (suc. n') h)
    → Type)
  (f : (n : Nat) (k : Nat) (h : k ≤ suc. n)
    → X n (Nat.degen n) k (Nat.degen k) h (Nat.lte.degen k (suc. n) h))
  (n : Nat) (n' : Nat⁽ᵈ⁾ n)
  (k : Nat) (k' : Nat⁽ᵈ⁾ k)
  (h : k ≤ suc. n) (h' : Nat.lte⁽ᵈ⁾ k k' (suc. n) (suc. n') h)
  : X n n' k k' h h' :=
match k' [
| zero. ↦
  match n' [
  | zero. ↦ f 0 0 ()
  | suc. n' ↦
    Nat.Π.adjust
      (n n' ↦ X (suc. n) (suc. n') 0 0 h h')
      (n ↦ f (suc. n) 0 h)
      n'.0 n'.1
  ]
| suc. k' ↦
  ` Life is suffering
  match k' [
  | zero. ↦
    match n' [
    | zero. ↦ f 0 1 h
    | suc. n' ↦
      Nat.Π.adjust
        (n n' ↦ X (suc. n) (suc. n') 1 1 h h')
        (n ↦ f (suc. n) 1 h)
        n'.0 n'.1
    ]
  | suc. k' ↦
    match n' [
    | zero. ↦ match h []
    | suc. n' ↦
      Nat.lte.Π.adjust
        (n n' k k' h h' ↦
          X (suc. n) (suc. n')
            (suc. k) (suc. k')
            h h')
        (n k h ↦ f (suc. n) (suc. k) h)
        n'.0 n'.1
        (suc. k'.0) (suc. k'.1)
        h h'

    ]
  ]
]


` This function should be very easy, but again we are thwarted by non-discrete nat.
def Kan.promote
  (A : SST) (K : Kan A)
  (x : A .z)
  : Kan⁽ᵈ⁾ A (A .s x) K :=
  n n' k k' h h' Λ Λ' ↦
    Nat.lte.Π.adjust
      (n n' k k' h h' ↦
        (Λ : Horn n k h A)
        (Λ' : Horn⁽ᵈ⁾ n n' k k' h h' A (A .s x) Λ)
        → Σ⁽ᵈ⁾ (Horn.face n k h A Λ)
           (Horn.face⁽ᵈ⁾ n n' k k' h h' A (A .s x) Λ Λ')
           (face ↦ Horn.filler n k h A Λ face)
           (face ⤇ Horn.filler⁽ᵈ⁾ n n' k k' h h' A (A .s x) Λ Λ' face.0 face.1)
           (K n k h Λ))
      (n k h Λ Λ' ↦
        ( K (suc. n) (suc. k) h
          ( x
          , Λ
          , K n k h Λ .fst
          , K n k h Λ .snd
          , Λ'
          ) .fst
        , K (suc. n) (suc. k) h
          ( x
          , Λ
          , K n k h Λ .fst
          , K n k h Λ .snd
          , Λ'
          ) .snd))
      n n' k k' h h' Λ Λ'
