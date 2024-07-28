` Prelude

def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A :=
  A' ↦ sig #(transparent) x ↦ (ungel : A' x)

def Path (A : Type) (x : A) : A → Type :=
data [
| refl. : Path A x x
]

def tr (A : Type) (P : A → Type) (x y : A) (p : Path A x y) (x' : P x) : P y :=
match p [
| refl. ↦ x'
]

def J (A : Type) (x : A) (P : (y : A) → Path A x y → Type) (x' : P x refl.)
  (y : A) (p : Path A x y) : P y p :=
match p [
| refl. ↦ x'
]

def cong (A B : Type) (f : A → B) (x y : A) (p : Path A x y) : Path B (f x) (f y) :=
match p [
| refl. ↦ refl.
]

def ⊥ : Type := data []
def ⊤ : Type := sig #(transparent) ()

def Prod (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

notation 5 Prod : A "×" B := Prod A B

def Coprod (A B : Type) : Type := data [
| inl. : A → Coprod A B
| inr. : B → Coprod A B
]

notation 5 Coprod : A "⊔" B := Coprod A B

def Nat : Type :=
data [
| zero. : Nat
| suc. : Nat → Nat
]

def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n :=
match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

def Nat.degen² (n : Nat)
  : Path
      (Nat⁽ᵈᵈ⁾ n (Nat.degen n) (Nat.degen n))
      (sym (Nat.degen⁽ᵈ⁾ n (Nat.degen n)))
      (Nat.degen⁽ᵈ⁾ n (Nat.degen n)) :=
match n [
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

def Nat.lte (k n : Nat) : Type :=
match k [
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
  : Nat.lte⁽ᵈ⁾ k (Nat.degen k) n (Nat.degen n) h :=
match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ match h []
  | suc. n ↦ Nat.lte.degen k n h
  ]
]

def Nat.lte.wk (k n : Nat) (h : k ≤ n) : k ≤ suc. n :=
match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ match h []
  | suc. n ↦ Nat.lte.wk k n h
  ]
]

def Nat.lte.refl (n : Nat) : n ≤ n :=
match n [
| zero. ↦ ()
| suc. n ↦ Nat.lte.refl n
]

def Nat.Π.adjust
  (X : (n : Nat) (n' : Nat⁽ᵈ⁾ n) → Type)
  (f : (n : Nat) → X n (Nat.degen n))
  (n : Nat) (n' : Nat⁽ᵈ⁾ n) : X n n' :=
match n' [
| zero. ↦ f 0
| suc. n' ↦ Nat.Π.adjust (n n' ↦ X (suc. n) (suc. n')) (n ↦ f (suc. n)) n'.0 n'.1
]

def Nat.lte.Π.adjust
  (X : (n : Nat) (n' : Nat⁽ᵈ⁾ n) (k : Nat) (k' : Nat⁽ᵈ⁾ k)
    (h : k ≤ n) → Type)
  (f : (n : Nat) (k : Nat) (h : k ≤ n) → X n (Nat.degen n) k (Nat.degen k) h)
  (n : Nat) (n' : Nat⁽ᵈ⁾ n)
  (k : Nat) (k' : Nat⁽ᵈ⁾ k)
  (h : k ≤ n) (h' : Nat.lte⁽ᵈ⁾ k k' n n' h)
  : X n n' k k' h  :=
match k' [
| zero. ↦ Nat.Π.adjust (n n' ↦ X n n' 0 0 h) (n ↦ f n 0 h) n n'
| suc. k' ↦
  match n' [
  | zero. ↦ match h []
  | suc. n' ↦
    Nat.lte.Π.adjust
      (n n' k k' h ↦ X (suc. n) (suc. n') (suc. k) (suc. k') h)
      (n k h ↦ f (suc. n) (suc. k) h)
      n'.0 n'.1
      k'.0 k'.1
      h h'
  ]
]

` Semi-Simplicial Types

def SST : Type :=
codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def Coslice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (y ↦ A .s y .z x)
| .s ↦ y α ↦ sym (Coslice⁽ᵈ⁾ A (A .s y) x (α .ungel))
]

` Simplex Boundaries and Fillers

def ○ (n : Nat) (A : SST) : Type :=
match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    (pt : A .z
    , ∂a : ○ n A
    , a : ● n A ∂a
    , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ∂a
    )
]

and ● (n : Nat) (A : SST) (○a : ○ n A) : Type :=
match n [
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]

` Snoc Variants

def ○₁ (n k : Nat) (A : SST) : Type :=
match k [
| zero. ↦ ○ n A
| suc. k ↦
  match n [
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
match k [
| zero. ↦ ● n A ○a
| suc. k ↦
  match n [
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
match n [
| zero. ↦ ○a .a
| suc. n ↦ ○.↑.pt n A (○a .∂a)
]

and ○.↑.∂a (n : Nat) (A : SST) (○a : ○ (suc. n) A) : ○ n A :=
match n [
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
match n [
| zero. ↦ ○a .pt
| suc. n ↦ ○.↑.a⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')
]

and ○.↑.∂a' (n : Nat) (A : SST) (○a : ○ (suc. n) A)
  : ○⁽ᵈ⁾ n (Nat.degen n) A (Coslice A (○.↑.pt n A ○a)) (○.↑.∂a n A ○a) :=
match n [
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
match n [
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
match n [
| zero. ↦
  match k [
  | zero. ↦ ()
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k [
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
match n [
| zero. ↦
  match k [
  | zero. ↦ ●a
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k [
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
match k [
| zero. ↦ ○a
| suc. k ↦
  ○.↑₁
    n k h A
    (○.↑ n k (Nat.lte.wk (suc. k) n h) A ○a)
]

and ●.↑ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  : ●₁ n k A (○.↑ n k h A ○a) :=
match k [
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
match n [
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
match k [
| zero. ↦ ○.↓₂ n A ○a
| suc. k ↦
  match n [
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
match k [
| zero. ↦ ●.↓₂ n A ○a ●a
| suc. k ↦
  match n [
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
match k [
| zero. ↦ ○a
| suc. k ↦
  match n [
  | zero. ↦ match h []
  | suc. n ↦ ○.↓ (suc. n) k (Nat.lte.wk k n h) A (○.↓₁ n k h A ○a)
  ]
]

def ●.↓ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○₁ n k A) (●a : ●₁ n k A ○a)
  : ● n A (○.↓ n k h A ○a) :=
match k [
| zero. ↦ ●a
| suc. k ↦
  match n [
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

def Horn.○ (n k : Nat) (A : SST) (○a : ○ n A) : Type :=
match n [
| zero. ↦
  match k [
  | zero. ↦ A .z
  | suc. k ↦
    match k [
    | zero. ↦ A .z
    | suc. k ↦ ⊥
    ]
  ]
| suc. n ↦
  match k [
  | zero. ↦
    sig
      ( pt : A .z
      , Λa : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s pt) ○a
      )
  | suc. k ↦
    sig
      ( Λa : Horn.○ n k A (○a .∂a)
      , a : Horn.● n k A (○a .∂a) (○a .a) Λa
      , Λa' : Horn.○⁽ᵈ⁾
        n (Nat.degen n)
        k (Nat.degen k)
        A (A .s (○a .pt))
        (○a .∂a) (○a .∂a')
        Λa
      )
  ]
]

and Horn.● (n k : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (Λ : Horn.○ n k A ○a) : Type :=
match n [
| zero. ↦
  match k [
  | zero. ↦ A .s ●a .z Λ
  | suc. k ↦
    match k [
    | zero. ↦ A .s Λ .z ●a
    | suc. k ↦ ⊥
    ]
  ]
| suc. n ↦
  match k [
  | zero. ↦ ●⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s (Λ .pt)) ○a (Λ .Λa) ●a
  | suc. k ↦
    Horn.●⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (Λ .Λa) (Λ .Λa')
      (Λ .a)
  ]
]

def Horn (n k : Nat) (A : SST) : Type :=
sig
  ( ∂a : ○ n A
  , Λa : Horn.○ n k A ∂a
  )

def Horn.data (n k : Nat) (A : SST) (Λ : Horn n k A) : Type :=
sig
  ( face : ● n A (Λ .∂a)
  , filler : Horn.● n k A (Λ .∂a) face (Λ .Λa)
  )

def Inner (A : SST) : Type :=
  (n k : Nat) (h : k ≤ n)
  (Λ : Horn (suc. n) (suc. k) A)
  → Horn.data (suc. n) (suc. k) A Λ

def Inner.promote (A : SST) (I : Inner A) (x : A .z) : Inner⁽ᵈ⁾ A (A .s x) I :=
n n' k k' h h' Λ Λ' ↦
  Nat.lte.Π.adjust
    (n n' k k' h ↦
      (Λ : Horn (suc. n) (suc. k) A)
      (Λ' : Horn⁽ᵈ⁾ (suc. n) (suc. n') (suc. k) (suc. k') A (A .s x)  Λ)
      → Horn.data⁽ᵈ⁾ (suc. n) (suc. n') (suc. k) (suc. k') A (A .s x) Λ Λ' (I n k h Λ))
    (n k h Λ Λ' ↦
      let F :=
        I (suc. n) (suc. k) h
          ( (x, Λ .∂a, I n k h Λ .face, Λ' .∂a)
          , (Λ .Λa, I n k h Λ .filler, Λ' .Λa)) in
      (F .face , F .filler))
    n n' k k' h h' Λ Λ'


def Disc (X : Type) : SST :=
[
| .z ↦ X
| .s ↦ _ ↦ Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

def SST.⊥ : SST := Disc ⊥

def SST.⊤ : SST :=
[
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

def SST.Const (A B : SST) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (_ ↦ B .z)
| .s ↦ a b ↦ sym (SST.Const⁽ᵈ⁾ A (A .s a) B (B .s (b .ungel)))
]

def SST.Id (A : SST) : SST⁽ᵈ⁾ A := SST.Const A SST.⊤
def SST.Trivial (A : SST) : SST⁽ᵈ⁾ A := SST.Const A SST.⊥




{`def 𝒰.○ (n : Nat) : Type :=
match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    ( P : SST
    , ∂A : 𝒰.○ n
    , A : 𝒰.● n ∂A
    , ∂A' : 𝒰.○⁽ᵈ⁾ n (Nat.degen n) ∂A
    )
]

def 𝒰.● (n : Nat) (○A : 𝒰.○ n) : Type :=
match n [
| zero. ↦ SST
| suc. n ↦ 𝒰.●⁽ᵈ⁾ n (Nat.degen n)
]`}

` def 𝒰 : SST := ?

def 𝒰 : SST := [
| .z ↦ Type
| .s ↦ X ↦ 𝒰⁽ᵈ⁾
]

def cool : 𝒰 .s Nat .z ? := ?
` match n [
` | zero. ↦ ⊤
` | suc. n ↦
`   sig
`     ( P : (A .s (○a pt))
`     , ∂A : 𝒰.○ n
`     , A : 𝒰.● n ∂A
`     , ∂A' : 𝒰.○⁽ᵈ⁾ n (Nat.degen n) ∂A
`     )
` ]

` def 𝒰.● (A : SST) : SST ⁽ᵈ⁾

` def 𝒰.● (n : Nat) (○A : 𝒰.○ n) : Type :=
` match n [
` | zero. ↦ SST
` | suc. n ↦ 𝒰.●⁽ᵈ⁾ n (Nat.degen n)
` ]















quit

def Connection (A B : SST) : Type :=
codata [
| 𝒞 .z : (x : A .z) → SST⁽ᵈ⁾ B
| 𝒞 .s : (x : A .z) → Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞
]

def Fib (A B : SST) (𝒞 : Connection A B) (b : B .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (a ↦ 𝒞 .z a .z b)
| .s ↦ a f ↦
  sym (Fib⁽ᵈ⁾
      A (A .s a)
      B (𝒞 .z a)
      𝒞 (𝒞 .s a)
      b (f .ungel))
]

def Assemble (A B : SST) (𝒞 : Connection A B) : SST :=
[
| .z ↦ A .z ⊔ B .z
| .s ↦ [
  | inl. a ↦
    Assemble⁽ᵈ⁾
      A (A .s a)
      B (𝒞 .z a)
      𝒞 (𝒞 .s a)
  | inr. b ↦
    Assemble⁽ᵈ⁾
      A (SST.Trivial A)
      B (B .s b)
      𝒞 ?
  ]
]

def Connection₂ (A B : SST) (𝒞AB : Connection A B) (C : SST)
  (𝒞AC : Connection A C) (𝒞BC : Connection B C) : Type :=
codata [
| 𝒞 .z : (x : A .z) → Connection⁽ᵈ⁾ B (𝒞AB .z x) C (𝒞AC .z x) 𝒞BC
| 𝒞 .s : (x : A .z) →
    Connection₂⁽ᵈ⁾
      A (A .s x)
      B (𝒞AB .z x)
      𝒞AB (𝒞AB .s x)
      C (𝒞AC .z x)
      𝒞AC (𝒞AC .s x)
      𝒞BC (𝒞 .z x)
      𝒞
]

def Foo (A : SST) (B : ASST)

{`def Foo (X : Type) (Z : X → Type) (A : X) : Type :=
codata [
| f .z : (b : Z A) → X⁽ᵈ⁾ A
| f .s : (b : Z A) → Foo⁽ᵈ⁾ X ? Z ? A (f .z b) f
]`}

def ASST : Type :=
codata [
| A .z : Type
| A .s : ASST⁽ᵈ⁾ A
]

def Foo (X : ASST) (Y : SST) (a : X .z) : Type :=
codata [
| f .z : (y : Y .z) → X .s .z a
| f .s : (y : Y .z) → Foo⁽ᵈ⁾ X (X .s) Y (Y .s y) a (f .z y) f
]

{`def Bar (X : ASST) (Y : SST) (a : X .z) (f : Foo X Y a) : SST⁽ᵈ⁾ Y :=
[
| .z ↦ Gel (Y .z) (y ↦ X .s .s .zf .z y)
| .s ↦ ?
]`}


{`def Bar (X : ASST) (Y : SST) : ASST⁽ᵈ⁾ X :=
[
| .z ↦ Gel (X .z) (a ↦ Foo X Y a)
| .s ↦ sym (Bar⁽ᵈ⁾ X (X .s) Y ?)
]`}

{`def 𝒰 (X : ASST) (Y : SST) (a : X .z) : SST :=
[
| .z ↦ Foo X Y a
| .s ↦ f ↦ 𝒰⁽ᵈ⁾ X (X .s) Y ?
]`}

{`def SST.𝒰 : ASST :=
[
| .z ↦ SST
| .s ↦ SST.𝒰⁽ᵈ⁾
]`}

`def Foo (A : SST) :

{`def Foo (A : SST) (a : A .z) : Type :=
codata [
| f .z : (b : A .z) → A .s b .z a
| f .s : (b : A .z) → Foo⁽ᵈ⁾ A (A .s b) a (f .z b) f
]

def Bar (A : SST) (a : A .z) : SST :=
[
| .z ↦ Foo A a
| .s ↦ f ↦ Bar⁽ᵈ⁾ A ? a ?
]`}

` Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞

{`def Foo (A : SST) (a : A .z) : SST :=
[
| .z ↦
  codata [
  | .z ↦ (b : A .z) → A .s a .z b
  | .s ↦ (b : A .z) → Foo⁽ᵈ⁾ A (A .s b) a ?
  ]
| .s ↦ ?
]`}


`and Connection (A B : SST) : Type :=

{`def Connection (A : SST) (B : SST⁽ᵈ⁾ A) : Type :=
codata [
| 𝒞 .z : (a : A .z) → SST⁽ᵈᵈ⁾ A B (A .s a)
| 𝒞 .s : (a : A .z) → Connection⁽ᵈ⁾ A (A .s a) B (sym (𝒞 .z a)) 𝒞
]

def 𝒰 (A : SST) (B : SST⁽ᵈ⁾ A) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Connection A B
| .s ↦ a 𝒞 ↦ 𝒰⁽ᵈ⁾ A ? B ?
]`}

{`def Connection (A B : SST) : Type :=
codata [
| 𝒞 .z : (x : A .z) → SST⁽ᵈ⁾ B
| 𝒞 .s : (x : A .z) → Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞
]

def Fib (A B : SST) (𝒞 : Connection A B) (b : B .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (a ↦ 𝒞 .z a .z b)
| .s ↦ a f ↦
  sym (Fib⁽ᵈ⁾
      A (A .s a)
      B (𝒞 .z a)
      𝒞 (𝒞 .s a)
      b (f .ungel))
]

def Assemble (A : SST) (𝒞 : Connection A (Disc ⊤)) : SST⁽ᵈ⁾ A :=
Fib A (Disc ⊤) 𝒞 ()`}

{`def Connection (A : SST) (B : SST⁽ᵈ⁾ A) : SST⁽ᵈ⁾ A  :=
[
| .z ↦ Gel (A .z) (a ↦ SST⁽ᵈᵈ⁾ A B (A .s a))
| .s ↦ a f ↦ sym (Connection⁽ᵈ⁾ A (A .s a) B (f .ungel))
]`}

{`
def Connection (A : SST) : Type :=
codata [
| 𝒞 .z : SST⁽ᵈ⁾ A
| 𝒞 .s : Connection⁽ᵈ⁾ A (𝒞 .z) 𝒞
]

def 𝒰 (A : SST) : SST :=
[
| .z ↦ Connection A
| .s ↦ 𝒰 ↦ 𝒰⁽ᵈ⁾ A
]
`}

{`axiom A : SST
axiom A' : SST⁽ᵈ⁾ A

axiom 𝒞 : Connection A
axiom 𝒞' : Connection⁽ᵈ⁾ A A' 𝒞

echo 𝒞' .s .z`}


{`def Connection (A : SST) (B : SST⁽ᵈ⁾ A) : Type :=
codata [
| 𝒞 .z : (a : A .z) → SST⁽ᵈᵈ⁾ A B (A .s a)
| 𝒞 .s : (a : A .z) → Connection⁽ᵈ⁾ A (A .s a) B (sym (𝒞 .z a)) 𝒞
]

def 𝒰 (A : SST) (B : SST⁽ᵈ⁾ A) : SST :=
[
| .z ↦ A .z × Connection A B
| .s ↦ a𝒞 ↦ 𝒰⁽ᵈ⁾ A ? B ?
]`}



{`def Sec (A : SST) (B : SST⁽ᵈ⁾ A) : Type :=
codata [
| 𝓈 .z : (a : A .z) → B .z a
| 𝓈 .s : (a : A .z) → Sec⁽ᵈ⁾ A (A .s a) B (sym (B .s a (𝓈 .z a))) 𝓈
]

def Connection (A B : SST) : SST⁽ᵈ⁾ A  :=
[
| .z ↦ Gel (A .z) (a ↦ SST⁽ᵈ⁾ B)
| .s ↦ a f ↦ sym (Connection⁽ᵈ⁾ A (A .s a) B (f .ungel))
]

def 𝒰 (A B : SST) : SST :=
[
| .z ↦ Sec A (Connection A B)
| .s ↦ 𝓈 ↦ 𝒰⁽ᵈ⁾ A (Connection A B) B (𝓈 .z ? .ungel)
]`}


`def 𝒰 (A B : SST) : SST⁽ᵈ⁾ A

`  (x : A .z) → Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞


{`
def Assemble (X : Type) (A : SST) (𝒞 : Connection A (Disc X)) (x : X) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (a ↦ 𝒞 .z a .z x)
| .s ↦ a f ↦
    sym (Assemble⁽ᵈ⁾
      X (Gel X (x ↦ 𝒞 .z a .z x))
      A (A .s a)
      𝒞 ? `(𝒞 .s a)
      x (ungel := f .ungel))
]

and Lem (X : Type) (A : SST⁽ᵈ⁾ (Disc X))
  : Path (SST⁽ᵈ⁾ (Disc X)) A (Disc⁽ᵈ⁾ X (Gel X (x ↦ A .z x))) :=
?
`}

{`
and Lem (X : Type) (𝒞 : Connection SST.⊤ (Disc X))
  : Connection⁽ᵈ⁾ SST.⊤ SST.⊤⁽ᵈ⁾ (Disc X) (Disc⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z () .z x))) 𝒞 :=
[
| .z ↦ _ _ ↦ 𝒞 .s () .z () ()
| .s ↦ ?
]`}

{`def Assemble (X : Type) (𝒞 : Connection SST.⊤ (Disc X)) (x : X) : SST :=
[
| .z ↦ 𝒞 .z () .z x
| .s ↦ a ↦ Assemble⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z () .z x)) 𝒞 ? x (ungel := a)
]

and Lem (X : Type) (𝒞 : Connection SST.⊤ (Disc X))
  : Connection⁽ᵈ⁾ SST.⊤ SST.⊤⁽ᵈ⁾ (Disc X) (Disc⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z () .z x))) 𝒞 :=
[
| .z ↦ _ _ ↦ ?
| .s ↦ ?
]`}



{`codata [
| 𝒞 .z : (x : A .z) → SST⁽ᵈ⁾ B
| 𝒞 .s : (x : A .z) → Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞
]`}

{`
def Connection (A B : SST) : Type :=
codata [
| 𝒞 .z : (x : A .z) → SST⁽ᵈ⁾ B
| 𝒞 .s : (x : A .z) → Connection⁽ᵈ⁾ A (A .s x) B (𝒞 .z x) 𝒞
]

def 𝒰 (A B : SST) : SST⁽ᵈ⁾ A :=
[
| .z ↦ ? `Connection A B
| .s ↦ a 𝒞 ↦ ? `𝒰⁽ᵈ⁾ A ? B ?
]
`}


{`def Assemble (X : Type) (𝒞 : Connection SST.⊤ (Disc X)) (x : X) : SST :=
[
| .z ↦ 𝒞 .z () .z x
| .s ↦ a ↦ Assemble⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z () .z x)) 𝒞 (𝒞 .s ()) x (ungel := a)
]`}






{`and Lem (X : Type) (A B : SST) (𝒞 : Connection A B) (b : X → B .z)
  : Connection A (Disc X) :=
[
| .z ↦ a' ↦ Disc⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z a' .z (b x)))
| .s ↦ a' ↦ Lem⁽ᵈ⁾ X (Gel X (x ↦ 𝒞 .z a' .z (b x))) A (A .s a') B ?
]`}

{`
axiom B : Connection SST.⊤ (Disc ⊤)

axiom x : B .z () .z ()
axiom y : B .z () .z ()

echo B .s () .z () () .z () x y
`}


{`def 𝒰 (X : Type) (A : SST) : SST :=
[
| .z ↦ Connection A B
| .s ↦ 𝒞 ↦ 𝒰⁽ᵈ⁾ A ? B ?
]`}

{`def 𝒰 (A B : SST) : SST :=
[
| .z ↦ Connection A B
| .s ↦ 𝒞 ↦ 𝒰⁽ᵈ⁾ A ? B ?
]`}


{`def 𝒰 : SST :=
[
| .z ↦ SST
| .s ↦ A ↦ 𝒰' A
]

and 𝒰' (A : SST) : SST⁽ᵈ⁾ 𝒰 :=
[
| .z ↦ Gel SST (B ↦ Connection A B)
| .s ↦ B 𝒞 ↦ sym (𝒰'⁽ᵈ⁾ A ?)
]`}


























quit


def Inner.copromote (A : SST) (I : Inner A) (x : A .z) : Inner⁽ᵈ⁾ A (Coslice A x) I :=
n n' k k' h h' Λ Λ' ↦
  Nat.lte.Π.adjust
    (n n' k k' h ↦
      (Λ : Horn (suc. n) (suc. k) A)
      (Λ' : Horn⁽ᵈ⁾ (suc. n) (suc. n') (suc. k) (suc. k') A (Coslice A x)  Λ)
      → Horn.data⁽ᵈ⁾ (suc. n) (suc. n') (suc. k) (suc. k') A (Coslice A x) Λ Λ'
        (I n k h Λ))
    (n k h Λ Λ' ↦
      ? {`let F :=
        K (suc. n) (suc. k) h
          ( x
          , Λ
          , K n k h Λ .face
          , K n k h Λ .filler
          , Λ'
          ) in
      (F .face, F .filler)`})
    n n' k k' h h' Λ Λ'






quit

` Degeneracies

def Degen₀ (A : SST) : Type :=
codata
[
| d .z : (x : A .z) → A .s x .z x
| d .s : (x : A .z) → Degen₀⁽ᵈ⁾ A (A .s x) d
]

def Degen (A : SST) : Type :=
codata
[
| d .z : Degen₀ A
| d .s : (x : A .z) → Degen⁽ᵈ⁾ A (Coslice A x) d
]

def Degen.promote (A : SST) (d : Degen A) (x : A .z) : Degen⁽ᵈ⁾ A (A .s x) d :=
[
| .z ↦ d .z .s x
| .s ↦ y α ↦ sym (Degen.promote⁽ᵈ⁾ A (Coslice A y) d (d .s y) x (ungel := α))
]

def Degen.○₁ (n k : Nat) (h : k ≤ n) (A : SST)
  (○a : ○₁ n k A) (●a : ●₁ n k A ○a) (d : Degen A)
  : ○₁ (suc. n) k A :=
match n [
| zero. ↦
  match k [
  | zero. ↦ (●a, (), ●a, ())
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k [
  | zero. ↦
    ( ○a .pt
    , Degen.○₁ n 0 () A (○a .∂a) (○a .a) d
    , Degen.●₁ n 0 () A (○a .∂a) (○a .a) d
    , Degen.○₁⁽ᵈ⁾
        n (Nat.degen n)
        0 0
        () ()
        A (A .s (○a .pt))
        (○a .∂a) (○a .∂a')
        (○a .a) ●a
        d (Degen.promote A d (○a .pt))
    )
  | suc. k ↦
    ( ○a .pt
    , Degen.○₁ n k h A (○a .∂a) (○a .a) d
    , Degen.●₁ n k h A (○a .∂a) (○a .a) d
    , Degen.○₁⁽ᵈ⁾
        n (Nat.degen n)
        k (Nat.degen k)
        h (Nat.lte.degen k n h)
        A (Coslice A (○a .pt))
        (○a .∂a) (○a .∂a')
        (○a .a) ●a
        d (d .s (○a .pt))
    )
  ]
]

and Degen.●₁ (n k : Nat) (h : k ≤ n) (A : SST)
  (○a : ○₁ n k A) (●a : ●₁ n k A ○a) (d : Degen A)
  : ●₁ (suc. n) k A (Degen.○₁ n k h A ○a ●a d) :=
match n [
| zero. ↦
  match k [
  | zero. ↦ d .z .z ●a
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k [
  | zero. ↦
    Degen.●₁⁽ᵈ⁾
      n (Nat.degen n)
      0 0
      () ()
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      d (Degen.promote A d (○a .pt))
  | suc. k ↦
    Degen.●₁⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k n h)
      A (Coslice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      d (d .s (○a .pt))
  ]
]

def Degen.○ (n k : Nat) (h : k ≤ n) (A : SST)
  (○a : ○ n A) (●a : ● n A ○a) (d : Degen A)
  : ○ (suc. n) A :=
○.↓ (suc. n) k (Nat.lte.wk k n h) A
  (Degen.○₁ n k h A
    (○.↑ n k h A ○a)
    (●.↑ n k h A ○a ●a)
    d)

and Degen.● (n k : Nat) (h : k ≤ n) (A : SST)
  (○a : ○ n A) (●a : ● n A ○a) (d : Degen A)
  : ● (suc. n) A (Degen.○ n k h A ○a ●a d) :=
●.↓ (suc. n) k (Nat.lte.wk k n h) A
  (Degen.○₁ n k h A
    (○.↑ n k h A ○a)
    (●.↑ n k h A ○a ●a)
    d)
  (Degen.●₁ n k h A
    (○.↑ n k h A ○a)
    (●.↑ n k h A ○a ●a)
    d)

` Quasi-Categories

def Quasi (A : SST) : Type :=
  sig
    ( inner : Inner A
    , degen : Degen A
    )

def Quasi.promote (A : SST) (Q : Quasi A) (x : A .z) : Quasi⁽ᵈ⁾ A (A .s x) Q :=
( Inner.promote A (Q .inner) x
, Degen.promote A (Q .degen) x
)

` Half-Adjoint Equivalences

` type checking hint function
def Horn.combine (n k : Nat) (A : SST) (x : A .z) (Λ : Horn n k A)
  (Λ' : Horn⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) A (A .s x) Λ)
  (F : Horn.data n k A Λ) : Horn (suc. n) (suc. k) A :=
( (x, Λ .∂a , F .face, Λ' .∂a)
, (Λ .Λa , F .filler, Λ' .Λa)
)

def Hae (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ n A) (●a : ● n A ○a) : Type :=
match n [
| zero. ↦ ⊤
| suc. n ↦
  match n [
  | zero. ↦
    sig
      ( inv : ● 1 A (Hae.Λ₀ n A Q ○a ●a () .∂a)
      , η : Horn.● 1 n A (Hae.Λ₀ n A Q ○a ●a () .∂a) inv (Hae.Λ₀ n A Q ○a ●a () .Λa)
      )
  | suc. n ↦
    sig
      ( ∂h : Hae (suc. n) A Q (○a .∂a) (○a .a)
      , ∂h' :
          Hae⁽ᵈ⁾
            n (Nat.degen n)
            A (A .s (○a .pt))
            Q (Quasi.promote A Q (○a .pt))
            (○a .∂a .∂a) (○a .∂a' .∂a)
            (○a .∂a .a) (○a .∂a' .a)
            (Hae.lower n A Q (○a .∂a) (○a .a) ∂h)
      , inv : ● n A (Hae.Λ₀ n A Q ○a ●a ∂h .∂a)
      , η : Horn.● n n A (Hae.Λ₀ n A Q ○a ●a ∂h .∂a) inv (Hae.Λ₀ n A Q ○a ●a ∂h .Λa)
      )
  ]
]

and Hae.lower (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae (suc. n) A Q ○a ●a) : Hae n A Q (○a .∂a) (○a .a) := ?

and Hae.Λ₀ (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a)) : Horn (suc. n) n A :=
match n [
| zero. ↦
    ( (○a .a, (), ○a .pt, ()),
      (○a .pt, (●a, (), Degen.● 0 0 () A () (○a .pt) (Q .degen), ()))
    )
| suc. n ↦
  Horn.combine
    (suc. n) n A (○a .pt)
    (Hae.Λ₀ n A Q (○a .∂a) (○a .a) (H .∂h))
    (Hae.Λ₀⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (H .∂h) ? {`(Hae.degen n A Q ○a H)`})
    (H .inv, H .η)
]

` type checking hint function
and Hae.combine₁ (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a))
  (F : Horn.data (suc. n) n A (Hae.Λ₀ n A Q ○a ●a H))
  : Hae (suc. n) A Q ○a ●a :=
( H
, F .face
, F .filler
)




quit
def Hae (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ n A) (●a : ● n A ○a) : Type :=
match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    ( ∂h : Hae n A Q (○a .∂a) (○a .a)
    , inv : ● (suc. n) A (Hae.Λ₀ n A Q ○a ●a ∂h .∂a)
    , η : Horn.● (suc. n) n A (Hae.Λ₀ n A Q ○a ●a ∂h .∂a) inv (Hae.Λ₀ n A Q ○a ●a ∂h .Λa)
    )
]

and Hae.lower (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae (suc. n) A Q ○a ●a) : Hae n A Q (○a .∂a) (○a .a) := H .∂h

and Hae.Λ₀ (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a)) : Horn (suc. n) n A :=
match n [
| zero. ↦
    ( (○a .a, (), ○a .pt, ()),
      (○a .pt, (●a, (), Degen.● 0 0 () A () (○a .pt) (Q .degen), ()))
    )
| suc. n ↦
  Horn.combine
    (suc. n) n A (○a .pt)
    (Hae.Λ₀ n A Q (○a .∂a) (○a .a) (H .∂h))
    (Hae.Λ₀⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (H .∂h) (Hae.degen n A Q ○a H))
    (H .inv, H .η)
]

` type checking hint function
and Hae.combine₁ (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a))
  (F : Horn.data (suc. n) n A (Hae.Λ₀ n A Q ○a ●a H))
  : Hae (suc. n) A Q ○a ●a :=
( H
, F .face
, F .filler
)

and Hae.promote (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae (suc. n) A Q (○a .∂a) (○a .a))
  : Hae (suc. (suc. n)) A Q ○a ●a :=
Hae.combine₁ (suc. n) A Q ○a ●a H
  (Q .inner (suc. n) n (Nat.lte.wk n n (Nat.lte.refl n)) (Hae.Λ₀ (suc. n) A Q ○a ●a H))

` type checking hint function
and Hae.combine₂ (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae (suc. (suc. n)) A Q ○a ●a)
  : Hae⁽ᵈ⁾
      (suc. n) (Nat.degen (suc. n))
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (Hae.lower (suc. n) A Q ○a ●a H) :=
( Hae.degen n A Q ○a (H .∂h)
, H .inv
, H .η
)

and Hae.degen (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A)
  (H : Hae (suc. n) A Q (○a .∂a) (○a .a))
  : Hae⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a .∂a) (○a .∂a' .∂a)
      (○a .∂a .a) (○a .∂a' .a)
      (Hae.lower n A Q (○a .∂a) (○a .a) H) :=
match n [
| zero. ↦ ()
| suc. n ↦
  Hae.combine₂ n A Q
    (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
    (○a .∂a' .a)
    (Hae.promote n A Q
      (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
      (○a .∂a' .a)
      (H .∂h))
]




quit








{`
and Hae.Λ₀ (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a)) : Horn (suc. n) n A :=
( Hae.inv n A Q ○a H
, Hae.η n A Q ○a ●a H
)
`}


quit
and Hae.inv (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A)
  (H : Hae n A Q (○a .∂a) (○a .a)) : ○ (suc. n) A :=
match n [
| zero. ↦ (○a .a, (), ○a .pt, ())
| suc. n ↦
  ( ○a .pt
  , Hae.inv n A Q (○a .∂a) (H .∂h)
  , H .inv
  , Hae.inv⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (H .∂h) (Hae.degen n A Q ○a H)
  )
]

and Hae.η (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a))
  : Horn.○ (suc. n) n A (Hae.inv n A Q ○a H) :=
match n [
| zero. ↦
  ( ○a .pt
  , (●a, (), Degen.● 0 0 () A () (○a .pt) (Q .degen), ())
  )
| suc. n ↦
  ( Hae.η n A Q (○a .∂a) (○a .a) (H .∂h)
  , H .η
  , Hae.η⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (H .∂h) (Hae.degen n A Q ○a H)
  )
]

and Hae.Λ₀ (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a)) : Horn (suc. n) n A :=
( Hae.inv n A Q ○a H
, Hae.η n A Q ○a ●a H
)

and Hae.combine₁ (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a))
  (F : Horn.data (suc. n) n A (Hae.Λ₀ n A Q ○a ●a H))
  : Hae (suc. n) A Q ○a ●a :=
( H
, F .face
, F .filler
)

and Hae.promote (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae (suc. n) A Q (○a .∂a) (○a .a))
  : Hae (suc. (suc. n)) A Q ○a ●a :=
Hae.combine₁ (suc. n) A Q ○a ●a H
  (Q .inner (suc. n) n (Nat.lte.wk n n (Nat.lte.refl n)) (Hae.Λ₀ (suc. n) A Q ○a ●a H))

and Hae.degen (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A)
  (H : Hae (suc. n) A Q (○a .∂a) (○a .a))
  : Hae⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a .∂a) (○a .∂a' .∂a)
      (○a .∂a .a) (○a .∂a' .a)
      (Hae.lower n A Q (○a .∂a) (○a .a) H) :=
? {`match n [
| zero. ↦ ()
| suc. n ↦
  let H' :=
    Hae.promote n A Q
      (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
      (○a .∂a' .a)
      (H .∂h) in
    ( Hae.degen n A Q (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (H' .∂h)
    , H' .inv
    , H' .η
    )
]`}


{`
def Hae (n : Nat) (h₀ : n ≤ suc. (suc. n))
  (A : SST) (Q : Quasi A) (○a : ○ n A) (●a : ● n A ○a) : Type :=
match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    ( ∂h : Hae n h₀ A Q (○a .∂a) (○a .a)
    , inv : ● (suc. n) A (Hae.inv n h₀ A Q ○a ∂h)
    , η : Horn.● (suc. n) n h₀ A (Hae.inv n h₀ A Q ○a ∂h) inv (Hae.η n h₀ A Q ○a ●a ∂h)
    )
]

and Hae.inv (n : Nat) (h₀ : n ≤ suc. (suc. n))
  (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A)
  (H : Hae n h₀ A Q (○a .∂a) (○a .a)) : ○ (suc. n) A :=
match n [
| zero. ↦ (○a .a, (), ○a .pt, ())
| suc. n ↦
  ( ○a .pt
  , Hae.inv n h₀ A Q (○a .∂a) (H .∂h)
  , H .inv
  , Hae.inv⁽ᵈ⁾
      n (Nat.degen n)
      h₀ (Nat.lte.degen n (suc. (suc. n)) h₀)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (H .∂h) ?
  )
]

and Hae.η (n : Nat) (h₀ : n ≤ suc. (suc. n))
  (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae n h₀ A Q (○a .∂a) (○a .a))
  : Horn.○ (suc. n) n h₀ A (Hae.inv n h₀ A Q ○a H) :=
match n [
| zero. ↦
  ( ○a .pt
  , (●a, (), Degen.● 0 0 () A () (○a .pt) (Q .degen), ())
  )
| suc. n ↦
  ( Hae.η n h₀ A Q (○a .∂a) (○a .a) (H .∂h)
  , H .η
  , ?
  )
]

and Hae.promote (n : Nat) (h₀ : n ≤ suc. n)
  (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae (suc. n) (Nat.lte.wk n (suc. n) h₀) A Q (○a .∂a) (○a .a))
  : Hae (suc. (suc. n)) (Nat.lte.wk n (suc. n) h₀) A Q ○a ●a :=
? {`let F :=
  Q .inner (suc. n) n h₀
    ( Hae.inv (suc. n) (Nat.lte.wk n (suc. n) h₀) A Q ○a H
    , Hae.η (suc. n) (Nat.lte.wk n (suc. n) h₀) A Q ○a ●a H
    ) in
  ( H
  , F .face
  , F .filler
  )`}

quit

and Hae.lower (n : Nat) (h₀ : n ≤ suc. (suc. n))
  (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae (suc. n) h₀ A Q ○a ●a) : Hae n h₀ A Q (○a .∂a) (○a .a) := H .∂h

and Hae.degen (n : Nat) (h₀ : n ≤ suc. (suc. n))
  (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae (suc. n) h₀ A Q (○a .∂a) (○a .a))
  : Hae⁽ᵈ⁾
      n (Nat.degen n) h₀
      (Nat.lte.degen n (suc. (suc. n)) h₀)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a .∂a) (○a .∂a' .∂a)
      (○a .∂a .a) (○a .∂a' .a)
      (Hae.lower n h₀ A Q (○a .∂a) (○a .a) H) :=
match n [
| zero. ↦ ()
| suc. n ↦
  let H' :=
    Hae.promote n h₀ (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a) in
    (  Hae.degen h₀ A Q ? ?
    , ?
    , ?
    )
]


{`
and Hae.lower (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae (suc. n) A Q ○a ●a) : Hae n A Q (○a .∂a) (○a .a) := H .∂h

and Hae.degen (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (H : Hae (suc. n) A Q ○a ●a)
  : Hae⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (Hae.lower n A Q ○a ●a H) :=
match n [
| zero. ↦ ()
| suc. n ↦
  ( Hae.degen n A Q (○a .∂a) (○a .a) (H .∂h)
  , ? `H .inv
  )
]`}

{`and Hae.degen (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A)
  (H : Hae (suc. n) A Q (○a .∂a) (○a .a))
  : Hae⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .pt))
      Q (Quasi.promote A Q (○a .pt))
      (○a .∂a .∂a) (○a .∂a' .∂a)
      (○a .∂a .a) (○a .∂a' .a)
      (Hae.lower n A Q (○a .∂a) (○a .a) H) :=
match n [
| zero. ↦ ()
| suc. n ↦
  ( ? `Hae.degen n A Q (○a .∂a) (H .∂h)
  , ? `H .inv
  )
]`}


{`
def Hae (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a) : Type :=
match n [
| zero. ↦
  sig
    ( inv : A .s (○a .a) .z (○a .pt)
    , η : A .s (○a .pt) .s (○a .a) ●a
            .z (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv
    , ε : A .s (○a .a) .s (○a .pt) inv
            .z (○a .a) (Degen.● 0 0 () A () (○a .a) (Q .degen)) ●a
    , coh :
      A .s (○a .pt) .s (○a .a) ●a
        .s (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv η .z (○a .a) ●a
          (Degen.● 0 0 () A () (○a .a) (Q .degen))
          (Degen.● 1 0 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen))
          ●a (Degen.● 1 1 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen)) ε
    )
| suc. n ↦
  sig
    ( ∂h : Hae n A Q (○a .∂a) (○a .a)
    , inv : ● (suc. (suc. n)) A (Hae.flip n A Q ○a ∂h)
    )
]

and Hae.flip (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A)
  (H : Hae n A Q (○a .∂a) (○a .a)) : ○ (suc. (suc. n)) A :=
match n [
| zero. ↦
  ( ○a .pt
  , (○a .∂a .a, (), ○a .∂a .pt, ())
  , H .inv
  , (○a .∂a' .a, (), ○a .∂a' .pt, ()))
| suc. n ↦ ?
]
`}
`}




quit
def Hae (A : SST) (Q : Quasi A) (x y : A .z) (α : A .s x .z y) : Type :=
sig
  ( inv : A .s y .z x
  , η : A .s x .s y α .z x (Degen.● 0 0 () A () x (Q .degen)) inv
  , ε : A .s y .s x inv .z y (Degen.● 0 0 () A () y (Q .degen)) α
  , coh :
    A .s x .s y α
      .s x (Degen.● 0 0 () A () x (Q .degen)) inv η .z y α
        (Degen.● 0 0 () A () y (Q .degen)) (Degen.● 1 0 () A (x, (), y, ()) α (Q .degen))
        α (Degen.● 1 1 () A (x, (), y, ()) α (Q .degen)) ε
  )

def Hae.promote (A : SST) (Q : Quasi A) (y z : A .z) (γ : A .s y .z z)
  (h : Hae A Q y z γ) (x : A .z)
  (α : A .s x .z y) (β : A .s x .z z) (𝔣 : A .s x .s y α .z z β γ) :
  Hae⁽ᵈ⁾ A (A .s x) Q (Quasi.promote A Q x) y α z β γ 𝔣 h :=
? {`let Λ₀ : Horn 2 1 () A :=
  ( x
  , (y, (z, (), y, ()), (γ, (), Degen.● 0 0 () A () y (Q .degen), ()))
  , h .inv
  , h .η
  , (α, (β, (), α, ()), (𝔣, (), Degen.● 1 0 () A (x, (), y, ()) α (Q .degen), ()))) in
let inv := Q .inner 1 0 () Λ₀ .face in
let η := Q .inner 1 0 () Λ₀ .filler in
let Λ₁ : Horn 3 1 () A :=
  ( x
  , ( y
    , ( z
      , (y, (), z, ())
      , γ
      , (h .inv, (), Degen.● 0 0 () A () z (Q .degen), ())
      )
    , ( γ
      , (Degen.● 0 0 () A () y (Q .degen), (), γ, ())
      , Degen.● 1 1 () A (y, (), z, ()) γ (Q .degen)
      , (h .η, (), Degen.● 1 0 () A (y, (), z, ()) γ (Q .degen), ())
      )
    )
  , h .ε
  , h .coh
  , ( α
    , ( β
      , (α, (), β, ())
      , 𝔣
      , ( inv
        , ()
        , Degen.● 1 0 () A (x, (), z, ()) β (Q .degen)
        , ()
        )
      )
    , ( 𝔣
      , (Degen.● 1 0 () A (x, (), y, ()) α (Q .degen), (), 𝔣, ())
      , Degen.● 2 1 () A
          (x, (y, (), z, ()), γ, (α, (), β, ()))
          𝔣 (Q .degen)
      , ( η
        , ()
        , Degen.● 2 0 () A
            (x, (y, (), z, ()), γ, (α, (), β, ()))
            𝔣 (Q .degen)
        , ()
        )
      )
    )
  ) in
let ε := Q .inner 2 0 () Λ₁ .face in
let coh := Q .inner 2 0 () Λ₁ .filler in
  ( inv, η, ε, coh )`}










{`
def Hae (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a) : Type :=
match n [
| zero. ↦
  sig
    ( inv : A .s (○a .a) .z (○a .pt)
    , η : A .s (○a .pt) .s (○a .a) ●a
            .z (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv
    , ε : A .s (○a .a) .s (○a .pt) inv
            .z (○a .a) (Degen.● 0 0 () A () (○a .a) (Q .degen)) ●a
    , coh :
      A .s (○a .pt) .s (○a .a) ●a
        .s (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv η .z (○a .a) ●a
          (Degen.● 0 0 () A () (○a .a) (Q .degen))
          (Degen.● 1 0 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen))
          ●a (Degen.● 1 1 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen)) ε
    )
| suc. n ↦
  sig
    ( ∂h : Hae n A Q (○a .∂a) (○a .a)
    , inv : ● (suc. (suc. n)) A (Hae.flip n A Q ○a ∂h)
    )
]

and Hae.flip (n : Nat) (A : SST) (Q : Quasi A) (○a : ○ (suc. (suc. n)) A)
  (H : Hae n A Q (○a .∂a) (○a .a)) : ○ (suc. (suc. n)) A :=
match n [
| zero. ↦ (○a .pt, (○a .∂a .pt, ?, ?, ?), ?, (?, ?, ?, ?))
| suc. n ↦ ?
]
`}


{`
def Hae (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a) : Type :=
match n [
| zero. ↦
  sig
    ( inv : A .s (○a .a) .z (○a .pt)
    , η : A .s (○a .pt) .s (○a .a) ●a
            .z (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv
    , ε : A .s (○a .a) .s (○a .pt) inv
            .z (○a .a) (Degen.● 0 0 () A () (○a .a) (Q .degen)) ●a
    , coh :
      A .s (○a .pt) .s (○a .a) ●a
        .s (○a .pt) (Degen.● 0 0 () A () (○a .pt) (Q .degen)) inv η .z (○a .a) ●a
          (Degen.● 0 0 () A () (○a .a) (Q .degen))
          (Degen.● 1 0 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen))
          ●a (Degen.● 1 1 () A (○a .pt, (), ○a .a, ()) ●a (Q .degen)) ε
    )
| suc. n ↦
  sig
    ( ∂h : Hae n A Q (○a .∂a) (○a .a)
    , h :
        Hae⁽ᵈ⁾
          n (Nat.degen n)
          A (A .s (○a .pt))
          Q (Quasi.promote A Q (○a .pt))
          (○a .∂a) (○a .∂a')
          (○a .a) ●a
          ∂h
    )
]

def Hae.promote (n : Nat) (A : SST) (Q : Quasi A)
  (○a : ○ (suc. (suc. n)) A) (●a : ● (suc. (suc. n)) A ○a)
  (H : Hae n A Q (○a .∂a) (○a .a))
  : Hae (suc. n) A Q ○a ●a :=
match n [
| zero. ↦ ?
| suc. n ↦ ?
]
`}
