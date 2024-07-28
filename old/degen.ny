{` Prelude `}

def ⊥ : Type := data []
def ⊤ : Type := sig ()

def absurd (A : Type) : ⊥ → A := []

def Nat : Type := data [
| zero. : Nat
| suc. : Nat → Nat
]

def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
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
  | zero. ↦ absurd (⊥⁽ᵈ⁾ h) h
  | suc. n ↦ Nat.lte.degen k n h
  ]
]

def Nat.lte.wk (k n : Nat) (h : k ≤ n) : k ≤ suc. n := match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ absurd (k ≤ 0) h
  | suc. n ↦ Nat.lte.wk k n h
  ]
]

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

def SST : Type := codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

{` degeneracy structures `}

` simplex boundaries and fillers

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

def ●.init (n : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a) : A .z :=
match n
[
| zero. ↦ ●a
| suc. n ↦ ○a .pt
]

` degeneracies

def Degen (n : Nat) (A : SST) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    sig
      ( ∂σ : Degen n A
      , ℓ : Degen.level n A ∂σ
      )
]

and Degen.level (n : Nat) (A : SST) (d : Degen n A) : Type :=
match n
[
| zero. ↦ (x : A .z) → A .s x .z x
| suc. n ↦
    sig
      ( ℓ' : (x : A .z) →
               Degen.level⁽ᵈ⁾
                 n (Nat.degen n)
                 A (A .s x)
                 (d .∂σ) (Degen.promote n A (d .∂σ) (d .ℓ) x)
                 (d .ℓ)
      , σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A (d .∂σ) ○a ●a)
      )
]

and Degen.promote (n : Nat) (A : SST) (d : Degen n A) (ℓ : Degen.level n A d) (x : A .z)
  : Degen⁽ᵈ⁾ n (Nat.degen n) A (A .s x) d :=
match n
[
| zero. ↦ ()
| suc. n ↦
    ( Degen.promote n A (d .∂σ) (d .ℓ) x
    , ℓ .ℓ' x)
]

and Degen.○ (n : Nat) (A : SST) (d : Degen n A) (○a : ○ n A) (●a : ● n A ○a) : ○ (suc. n) A :=
match n
[
| zero. ↦ (●a, (), ●a, ())
| suc. n ↦
    ( ○a .pt
    , ○a
    , ●a
    , Degen.○' n A d ○a ●a
    )
]

` This field should exist!
and Degen.● (n : Nat) (A : SST) (d : Degen n A) (ℓ : Degen.level n A d) (○a : ○ n A) (●a : ● n A ○a) : ● (suc. n) A (Degen.○ n A d ○a ●a) :=
match n
[
| zero. ↦ ℓ ●a
| suc. n ↦ ?
]


and Degen.○' (n : Nat) (A : SST) (d : Degen (suc. n) A)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s (○a .pt)) ○a :=
match n
[
| zero. ↦ (d .ℓ (○a .pt), (), ●a, ())
| suc. n ↦
    {`Degen.○' n A (d .∂σ)
      (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
      (○a .∂a' .a)`}
    {`Degen.○' 0 A ? (○a .pt, (), ○a .∂a .pt, ()) (○a .∂a' .pt)`}
    let ○a' :=
      (Degen.○' n A (d .∂σ)
        (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
        (○a .∂a' .a))
      : (○⁽ᵈ⁾
          (suc. n) (Nat.degen (suc. n))
          A (A .s (○a .pt))
          ( ○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a))
    in
      (( ○a' .pt
      , ○a .∂a'
      , ●a
      , (?, ?, ?, ?)) : ○⁽ᵈ⁾ (suc. (suc. n)) (suc. (suc. (Nat.degen n))) A (A .s (○a .pt)) ○a)
    
    {`( ?
    , ○a .∂a'
    , ●a
    , ? `Degen.○' n A (d .∂σ) (○a .∂a) (○a .a) x
        {`Degen.○'⁽ᵈ⁾
        n (Nat.degen n)
        A (A .s (○a .pt))
        (d .∂σ) (Degen.promote n A (d .∂σ) (d .ℓ) (○a .pt))
        (○a .∂a) (Degen.○' n A (d .∂σ) (○a .∂a) (○a .a))
        (○a .a) ?`}
    )`}
]

and Degen.●' (n : Nat) (A : SST) (d : Degen n A) (ℓ : Degen.level n A d)
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  : ●⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n))
      A (A .s (○a .pt))
      ○a (Degen.○' n A ? ○a ●a)
      (Degen.● n A d ℓ ? ?) := ?










{`
def Degen.res (n k : Nat) (h : k ≤ n) (A : SST) (d : Degen n A) : Degen k A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ d
  | suc. k ↦ absurd (Degen (suc. k) A) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ ()
  | suc. k ↦
      ( Degen.res n k h A (d .∂σ)
      , Degen.level.res n k h A (d .∂σ) (d .ℓ))
  ]
]

and Degen.level.res (n k : Nat) (h : k ≤ n) (A : SST) (d : Degen n A)
  (ℓ : Degen.level n A d) : Degen.level k A (Degen.res n k h A d) :=
match n  
[
| zero. ↦
  match k
  [
  | zero. ↦ ℓ
  | suc. k ↦ absurd (Degen.level (suc. k) A (absurd (Degen (suc. k) A) h)) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ Degen.level.res n 0 () A (d .∂σ) (d .ℓ)
  | suc. k ↦
      ?
  ]
]
`}

    {`sig
      ( ∂σ : Degen n A
      , σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A ∂σ ○a ●a)
      , ∂σ' : (x : A .z) → Degen⁽ᵈ⁾ n (Nat.degen n) A (A .s x) ∂σ
      ) `} 

{`def Degen (n : Nat) (A : SST) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    sig
      ( ∂σ : Degen n A
      , σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A ∂σ ○a ●a)
      , ∂σ' : (x : A .z) → Degen⁽ᵈ⁾ n (Nat.degen n) A (A .s x) ∂σ
      )     
]

and Degen.○ (n : Nat) (A : SST) (d : Degen n A) (○a : ○ n A) (●a : ● n A ○a)
  : ○ (suc. n) A :=
match n
[
| zero. ↦ (●a, (), ●a, ())
| suc. n ↦
    ( ○a .pt
    , ○a
    , ●a
    , ( Degen.zero n A d (○a .pt)
      , ○a .∂a'
      , ●a
      , ?
      )
    )
]


and Degen.zero (n : Nat) (A : SST) (d : Degen (suc. n) A) (x : A .z) : A .s x .z x :=
match n
[
| zero. ↦ d .σ () x
| suc. n ↦ Degen.zero n A (d .∂σ) x
]

and Degen.○' (n : Nat) (A : SST) (d : Degen (suc. n) A) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  : ○⁽ᵈᵈ⁾
      n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      A (A .s (○a .pt)) (A .s (○a .pt))
      (A .s (○a .pt) .s (○a .pt) (Degen.zero n A d (○a .pt)))
      (○a .∂a) (○a .∂a') (○a .∂a') :=
match n
[
| zero. ↦ ()
| suc. n ↦
    ( Degen.zero⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (d .∂σ) (d .∂σ' (○a .pt)) (○a .∂a .pt) (○a .∂a' .pt)
    , ?
    , ?
    , ?
    )
]`}


  {`( Degen.zero n A d (○a .pt)
  , ○a .∂a'
  , ●a
  , ?)`}


    {`( Degen.zero n A d (○a .pt)
      , ○a .∂a'
      , ●a
      , Degen.○⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (d .∂σ) (d .∂σ' (○a .pt)) (○a .∂a) (○a .∂a') (○a .a) ●a
      )`}








{`
def Degen.○ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  : Type :=
match n [
| zero. ↦
  match k
  [
  | zero. ↦ ⊤
  | suc. n ↦ ⊥
  ]
| suc. n ↦
  match k
  [
  | zero. ↦
    sig
      ( pt : A .s (○a .pt) .z (○a .pt)
      , ∂a :
        ○⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
          A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) pt)
          (○a .∂a) (○a .∂a') (○a .∂a')
      )
  | suc. k ↦
    sig
      ( ∂σa : Degen.○ n k h A (○a .∂a) (○a .a)
      , σa : ● (suc. n) A (Degen.∫ n k h A (○a .∂a) (○a .a) ∂σa)
      , ∂σa' :
        Degen.○⁽ᵈ⁾
          n (Nat.degen n)
          k (Nat.degen k)
          h (Nat.lte.degen k n h)
          A (A .s (○a .pt))
          (○a .∂a) (○a .∂a') 
          (○a .a) ●a
          ∂σa
     )
  ]
]

and Degen.○.∫ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (∂da : Degen.○ n k h A ○a ●a) : ○ (suc. n) A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ (●a, (), ●a, ())
  | suc. k ↦ absurd (○ 1 A) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ (○a .pt, ○a, ●a, (∂da .pt, ○a .∂a', ●a, ∂da .∂a))
  | suc. k ↦
    ( ○a .pt
    , Degen.○.∫ n k h A (○a .∂a) (○a .a) (∂da .∂σa)
    , ∂da .σa
    , Degen.○.∫⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k n h)
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (∂da .∂σa) (∂da .∂σa')
    )
  ]
]

def Degen.fin (n : Nat) (A : SST) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
  Σ
    (Degen.fin n A)
    (d ↦
      (k : Nat) (h : k ≤ n) (○a : ○ n A) (●a : ● n A ○a)
      → ● (suc. n) A (Degen.∫ n k h A d ○a ●a))
]

and Degen.assemble (n k : Nat) (h : k ≤ n) (A : SST) (d : Degen.fin n A)
  (○a : ○ n A) (●a : ● n A ○a) : ○ (suc. n) A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ (●a, (), ●a, ())
  | suc. k ↦ absurd (○ 1 A) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦
    ( ○a .pt
    , ○a
    , ●a
    , ( Degen.d₋₁ n A d (○a .pt)
      , ○a .∂a'
      , ●a
      , ?
      )
    )
  | suc. k ↦ ?
  ]
]
and Degen.d₋₁ (n : Nat) (A : SST) (d : Degen.fin (suc. n) A)
  : (x : A .z) → A .s x .z x :=
match n
[
| zero. ↦ x ↦ d .snd 0 () () x
| suc. n ↦ Degen.d₋₁ n A (d .fst)
]
`}




`and Degen.row (n : Nat) (A : SST) (d : Degen.trunc n A) : Type := ?

{`
def Degen (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  : Type :=
match n [
| zero. ↦
  match k
  [
  | zero. ↦ A .s ●a .z ●a
  | suc. n ↦ ⊥
  ]
| suc. n ↦
  match k
  [
  | zero. ↦
    sig
      ( pt : A .s (○a .pt) .z (○a .pt)
      , ∂a :
        ○⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
          A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) pt)
          (○a .∂a) (○a .∂a') (○a .∂a')
      , a :
        ●⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
          A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) pt)
          (○a .∂a) (○a .∂a') (○a .∂a') ∂a
          (○a .a) ●a ●a
      )
  | suc. k ↦
    sig
      ( σa : Degen n k h A (○a .∂a) (○a .a)
      , σa' :
        Degen⁽ᵈ⁾
          n (Nat.degen n)
          k (Nat.degen k)
          h (Nat.lte.degen k n h)
          A (A .s (○a .pt))
          (○a .∂a) (○a .∂a') 
          (○a .a) ●a
          σa
     )
  ]
]

` extraction functions

def Degen.○ (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (da : Degen n k h A ○a ●a) : ○ (suc. n) A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ (●a, (), ●a, ())
  | suc. k ↦ absurd (○ 1 A) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ (○a .pt, ○a, ●a, (da .pt, ○a .∂a', ●a, da .∂a))
  | suc. k ↦
    ( ○a .pt
    , Degen.○ n k h A (○a .∂a) (○a .a) (da .σa)
    , Degen.● n k h A (○a .∂a) (○a .a) (da .σa)
    , Degen.○⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k n h)
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (da .σa) (da .σa')
    )
  ]
]

and Degen.● (n k : Nat) (h : k ≤ n) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (da : Degen n k h A ○a ●a) : ● (suc. n) A (Degen.○ n k h A ○a ●a da)  :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ da
  | suc. k ↦ absurd (A .s (absurd (○ 1 A) h .pt) .z (absurd (○ 1 A) h .a)) h
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ da .a
  | suc. k ↦
    Degen.●⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k n h)
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      (da .σa) (da .σa')
  ]
]

` demo

axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

axiom d₀f : Degen 2 0 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f
axiom d₁f : Degen 2 1 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f
axiom d₂f : Degen 2 2 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f

def σ₀f : A .s x .s x (d₀f .pt) .s y α α (d₀f .∂a .pt) .z z β β (d₀f .∂a .a) γ f f
  := Degen.● 2 0 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f d₀f
def σ₁f : A .s x .s y α .s y α (d₁f .σa .pt) (d₁f .σa' .pt) .z z β γ f γ f (d₁f .σa .a)
  := Degen.● 2 1 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f d₁f
def σ₂f : A .s x .s y α .s z β γ f .z z β γ f (d₂f .σa .σa) (d₂f .σa' .σa) (d₂f .σa .σa')
  := Degen.● 2 2 () A (x, (y, (), z, ()), γ, (α, (), β, ())) f d₂f
`}

{`axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

axiom d : Degen 3 A

def d₀f : A .s x .s y α .s z β γ f .z z β γ f (d .∂σ .∂σ .σ ()z)
  (d .∂σ .∂σ' x .σ ()()z β) (d .∂σ .σ ( y, (), z, () ) γ)
  := d .σ (x, (y, (), z, ()), γ, (α, (), β, ())) f

def d₁f : A .s x .s y α .s z β γ f .z z β γ f (d .∂σ .∂σ .σ ()z)
  (d .∂σ' x .∂σ .σ ()()z β) (d .∂σ .σ ( y, (), z, () ) γ)
  := d .∂σ' x .σ (y, (), z, ()) (α, (), β, ()) γ f

def d₁f : A .s x .s y α .s z β γ f .z z β γ f (d .∂σ .∂σ .σ ()z)
  (d .∂σ' x .∂σ .σ ()()z β) (d .∂σ .∂σ' y .σ ()()z γ)
 := d .∂σ' x .∂σ' y α .σ () () () () z β γ f
`}
