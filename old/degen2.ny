{` Prelude `}

def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

def Gel²
  (Ap : Type) (Ax Ay : Type⁽ᵈ⁾ Ap)
  (Aα : (p : Ap) → Ax p → Ay p → Type)
  : Type⁽ᵈᵈ⁾ Ap Ax Ay := sig p x y ↦ (ungel : Aα p x y)

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

def Sec (A : SST) (A' : SST⁽ᵈ⁾ A) : Type :=
codata
[
| 𝓈 .z : (x : A .z) → A' .z x 
| 𝓈 .s : (x : A .z) → Sec⁽ᵈ⁾ A (A .s x) A' (sym (A' .s x (𝓈 .z x))) 𝓈
]

def Coslice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (y ↦ A .s y .z x)
| .s ↦ y α ↦ sym (Coslice⁽ᵈ⁾ A (A .s y) x (α .ungel))
]

def Opposite (A : SST) : SST :=
[
| .z ↦ A .z
| .s ↦ x ↦ Opposite⁽ᵈ⁾ A (Coslice A x)
]

def ∫ (B : SST) (E : SST⁽ᵈ⁾ B) : SST := [
| .z ↦ Σ (B .z) (b ↦ E .z b)
| .s ↦ ∫e ↦ ∫⁽ᵈ⁾ B (B .s (∫e .fst)) E (sym (E .s (∫e .fst) (∫e .snd)))
]


` Morally the opposite of ∫ A (A .s x), but with better definitional behaviour.
def Fib (A : SST) (x : A .z) : SST :=
[
| .z ↦ Σ (A .z) (y ↦ A .s x .z y)
| .s ↦ yα ↦ Fib⁽ᵈ⁾ A (Coslice A (yα .fst)) x (ungel := yα .snd)
]

` simplex boundaries and fillers
def ○ (n : Nat) (A : SST) : Type :=
match n
[
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
match n
[
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]
def ○.drop (n : Nat) (A : SST) (○a : ○ (suc. n) A) : ○ n A :=
match n
[
| zero. ↦ ()
| suc. n ↦
  ( ○a .pt
  , ○.drop n A (○a .∂a)
  , ●.drop n A (○a .∂a) (○a .a)
  , ○.drop⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a')
  )
]
and ●.drop (n : Nat) (A : SST) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  : ● n A (○.drop n A ○a) :=
match n
[
| zero. ↦ ○a .pt
| suc. n ↦ ●.drop⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a) ●a
]

def ○.snoc
  (n : Nat) (A : SST)
  (x : A .z)
  (○a : ○ n A)
  (●a : ● n A ○a)
  (○a' : ○⁽ᵈ⁾ n (Nat.degen n) A (Coslice A x) ○a)
  : ○ (suc. n) A :=
match n [
| zero. ↦ (●a, (), x, ())
| suc. n ↦
  ( ○a .pt
  , ○.snoc n A x (○a .∂a) (○a .a) (○a' .∂a)
  , ●.snoc n A x (○a .∂a) (○a .a) (○a' .∂a) (○a' .a) ?
  , ?
  )
]

and ●.snoc
  (n : Nat) (A : SST)
  (x : A .z)
  (○a : ○ (suc. n) A)
  (●a : ● (suc. n) A ○a)
  (○a' : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (Coslice A x) ○a)
  (●a' : ●⁽ᵈ⁾ n (Nat.degen n) A
           (A .s (○a .pt))
           (○.snoc n A x (○a .∂a) (○a .a) (○a' .∂a))
           (○.snoc n A x (○a .∂a) (○a .a) (○a' .∂a) .∂a')
           (○.snoc n A x (○a .∂a) (○a .a) (○a' .∂a) .a))
  ` (●a' : ● n A ())
  ` ` (●a' : ●⁽ᵈ⁾ n (Nat.degen n) A (Coslice A x) ○a)
  : ● (suc. n) A (○.snoc n A x ○a ●a) :=
match n [
| zero. ↦ ?
| suc. n ↦ ?
]




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

def Degen.○
  (n k : Nat) (h : k ≤ n)
  (A : SST)
  (○a : ○ n A)
  (●a : ● n A ○a)
  (d : Degen A)
  : ○ (suc. n) A :=
match n [
| zero. ↦ match k [
  | zero. ↦ (●a, (), ●a, ())
  | suc. k ↦ match h []
  ]
| suc. n ↦ match k [
  | zero. ↦
    ( ○a .pt
    , Degen.○ n 0 () A (○a .∂a) (○a .a) d
    , Degen.● n 0 () A (○a .∂a) (○a .a) d
    , Degen.○⁽ᵈ⁾ n (Nat.degen n) 0 0 () ()
        A (A .s (○a .pt))
        (○a .∂a) (○a .∂a')
        (○a .a) ●a
        d ?
    )
  | suc. k ↦
    ?
    ` ( ○a .pt
    ` , Degen.○ n k h A (○a .∂a) (○a .a) d
    ` , Degen.● n k h A (○a .∂a) (○a .a) d
    ` , Degen.○⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) h ?
    `     A (Coslice A (○a .pt))
    `     (○a .∂a) ?
    `     (○a .a) ?
    `     d (d .s ?)
    ` )
  ]
]


and Degen.●
  (n k : Nat) (h : k ≤ n)
  (A : SST)
  (○a : ○ n A)
  (●a : ● n A ○a)
  (d : Degen A)
  : ● (suc. n) A (Degen.○ n k h A ○a ●a d) := ?
quit
  ` ((x , σx) , ○a , ●a , Degen.○' n A x σx ○a ●a d)

` and Degen.○'
`   (n : Nat) (A : SST)
`   (x : A .z)
`   (σx : A .s x .z x)
`   (○a : ○ n (Fib A x))
`   (●a : ● n (Fib A x) ○a)
`   (d : Sec (Fib A x) (Degen A x σx))
`   : ○⁽ᵈ⁾ n (Nat.degen n) (Fib A x) (Fib⁽ᵈ⁾ A (Coslice A x) x (ungel ≔ σx)) ○a :=
` match n
` [
` | zero. ↦ ()
` | suc. n ↦
`   ( (? , ?)
`   , ?
`   , ?
`   , ?
`   )
` ]

 

axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

axiom σx : A .s x .z x
axiom σα : A .s x .s x σx .z y α α
axiom σβ : A .s x .s x σx .z z β β

axiom d : Sec (Fib A x) (Degen A x σx)

def cool : Gel⁽ᵈ⁾ (A .z) (A .s x .z) (y ↦ A .s y .z z)
            (y ⤇ A .s x .s y.0 y.1 .z z β) y α (ungel := γ) := (ungel := f)

echo d .z (y, α) .ungel

echo (d .s (z, β) .z (y, α) ((ungel := γ), sym cool) .ungel)^(321) .ungel

quit

def SST.Σ (A : SST) (A' : SST⁽ᵈ⁾ A) : SST :=
[
| .z ↦ Σ (A .z) (x ↦ A' .z x)
| .s ↦ xy ↦ SST.Σ⁽ᵈ⁾ A (A .s (xy .fst)) A' (sym (A' .s (xy .fst) (xy .snd)))
]

def coslice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (y ↦ A .s y .z x)
| .s ↦ y α ↦ sym (coslice⁽ᵈ⁾ A (A .s y) x (α .ungel))
]

def opposite (A : SST) : SST :=
[
| .z ↦ A .z
| .s ↦ x ↦ opposite⁽ᵈ⁾ A (coslice A x)
]

def Fib (A : SST) (x : A .z) : SST :=
[
| .z ↦ Σ (A .z) (y ↦ coslice A y .z x)
| .s ↦ yα ↦ Fib⁽ᵈ⁾ A (coslice A (yα .fst)) x (yα .snd)
]

def Sec (A : SST) (A' : SST⁽ᵈ⁾ A) : Type :=
codata
[
| 𝓈 .z : (x : A .z) → A' .z x 
| 𝓈 .s : (x : A .z) → Sec⁽ᵈ⁾ A (A .s x) A' (sym (A' .s x (𝓈 .z x))) 𝓈
]

{` degeneracy structures `}

` simplex boundaries and fillers

def ○ (n : Nat) (A : SST) : Type :=
match n
[
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
match n
[
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]

def Degen (A : SST) (x : A .z) (σx : A .s x .z x) : SST⁽ᵈ⁾ (Fib A x) :=
[
| .z ↦
  Gel
    (Fib A x .z)
    (yα ↦
      A .s x .s x σx
        .z (yα .fst) (yα .snd .ungel) (yα .snd .ungel))
| .s ↦ yα σα ↦
  sym
    (Degen⁽ᵈ⁾
      A (coslice A (yα .fst))
      x (ungel := yα .snd .ungel)
      σx (sym (ungel := σα .ungel)))
]

def Degen.○
  (n : Nat) (A : SST)
  (x : A .z)
  (σx : A .s x .z x)
  (○a : ○ n (Fib A x))
  (●a : ● n (Fib A x) ○a)
  (d : Sec (Fib A (○a .pt)) (Degen A (○a .pt) σx))
  : ○ (suc. n) (Fib A x) := ?
  ` (○a .pt, ○a, ●a, (σx, ○a .∂a', ●a, Degen.○' n A ○a ●a σx d))

and Degen.○' (n : Nat) (A : SST) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (σx : A .s (○a .pt) .z (○a .pt))
  (d : Sec (Fib A (○a .pt)) (Degen A (○a .pt) σx))
  : ○⁽ᵈᵈ⁾
      n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) σx)
      (○a .∂a) (○a .∂a') (○a .∂a') :=
match n
[
| zero. ↦ ()
| suc. n ↦
    ( d .z (○a .∂a .pt, (ungel := ○a .∂a' .pt)) .ungel
    , Degen.○' n A
        (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
        (○a .∂a' .a) σx d
    , ?
    , ?
    )
]

and Degen.● (n : Nat) (A : SST) (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
  (σx : A .s (○a .pt) .z (○a .pt))
  (d : Sec (Fib A (○a .pt)) (Degen A (○a .pt) σx))
  : ● (suc. (suc. n)) A (Degen.○ n A ○a ●a σx d) :=
match n
[
| zero. ↦ d .z (○a .a, (ungel := ●a)) .ungel
| suc. n ↦
    Degen.●⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .∂a .pt))
      (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
      (σx, ○a .∂a .∂a', ○a .∂a' .a, ○a .∂a' .∂a')
      ? ?
      ? ?
]


{`
axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

axiom σx : A .s x .z x
axiom σα : A .s x .s x σx .z y α α
axiom σβ : A .s x .s x σx .z z β β

echo Degen A x σx .s (z, (ungel := β)) (ungel := σβ) .z (y, (ungel := α)) (ungel := σα) ((ungel := γ), ?)
`}

{`
def Degen (A : SST) (x : A .z) (σx : A .s x .z x) : SST⁽ᵈ⁾ (oposite (SST.Σ A (A .s x))) :=
[
| .z ↦ Gel (oposite (SST.Σ A (A .s x)) .z) (yα ↦ A .s x .s x σx .z (yα .fst) (yα .snd) (yα .snd))
| .s ↦ yα σα ↦ sym (Degen⁽ᵈ⁾ A (coslice A (yα .fst)) x (ungel := yα .snd) σx (sym (ungel := σα .ungel)))
]
`}

{`
def Degen (A : SST) (x : A .z) (σx : A .s x .z x) : SST⁽ᵈ⁾ (SST.Σ A (A .s x)) :=
[
| .z ↦ Gel (SST.Σ A (A .s x) .z) (yα ↦ A .s x .s x σx .z (yα .fst) (yα .snd) (yα .snd))
| .s ↦ yα σα ↦ sym (Degen⁽ᵈ⁾ A (coslice A (yα .fst)) x (ungel := yα .snd) σx ?)
]
`}

{`
def Degen (A : ASST) (p : A .z) : SST⁽ᵈ⁾ (Fib A p) :=
[
| .z ↦ Gel (A .s .z p) (x ↦ A .s .s .z p ? ?)
| .s ↦ x σx ↦ Degen⁽ᵈ⁾ A (A .s) p x
]

axiom A : ASST
axiom p : A .z
axiom x : A .s .z p x
axiom y : A .s .z p x
axiom α : A .s .s .z p x y

echo Degen A p .z ?
`}

`echo Degen A x .z

`axiom σx : Degen A x .z

`echo Degen A x .s σx .z σx

{`
def Sk (n k : Nat) (A : SST) : Type :=
match n
[
| zero. ↦ A .z
| suc. n ↦
    match k
    [
    | zero. ↦
        sig
          ( pt : A .z
          , ∂a : Sk n 0 A
          )
    | suc. k ↦
        sig
          ( pt : A .z
          , ∂a : Sk n k A
          , a : Sk.● n k A ∂a
          , ∂a' :
              Sk⁽ᵈ⁾
                n (Nat.degen n)
                k (Nat.degen k)
                A (A .s pt)
                ∂a
          )
    ]
]

and Sk.● (n k : Nat) (A : SST) (𝓈 : Sk n k A) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    match k
    [
    | zero. ↦
        sig
          ( ∂a :
              Sk⁽ᵈ⁾
                n (Nat.degen n)
                0 ()
                A (A .s (𝓈 .pt))
                (𝓈 .∂a)
          , a : Sk.● n 0 A (𝓈 .∂a)
          )
    | suc. k ↦
        sig
          ( a : Sk.● n (suc. k) A (𝓈 .∂a)
          , ∂a' :
              Sk.●⁽ᵈ⁾
                n (Nat.degen n)
                k (Nat.degen k)
                A (A .s pt)
                (𝓈 .∂a) (𝓈 .a)
          )
    ]
]


axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

def sk0 : Sk 2 0 () A := ?
`}
`def sk1 : Sk 2 1 () A := (x, (y, z), (?, ?))



` links

{`
def Link.○ (n m : Nat) (A : SST) (○a : ○ n A)
  (○b : ○ m A) (●b : ● m A ○b) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    sig
      ( ∂pt : ○⁽ᵈ⁾ m (Nat.degen m) A (A .s (○a .pt)) ○b
      , pt : ●⁽ᵈ⁾ m (Nat.degen m) A (A .s (○a .pt)) ○b ∂pt ●b
      , ∂a : Link.○ n m A (○a .∂a) (○a .a) ○b ●b
      , a : Link.● n m A (○a .∂a) (○a .a) ○b ●b ∂a
      , ∂a' :
        Link.○⁽ᵈ⁾
          n (Nat.degen n)
          m (Nat.degen m)
          A (A .s (○a .pt))
          (○a .∂a) (○a .∂a')
          ○b ∂pt
          ●b pt
          ∂a
      )
]

and Link.● (n m : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (○b : ○ m A) (●b : ● m A ○b) (○ab : Link.○ n m A ○a ●a ○b ●b) : Type :=
match n
[
| zero. ↦ ?
  `●⁽ᵈ⁾ m (Nat.degen m) A (A .s ●a) ○b ○ab ●b
| suc. n ↦ ?
    {`Link.●⁽ᵈ⁾
      n (Nat.degen n)
      m (Nat.degen m)
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a) ●a
      ○b (○ab .∂pt)
      ●b (○ab .pt)
      (○ab .∂a) (○ab .∂a')
      (○ab .a)`}
]
`}

` degeneracies

{`def Degen₀ (k n : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a) : Type :=
match k
[
| zero. ↦ ⊤
| suc. k ↦
  match n
  [
  | zero. ↦ A .s ●a .z ●a
  | suc. n ↦
      sig
        ( pt : A .s (○a .pt) .z (○a .pt)
        , ∂a : Degen₀ k n A (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a)
        , a : ?
        , ∂a' :
        `∂a : Degen₀ k A ○a ●a
        , ∂a' :
          Degen₀⁽ᵈ⁾
            k (Nat.degen k)
            n (Nat.degen n)
            A (A .s (○a .pt))
            (○a .∂a) (○a .∂a')
  ]
]`}

{`
def Degen₀.data (n : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    sig
      ( pt : A .s (○a .pt) .z (○a .pt)
      , ∂a :
          ○⁽ᵈᵈ⁾
            n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
            A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) pt)
            (○a .∂a) (○a .∂a') (○a .∂a')
      )
]

and Degen₀.○ (n : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (∂σ : Degen₀.data n A ○a ●a) : ○ (suc. n) A :=
match n
[
| zero. ↦ (●a, (), ●a, ())
| suc. n ↦
    ( ○a .pt
    , ○a
    , ●a
    , ( ∂σ .pt
      , ○a .∂a'
      , ●a
      , ∂σ .∂a
      )
    )
] 

def Degen₀.promote  (n : Nat) (A : SST) 
  (∂σ : (○a : ○ n A) (●a : ● n A ○a) → Degen₀.data n A ○a ●a)
  (σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen₀.○ n A ○a ●a (∂σ ○a ●a)))
  (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a) : Degen₀.data (suc. n) A ○a ●a :=
match n
[
| zero. ↦ (σ () (○a .pt), ())
| suc. n ↦
    ( ∂σ (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a) .pt
    , ( ?
      , ∂σ (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a) .∂a
      , σ (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a)
      , ?
      )
    )
]
`}

{`
pt : A .s (○a .pt) .z (○a .pt)
      , ∂a :
        ○⁽ᵈᵈ⁾
          n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
          A (A .s (○a .pt)) (A .s (○a .pt)) (A .s (○a .pt) .s (○a .pt) pt)
          (○a .∂a) (○a .∂a') (○a .∂a')
`}

{`
def Degen (n : Nat) (A : SST) : Type :=
match n
[
| zero. ↦ ⊤
| suc. n ↦
    sig
      ( ∂σ : Degen n A
      , σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A ∂σ ○a ●a)
      ) 
]

and Degen.○ (n : Nat) (A : SST) (d : Degen n A)
  (○a : ○ n A) (●a : ● n A ○a) : ○ (suc. n) A :=
match n
[
| zero. ↦ (●a, (), ●a, ())
| suc. n ↦ ?
]

and Degen.res.∂σ (n k : Nat) (h : k ≤ n) (A : SST) (d : Degen n A) : Degen k A :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ d
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ Degen.res.∂σ n 0 () A (d .∂σ)
  | suc. k ↦
      ( Degen.res.∂σ n k h A (d .∂σ)
      , Degen.res.σ n k h A (d .∂σ) (d .σ)
      )
  ]
]

and Degen.res.σ (n k : Nat) (h : k ≤ n) (A : SST) (d : Degen n A)
  (σ : (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A d ○a ●a))
  : (○a : ○ k A) (●a : ● k A ○a) → ● (suc. k) A (Degen.○ k A (Degen.res.∂σ n k h A d) ○a ●a) :=
match n
[
| zero. ↦
  match k
  [
  | zero. ↦ σ
  | suc. k ↦ match h []
  ]
| suc. n ↦
  match k
  [
  | zero. ↦ Degen.res.σ n 0 () A (d .∂σ) (d .σ)
  | suc. k ↦ ?
  ]
]
`}

{`
and Degen.ind (n m : Nat) (A : SST) (d : Degen n A) (d : Degen n A)
  (○a : ○ n A) (●a : ● n A ○a) (○b : ○ (suc. m) A) (●b : ● (suc. m) A ○b)
  (○ab : Link.○ n (suc. m) A ○a ●a ○b ●b) (●ab : Link.● n (suc. m) A ○a ●a ○b ●b ○ab)
  : Link.○ (suc. n) m A (Degen.○
`}



{`
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
codata
[
| ℓ .z :
    (○a : ○ n A) (●a : ● n A ○a) → ● (suc. n) A (Degen.○ n A d ○a ●a) 
| ℓ .s :
    (x : A .z)
      → Degen.level⁽ᵈ⁾
        n (Nat.degen n)
        A (A .s x)
        d (Degen.promote n A d x)
        ℓ
]

and Degen.promote (n : Nat) (A : SST) (d : Degen n A) (x : A .z)
  : Degen⁽ᵈ⁾ n (Nat.degen n) A (A .s x) d :=
match n
[
| zero. ↦ ()
| suc. n ↦
    ( Degen.promote n A (d .∂σ) x
    , d .ℓ .s x
    )
]

and Degen.zero (n : Nat) (A : SST) (d : Degen (suc. n) A) (x : A .z) : A .s x .z x :=
match n
[
| zero. ↦ d .ℓ .z () x
| suc. n ↦ ?
]

and Degen.○ (n : Nat) (A : SST) (d : Degen n A)
  (○a : ○ n A) (●a : ● n A ○a) : ○ (suc. n) A :=
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
      , Degen.○' n A d (○a .pt) (○a .∂a) (○a .∂a'))
    )
]

and Degen.○' (n : Nat) (A : SST) (d : Degen (suc. n) A)
  (x : A .z) (○a : ○ n A) (○a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s x) ○a)
  : ○⁽ᵈᵈ⁾
      n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      A (A .s x) (A .s x) (A .s x .s x (Degen.zero n A d x))
      ○a ○a' ○a' :=
match n
[
| zero. ↦ ()
| suc. n ↦ ?
]
`}

{`
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
      , σ : (○a : ○ (suc. n) A) (●a : ● (suc. n) A ○a)
            → ● (suc. (suc. n)) A
              ( ○a .pt
              , ○a
              , ●a
              , ( Degen.zero n A d (○a .pt)
                , ○a .∂a'
                , ●a
                , Degen.○ n A d (○a .pt) (○a .∂a) (○a .∂a'))
              )
      )
]

and Degen.zero (n : Nat) (A : SST) (d : Degen (suc. n) A) (x : A .z) : A .s x .z x :=
match n
[
| zero. ↦ d .ℓ x
| suc. n ↦ Degen.zero n A (d .∂σ) x
]

and Degen.one (n : Nat) (A : SST) (d : Degen (suc. (suc. n)) A) : Degen 2 A :=
match n
[
| zero. ↦ d
| suc. n ↦ Degen.one n A (d .∂σ)
]

and Degen.○ (n : Nat) (A : SST) (d : Degen (suc. n) A)
  (x : A .z) (○a : ○ n A) (○a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s x) ○a)
  : ○⁽ᵈᵈ⁾
      n (Nat.degen n) (Nat.degen n) (Nat.degen⁽ᵈ⁾ n (Nat.degen n))
      A (A .s x) (A .s x) (A .s x .s x (Degen.zero n A d x))
      ○a ○a' ○a' :=
match n
[
| zero. ↦ ()
| suc. n ↦
    ( ?
    , Degen.○ n A (d .∂σ) x (○a .∂a) (○a' .∂a)
    , d .ℓ .σ
        (x, ○a .∂a, ○a .a, ○a' .∂a)
        (○a' .a)
    , ? {`(Degen.○⁽ᵈ⁾
        n (Nat.degen n)
        A (A .s (○a .pt))
        (d .∂σ) ?
        x ?
        (○a .∂a) ?
        (○a' .∂a) ?)⁽³²¹⁾`}
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
`}

