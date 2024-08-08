import "prelude"
import "sst"
import "boundary"

import SST

` An (n, k) horn in an SST.
def Horn.○ (n k : Nat) (A : SST) (○a : ○ n A) : Type :=
match n, k [
| zero.  , zero.         ↦ A .z
| zero.  , suc. zero.    ↦ A .z
| zero.  , suc. (suc. k) ↦ ⊥
| suc. n , zero.         ↦
  sig
    ( pt : A .z
    , Λa : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s pt) ○a
    )
| suc. n , suc. k        ↦
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

` A filler of an (n, k) horn in an SST.
and Horn.●
  (n k : Nat) (A : SST) (○a : ○ n A) (●a : ● n A ○a)
  (Λ : Horn.○ n k A ○a) : Type :=
match n, k [
| zero.  , zero.         ↦ A .s Λ .z ●a
| zero.  , suc. zero.    ↦ A .s ●a .z Λ
| zero.  , suc. (suc. k) ↦ ⊥
| suc. n , zero.         ↦
  ●⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s (Λ .pt)) ○a (Λ .Λa) ●a
| suc. n , suc. k        ↦
  Horn.●⁽ᵈ⁾
    n (Nat.degen n)
    k (Nat.degen k)
    A (A .s (○a .pt))
    (○a .∂a) (○a .∂a')
    (○a .a) ●a
    (Λ .Λa) (Λ .Λa')
    (Λ .a)
]

def Horn.○.unop
  (n k : Nat) (A : SST)
  (○a : ○ n (Op A))
  (Λ : Horn.○ n k (Op A) ○a)
  : Horn.○ n (Nat.sub (suc. n) k) A (○.unop n A ○a) :=
match n, k [
| zero.  , zero.         ↦ Λ
| zero.  , suc. zero.    ↦ Λ
| zero.  , suc. (suc. k) ↦ match Λ []
| suc. n , zero.         ↦
  let cool := ○.unop⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (SST.Slice A (Λ .pt)) ○a (Λ .Λa) in ?
| suc. n , suc. k        ↦ ?
]

and Horn.●.unop
  (n k : Nat) (A : SST)
  (○a : ○ n (Op A)) (●a : ● n (Op A) ○a)
  (Λ : Horn.○ n k (Op A) ○a) (▲ : Horn.● n k (Op A) ○a ●a Λ)
  : Horn.● n (Nat.sub (suc. n) k) A
      (○.unop n A ○a) (●.unop n A ○a ●a)
      (Horn.○.unop n k A ○a Λ)
  := ?
