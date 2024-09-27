import "prelude"
import "sst"
import "boundary"


def tSST (k : Nat) : Type :=
match k [
| zero. ↦ ⊤
| suc. k ↦ sig (∂A : tSST k, ●A : tSST.○ k ∂A → Type)
]

and tSST.π (k : Nat) (A : tSST (suc. k)) : tSST k := A .∂A

and tSST.○ (k : Nat) (A : tSST k) : Type :=
match k [
| zero. ↦ ⊤
| suc. k ↦
  sig
    ( pt : tSST.z k A
    , ∂a : tSST.○ k (A .∂A)
    , a : A .●A ∂a
    , ∂a' : tSST.○⁽ᵈ⁾ k (Nat.degen k) (A .∂A) (tSST.s k A pt) ∂a
    )
]

and tSST.z (k : Nat) (A : tSST (suc. k)) : Type :=
match k [
| zero. ↦ A .●A ()
| suc. k ↦ tSST.z k (A .∂A)
]

and tSST.s
  (k : Nat) (A : tSST (suc. k)) (x : tSST.z k A)
  : tSST⁽ᵈ⁾ k (Nat.degen k) (tSST.π k A)
  :=
match k [
| zero. ↦ ()
| suc. k ↦ (tSST.s k (A .∂A) x , ○a ○a' ↦ Gel (A .∂A .●A ○a) (●a ↦ A .●A (x, ○a, ●a , ○a')))
]
