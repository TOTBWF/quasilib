` ----------------------------------------
` Simplex Boundaries / Fillers
` ----------------------------------------

import "prelude"
import "sst"

section SST :=
  import SST

  ` The type of `n`-bounaries in an SST, where the first `k` dimensions
  ` are taken to be slices rather than coslices.
  def ○ (n k : Nat) (A : SST) : Type :=
  match k, n [
  | zero. , zero.  ↦ ⊤
  | zero. , suc. n ↦
    sig
      ( pt : A .z
      , ∂a : ○ n zero. A
      , a : ● n zero. A ∂a
      , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) zero. zero. A (A .s pt) ∂a
      )
  | suc. k , zero.  ↦ ⊥
  | suc. k , suc. n ↦
    sig
      ( pt : A .z
      , ∂a : ○ n k A
      , a : ● n k A ∂a
      , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) A (Slice A pt) ∂a
      )
  ]

  ` The type of fillers for an n-boundary in an SST.
  and ● (n k : Nat) (A : SST) (○a : ○ n k A) : Type :=
  match k, n [
  | zero. , zero.  ↦ A .z
  | zero. , suc. n ↦
    ●⁽ᵈ⁾
      n (Nat.degen n)
      zero. zero.
      A (A .s (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a)
  | suc. k , zero.  ↦ ⊥
  | suc. k , suc. n ↦
    ●⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      A (Slice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a)
  ]
end
