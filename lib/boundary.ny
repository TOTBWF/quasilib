` ----------------------------------------
` Simplex Boundaries / Fillers
` ----------------------------------------

import "prelude"
import "sst"

section SST :=
  import SST

  ` The type of n-boundaries in an SST.
  def ○ (n : Nat) (A : SST) : Type :=
  match n [
  | zero.  ↦ ⊤
  | suc. n ↦
    sig
      ( pt : A .z
      , ∂a : ○ n A
      , a : ● n A ∂a
      , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ∂a
      )
  ]

  ` The type of n-boundary fillers in an SST.
  and ● (n : Nat) (A : SST) (○a : ○ n A) : Type :=
  match n [
  | zero.  ↦ A .z
  | suc. n ↦
    ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
  ]

  ` Generalization of an n-boundary, where 'k' many edges
  ` are slices rather than coslices.
  def ○₁ (n k : Nat) (A : SST) : Type :=
  match k, n [
  | zero.  , n      ↦ ○ n A
  | suc. k , zero.  ↦ ⊥
  | suc. k , suc. n ↦
    sig
      ( pt : A .z
      , ∂a : ○₁ n k A
      , a : ●₁ n k A ∂a
      , ∂a' : ○₁⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) A (Slice A pt) ∂a
      )
  ]

  ` Generalization of an n-boundary filler, where 'k' many edges
  ` are slices rather than coslices.
  and ●₁ (n k : Nat) (A : SST) (○a : ○₁ n k A) : Type :=
  match k, n [
  | zero.  , n      ↦ ● n A ○a
  | suc. k , zero.  ↦ ⊥
  | suc. k , suc. n ↦
    ●₁⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      A (Slice A (○a .pt))
      (○a .∂a) (○a .∂a')
      (○a .a)
  ]

  ` Given a single "snoc" n-boundary, form an n-boundary.
  def ○.↓₂ (n : Nat) (A : SST) (○a : ○₁ (suc. n) 1 A) : ○ (suc. n) A :=
  match n [
  | zero.  ↦ (○a .a, (), ○a .pt, ())
  | suc. n ↦
    ( ○a .∂a .pt
    , ○.↓₂ n A (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
    , ●.↓₂ n A (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a) (○a .∂a' .a)
    , ○.↓₂⁽ᵈ⁾
        n (Nat.degen n)
        A (A .s (○a .∂a .pt))
        (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
        (○a .∂a' .pt .ungel, ○a .∂a .∂a', ○a .a, sym (○a .∂a' .∂a'))
    )
  ]

  ` Given a single "snoc" n-boundary filler, form an n-boundary filler.
  and ●.↓₂ (n : Nat) (A : SST) (○a : ○₁ (suc. n) 1 A)
    (●a : ●₁ (suc. n) 1 A ○a) : ● (suc. n) A (○.↓₂ n A ○a) :=
  match n [
  | zero.  ↦ ●a .ungel
  | suc. n ↦
    ●.↓₂⁽ᵈ⁾
      n (Nat.degen n)
      A (A .s (○a .∂a .pt))
      (○a .pt, ○a .∂a .∂a, ○a .∂a .a, ○a .∂a' .∂a)
      (○a .∂a' .pt .ungel, ○a .∂a .∂a', ○a .a, sym (○a .∂a' .∂a'))
      (○a .∂a' .a)
      (sym ●a)
  ]
end
