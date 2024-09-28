` ----------------------------------------
` Generalized cells.
` ----------------------------------------

import "prelude"
import "sst"

section SST :=
  import SST

  ` An (n,k) cell in `A` has `n` points, and fillers
  ` to the generated filling problems only up to dimension `k`.
  def Cell (n k : Nat) (A : SST) : Type :=
    match n, k [
    | zero., _ ↦ ⊤
    | suc. n, zero. ↦ codata [
      | P .pt : A .z
      | P .rest : Cell n zero. A
      ]
    | suc. n, suc. k ↦ codata [
      | P .pt : A .z
      | P .rest : Cell n (suc. k) A
      | P .solve : Cell⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) A (A .s (P .pt)) (Cell.∂ n k A (P .rest))
      ]
    ]

  ` We can forget fillers in the highest dimension.
  and Cell.∂ (n k : Nat) (A : SST) (K : Cell n (suc. k) A) : Cell n k A :=
    match n, k [
    | zero., _ ↦ ()
    | suc. n, zero. ↦ [
      | .pt ↦ K .pt
      | .rest ↦ Cell.∂ n zero. A (K .rest)
      ]
    | suc. n, suc. k ↦ [
      | .pt ↦ K .pt
      | .rest ↦ Cell.∂ n (suc. k) A (K .rest)
      | .solve ↦
        Cell.∂⁽ᵈ⁾
          n (Nat.degen n)
          k (Nat.degen k)
          A (A .s (K .pt))
          (Cell.∂ n (suc. k) A (K .rest)) (K .solve)
      ]
    ]

  ` Here's a short example: if `k` is a (3,1) cell,
  ` then there are 3 points, edges connecting all of them,
  ` but no interior cell.
  section CellExample :=
    axiom A : SST

    axiom k : Cell 3 1 A

    def x : A .z := k .pt
    def y : A .z := k .rest .pt
    def z : A .z := k .rest .rest .pt

    def α : A .s x .z y := k .solve .pt
    def β : A .s x .z z := k .solve .rest .pt
    def γ : A .s y .z z := k .rest .solve .pt
  end
