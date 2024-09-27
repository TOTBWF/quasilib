import "prelude"
import "sst"
import "boundary"

` The type of SSTs, where all data at or above dimension `k` is trivial.
def tSST (k : Nat) : Type :=
match k [
| zero. ↦ ⊤
| suc. k ↦ codata [
  | X .z : Type
  | X .s : X .z → tSST⁽ᵈ⁾ k (Nat.degen k) (tSST.π (suc. k) X)
  ]
]

` Note that it is really easy to get a lower dimensional tSST with this data.
and tSST.π (k : Nat) (X : tSST k) : tSST (Nat.pred k) :=
match k [
| zero. ↦ ()
| suc. zero. ↦ ()
| suc. (suc. k) ↦ [
  | .z ↦ X .z
  | .s ↦ x ↦
    tSST.π⁽ᵈ⁾
      (suc. k) (Nat.degen (suc. k))
      (tSST.π (suc. (suc. k)) X) (X .s x)
  ]
]
