` ----------------------------------------
` Semi-simplicial types.
` ----------------------------------------
import "prelude"

` The type of semi-simplicial types.
` Each `X : SST` has a type of `X .z : Type` zero-simplices,
` a displayed type of lines `X .s x : SST⁽ᵈ⁾ X` originating from `x`, and so on.
`
` Note that one should read the type `X .s x .z y` as a line in `X`
` from `x` to `y`.
def SST : Type :=
codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

` Slices in an SST `A` over a vertex `x`.
` Note that the definition of SSTs privledges coslicing
` over slicing; this means that we need to define the
` displayed SST of slices "by hand".
def Slice (A : SST) (x : A .z) : SST⁽ᵈ⁾ A :=
[
| .z ↦ Gel (A .z) (y ↦ A .s y .z x)
| .s ↦ y α ↦ sym (Slice⁽ᵈ⁾ A (A .s y) x (α .ungel))
]
