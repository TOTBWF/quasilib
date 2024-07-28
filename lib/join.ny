import "prelude"
import "sst"

section SST :=
  import SST

  ` The join of two semi-simplicial types.
  def Join (A B : SST) : SST := [
  | .z ↦ A .z ⊎ B .z
  | .s ↦ [
    | inl. a ↦
      Join⁽ᵈ⁾
        A (A .s a)
        B (Id B)
    | inr. b ↦
      Join⁽ᵈ⁾
        A (Trivial A)
        B (B .s b)
    ]
  ]

  notation 5 Join : A "⋆" B := Join A B
end
