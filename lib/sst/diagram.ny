import "../prelude"
import "../sst"

def Diagram : Type :=
codata [
| D .z : SST
| D .s : D .z .z → Diagram⁽ᵈ⁾ D
]

` The opposite of a diagram.
def Diagram.Op (D : Diagram) : Diagram :=
[
| .z ↦ SST.Op (D .z)
| .s ↦ x ↦ Diagram.Op⁽ᵈ⁾ D (D .s x)
]

` The diagram of coslices.
def Coslices (A : SST) : Diagram :=
[
| .z ↦ A
| .s ↦ x ↦ Coslices⁽ᵈ⁾ A (A .s x)
]

quit
` ----------------------------------------
` Example: Fibrewise opposites and coslices
` ----------------------------------------
`
` The type `Diagram.Op (Coslices A)` is quite interesting,
` as it lets us slice in the "normal"

axiom A : SST

axiom x : A .z
axiom y : A .z
axiom z : A .z
axiom α : A .s x .z y
axiom β : A .s x .z z
axiom γ : A .s z .z y

axiom 𝒻 : A .s x .s z β .z y α γ

` Edges are flipped in the diagram
def example1 : Diagram.Op (Coslices A) .z .s y .z x := (ungel := α)

` Edges are not flipped while we slice though!
def example2 : Diagram.Op (Coslices A) .s x .z .s y α .z z β (ungel := γ) := (ungel := 𝒻)
