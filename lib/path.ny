` ----------------------------------------
` Charaterising path types
` ----------------------------------------
import "prelude"

` Paths in pairs are pairs of paths.
def Pair.path
  (A B : Type) (x y : A × B)
  (p : Path A (x .fst) (y .fst)) (q : Path B (x .snd) (y .snd))
  : Path (A × B) x y
  :=
    J₂ A
      (x1 y1 _ ↦ Path (A × B) (x1 , x .snd) (y1 , y .snd))
      (a ↦
        J₂ B
        (x2 y2 _ ↦ Path (A × B) (a , x2) (a , y2))
        (_ ↦ refl.)
        (x .snd) (y .snd) q)
      (x .fst) (y .fst) p

def Σ.path
  (A : Type) (B : A → Type)
  (x y : Σ A B)
  (p : Path A (x .fst) (y .fst)) (q : PathP A B (x .fst) (x .snd) (y .fst) (y .snd) p)
  : Path (Σ A B) x y :=
    J₂ A
      (x1 y1 p ↦ (x2 : B x1) (y2 : B y1) → PathP A B x1 x2 y1 y2 p → Path (Σ A B) (x1 , x2) (y1 , y2))
      (a ↦
        J₂ (B a)
        (x y _ ↦ Path (Σ A B) (a , x) (a , y))
        (_ ↦ refl.))
      (x .fst) (y .fst) p
      (x .snd) (y .snd) q

` Displayed paths in 'Gel' types are given by 'PathP's.
def Gel.path
  (A : Type) (B : A → Type)
  (a0 : A) (b0 : Gel A B a0)
  (a1 : A) (b1 : Gel A B a1)
  (p : Path A a0 a1) (q : PathP A B a0 (b0 .ungel) a1 (b1 .ungel) p)
  : Path⁽ᵈ⁾ A (Gel A B) a0 b0 a1 b1 p :=
match p [
| refl. ↦
  J (B a0) (b0 .ungel)
    (b1 _ ↦ Path⁽ᵈ⁾ A (Gel A B) a0 b0 a0 (ungel := b1) refl.)
    refl.
    (b1 .ungel)
    q
]
