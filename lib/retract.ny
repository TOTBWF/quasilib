` ----------------------------------------
` Retracts of types
` ----------------------------------------
import "prelude"

def Retraction (A B : Type) : Type :=
  sig (retr : A → B, sect : B → A, invl : (x : B) → Path B (retr (sect x)) x)

def Retraction.id (A : Type) : Retraction A A :=
  (retr := x ↦ x, sect := x ↦ x, invl := _ ↦ refl.)

` Retracts of types lift to retracts of path types.
def Path.retract
  (A B : Type) (x y : B)
  (f : Retraction A B)
  : Retraction (Path A (f .sect x) (f .sect y)) (Path B x y) :=
( retr := p ↦
  Path.trans B x (f .retr (f .sect x)) y
    (Path.sym B x (f .retr (f .sect x)) (f .invl x))
    (Path.trans B (f .retr (f .sect x)) (f .retr (f .sect y)) y
      (cong A B (f .retr) (f .sect x) (f .sect y) p)
      (f .invl y))
, sect := cong B A (f .sect) x y
, invl := p ↦
  match p [
  | refl. ↦
    J B (f .retr (f .sect x))
      (y p ↦
        Path (Path B y y)
          (Path.trans B y (f .retr (f .sect x)) y
            (Path.sym B y (f .retr (f .sect x)) p)
            (Path.trans B (f .retr (f .sect x)) (f .retr (f .sect x)) y
              refl.
              p))
          refl.
        )
      refl.
      x
      (f .invl x)
  ]
)
