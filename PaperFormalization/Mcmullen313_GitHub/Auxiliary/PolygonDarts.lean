
import SectorAngles

namespace McMullen313

/-!
# Polygon Darts and Vertex Cycles

This module models a finite collection of
combinatorial copies of one polygon.

Each dart is a pair:

  (copy index, oriented boundary-side index).

Boundary rotation moves to the next side.
An involution pairs the sides that are glued.

A state is encoded by its incoming side.
The vertex successor is:

  next = edgePair ∘ boundaryTurn.

This is a combinatorial model. Euclidean
side lengths, actual isometric edge gluings,
and geometric cone charts remain separate.
-/

/-! ## 1. Oriented polygon sides -/

abbrev PolygonDart (copies sides : Nat) :=
  Fin copies × Fin sides

theorem polygonDart_card
    (copies sides : Nat) :
    Fintype.card (PolygonDart copies sides) =
      copies * sides := by
  simp [PolygonDart]

/-! ## 2. Cyclic boundary rotation -/

def boundaryTurn
    (copies sides : Nat) :
    Equiv.Perm (PolygonDart copies sides) :=
  Equiv.prodCongr
    (Equiv.refl (Fin copies))
    (finRotate sides)

theorem boundaryTurn_apply
    {copies sides : Nat}
    (e : PolygonDart copies sides) :
    boundaryTurn copies sides e =
      (e.1, finRotate sides e.2) := by
  rfl

theorem boundaryTurn_bijective
    (copies sides : Nat) :
    Function.Bijective
      (boundaryTurn copies sides) :=
  (boundaryTurn copies sides).bijective

/-! ## 3. Polygon edge pairing -/

structure PolygonPairing
    (copies sides : Nat) where

  paired :
    Equiv.Perm (PolygonDart copies sides)

  paired_involutive :
    ∀ e, paired (paired e) = e

/-! ## 4. Vertex transition -/

def vertexStep
    {copies sides : Nat}
    (P : PolygonPairing copies sides) :
    Equiv.Perm (PolygonDart copies sides) :=
  (boundaryTurn copies sides).trans P.paired

theorem vertexStep_apply
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (e : PolygonDart copies sides) :
    vertexStep P e =
      P.paired
        (e.1, finRotate sides e.2) := by
  rfl

theorem vertexStep_bijective
    {copies sides : Nat}
    (P : PolygonPairing copies sides) :
    Function.Bijective (vertexStep P) :=
  (vertexStep P).bijective

/-!
## 5. Bridge to SectorState

The vertex coordinate of SectorState is
specialized to Fin 1.

Thus SectorState copies 1 sides is
equivalent to PolygonDart copies sides.
-/

def dartStateEquiv
    (copies sides : Nat) :
    PolygonDart copies sides ≃
      SectorState copies 1 sides where

  toFun := fun e =>
    ⟨e.1, 0, e.2⟩

  invFun := fun s =>
    (s.copy, s.side)

  left_inv := by
    intro e
    cases e
    rfl

  right_inv := by
    intro s
    cases s with
    | mk c v d =>
        have hv : v = (0 : Fin 1) :=
          Subsingleton.elim v 0
        cases hv
        rfl

/-! ## 6. Lifting a dart permutation -/

def liftDartPerm
    (copies sides : Nat)
    (e : Equiv.Perm
      (PolygonDart copies sides)) :
    Equiv.Perm
      (SectorState copies 1 sides) :=

  ((dartStateEquiv copies sides).symm.trans e).trans
    (dartStateEquiv copies sides)

theorem liftDartPerm_apply
    {copies sides : Nat}
    (e : Equiv.Perm
      (PolygonDart copies sides))
    (s : SectorState copies 1 sides) :

    liftDartPerm copies sides e s =
      dartStateEquiv copies sides
        (e ((dartStateEquiv copies sides).symm s)) := by
  rfl

theorem liftDartPerm_dart
    {copies sides : Nat}
    (e : Equiv.Perm
      (PolygonDart copies sides))
    (d : PolygonDart copies sides) :

    liftDartPerm copies sides e
      (dartStateEquiv copies sides d) =
    dartStateEquiv copies sides (e d) := by

  rw [liftDartPerm_apply]
  rw [Equiv.symm_apply_apply]

/-! ## 7. Lifting the edge-pairing involution -/

theorem liftPairing_involutive
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (s : SectorState copies 1 sides) :

    liftDartPerm copies sides P.paired
      (liftDartPerm copies sides P.paired s) =
    s := by

  change
    (dartStateEquiv copies sides)
      (P.paired
        ((dartStateEquiv copies sides).symm
          ((dartStateEquiv copies sides)
            (P.paired
              ((dartStateEquiv copies sides).symm s))))) =
      s

  simp only [
    Equiv.symm_apply_apply,
    P.paired_involutive,
    Equiv.apply_symm_apply
  ]

/-! ## 8. Constructing the existing gluing model -/

def polygonSectorGluing
    {copies sides : Nat}
    (P : PolygonPairing copies sides) :
    SectorGluing copies 1 sides where

  turn :=
    liftDartPerm copies sides
      (boundaryTurn copies sides)

  turn_bijective :=
    (liftDartPerm copies sides
      (boundaryTurn copies sides)).bijective

  across :=
    liftDartPerm copies sides P.paired

  across_involutive :=
    liftPairing_involutive P

/-! ## 9. Agreement of the two successors -/

theorem gluingNext_dart
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (d : PolygonDart copies sides) :

    gluingNext
      (polygonSectorGluing P)
      (dartStateEquiv copies sides d) =

    dartStateEquiv copies sides
      (vertexStep P d) := by

  change
    liftDartPerm copies sides P.paired
      (liftDartPerm copies sides
        (boundaryTurn copies sides)
        (dartStateEquiv copies sides d)) =
    dartStateEquiv copies sides
      (P.paired (boundaryTurn copies sides d))

  rw [liftDartPerm_dart]
  rw [liftDartPerm_dart]

/-! ## 10. The period of a polygon dart -/

noncomputable def polygonPeriod
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (d : PolygonDart copies sides) : Nat :=

  gluingPeriod
    (polygonSectorGluing P)
    (dartStateEquiv copies sides d)

theorem polygonPeriod_positive
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (d : PolygonDart copies sides) :
    0 < polygonPeriod P d := by

  exact
    gluingPeriod_positive
      (polygonSectorGluing P)
      (dartStateEquiv copies sides d)

theorem polygonPeriod_step
    {copies sides : Nat}
    (P : PolygonPairing copies sides)
    (d : PolygonDart copies sides) :

    polygonPeriod P (vertexStep P d) =
      polygonPeriod P d := by

  unfold polygonPeriod

  rw [← gluingNext_dart P d]

  exact
    gluingPeriod_invariant
      (polygonSectorGluing P)
      (dartStateEquiv copies sides d)

/-! ## 11. Polygon corner angles -/

structure AngledPolygonPairing
    (copies sides : Nat)
    extends PolygonPairing copies sides where

  cornerAngle :
    Fin sides → ℝ

  cornerAngle_pos :
    ∀ i, 0 < cornerAngle i

/-!
The state is labeled by its incoming edge.

If the incoming edge has index j, its
terminal corner has index finRotate sides j.
-/

def polygonAngledGluing
    {copies sides : Nat}
    (P : AngledPolygonPairing copies sides) :
    AngledGluing copies 1 sides where

  gluing :=
    polygonSectorGluing P.toPolygonPairing

  angle := fun s =>
    P.cornerAngle (finRotate sides s.side)

  angle_pos := by
    intro s
    exact P.cornerAngle_pos _

/-! ## 12. Total angle around a vertex cycle -/

noncomputable def polygonConeAngle
    {copies sides : Nat}
    (P : AngledPolygonPairing copies sides)
    (d : PolygonDart copies sides) : ℝ :=

  totalConeAngle
    (polygonAngledGluing P)
    (dartStateEquiv copies sides d)

theorem polygonConeAngle_positive
    {copies sides : Nat}
    (P : AngledPolygonPairing copies sides)
    (d : PolygonDart copies sides) :
    0 < polygonConeAngle P d := by

  exact
    totalConeAngle_positive
      (polygonAngledGluing P)
      (dartStateEquiv copies sides d)

theorem polygonConeAngle_step
    {copies sides : Nat}
    (P : AngledPolygonPairing copies sides)
    (d : PolygonDart copies sides) :

    polygonConeAngle P (vertexStep
      P.toPolygonPairing d) =
    polygonConeAngle P d := by

  unfold polygonConeAngle

  rw [← gluingNext_dart
    P.toPolygonPairing d]

  exact
    totalConeAngle_invariant
      (polygonAngledGluing P)
      (dartStateEquiv copies sides d)

end McMullen313
