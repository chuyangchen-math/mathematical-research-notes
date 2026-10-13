
import SectorCycle

namespace McMullen313

/-!
# Sector Gluing and Cycle Structure

This module constructs a sector transition from
two elementary operations:

1. turn:   a bijective local sector transition;
2. across: an involution pairing sectors across edges.

The resulting successor is

    next = across ∘ turn.

The module proves that this successor is bijective
and therefore inherits the minimal-period theory
from SectorCycle.
-/

/-! ## 1. Combinatorial gluing data -/

structure SectorGluing (n m k : Nat) where

  turn :
    SectorState n m k →
    SectorState n m k

  turn_bijective :
    Function.Bijective turn

  across :
    SectorState n m k →
    SectorState n m k

  across_involutive :
    ∀ s, across (across s) = s

/-! ## 2. The edge-pairing involution -/

theorem across_injective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Injective G.across := by

  intro x y h

  calc
    x = G.across (G.across x) :=
      (G.across_involutive x).symm

    _ = G.across (G.across y) :=
      congrArg G.across h

    _ = y :=
      G.across_involutive y

theorem across_surjective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Surjective G.across := by

  intro y

  refine ⟨G.across y, ?_⟩

  exact G.across_involutive y

theorem across_bijective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Bijective G.across := by

  exact
    ⟨across_injective G,
     across_surjective G⟩

/-! ## 3. The complete gluing transition -/

def gluingNext
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) :
    SectorState n m k :=
  G.across (G.turn s)

/-! ## 4. Injectivity of the transition -/

theorem gluingNext_injective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Injective (gluingNext G) := by

  intro x y h

  apply G.turn_bijective.1

  apply across_injective G

  exact h

/-! ## 5. Surjectivity of the transition -/

theorem gluingNext_surjective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Surjective (gluingNext G) := by

  intro y

  obtain ⟨x, hx⟩ :=
    G.turn_bijective.2 (G.across y)

  refine ⟨x, ?_⟩

  change G.across (G.turn x) = y

  rw [hx]

  exact G.across_involutive y

/-! ## 6. The gluing transition is a permutation -/

theorem gluingNext_bijective
    {n m k : Nat}
    (G : SectorGluing n m k) :
    Function.Bijective (gluingNext G) := by

  exact
    ⟨gluingNext_injective G,
     gluingNext_surjective G⟩

/-! ## 7. Constructing the sector system -/

def asSectorSystem
    {n m k : Nat}
    (G : SectorGluing n m k) :
    SectorSystem n m k where

  next :=
    gluingNext G

  next_bijective :=
    gluingNext_bijective G

theorem asSectorSystem_next
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) :
    (asSectorSystem G).next s =
      G.across (G.turn s) := by
  rfl

/-! ## 8. The period induced by the gluing -/

noncomputable def gluingPeriod
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) : Nat :=
  sectorPeriod (asSectorSystem G) s

theorem gluingPeriod_positive
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) :
    0 < gluingPeriod G s := by

  exact
    sectorPeriod_positive (asSectorSystem G) s

/-! ## 9. The gluing cycle closes -/

theorem gluingPeriod_return
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) :
    iterate (asSectorSystem G)
      (gluingPeriod G s) s = s := by

  exact
    iterate_sectorPeriod (asSectorSystem G) s

/-! ## 10. Minimality of the gluing period -/

theorem gluingPeriod_minimal
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k)
    (r : Nat)
    (hr : IsReturn (asSectorSystem G) s r) :
    gluingPeriod G s ≤ r := by

  exact
    sectorPeriod_minimal (asSectorSystem G) s r hr

theorem gluingPeriod_no_earlier_return
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k)
    (r : Nat)
    (hr : r < gluingPeriod G s) :
    ¬ IsReturn (asSectorSystem G) s r := by

  exact
    sectorPeriod_no_earlier_return
      (asSectorSystem G) s r hr

/-! ## 11. Invariance under gluing -/

theorem gluingPeriod_invariant
    {n m k : Nat}
    (G : SectorGluing n m k)
    (s : SectorState n m k) :
    gluingPeriod G (gluingNext G s) =
      gluingPeriod G s := by

  exact
    sectorPeriod_invariant
      (asSectorSystem G) s

/-! ## 12. Numerical cone angle for uniform sectors -/

/-
  For a cycle whose sectors all have the same
  corner angle, the total angle is the period
  multiplied by that angle.

  This definition is not yet a construction
  of a geometric cone chart.
-/

noncomputable def uniformConeAngle
    {n m k : Nat}
    (G : SectorGluing n m k)
    (angle : Real)
    (s : SectorState n m k) : Real :=
  (gluingPeriod G s : Real) * angle

theorem uniformConeAngle_invariant
    {n m k : Nat}
    (G : SectorGluing n m k)
    (angle : Real)
    (s : SectorState n m k) :
    uniformConeAngle G angle (gluingNext G s) =
      uniformConeAngle G angle s := by

  unfold uniformConeAngle

  rw [gluingPeriod_invariant]

end McMullen313
