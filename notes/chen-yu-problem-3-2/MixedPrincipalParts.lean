import AntiPrincipalParts
import GeometricAlgebra

/-! Finite principal-part spaces with both ramified points and exchanged pairs.
The bounds are supplied; their relation to a geometric divisor is not asserted. -/
noncomputable section
namespace Problem32.MixedPrincipalParts
open Problem32.PrincipalParts Problem32.AntiPrincipalParts
instance swappedAnti_group (m : ℕ) : AddCommGroup (swappedAnti m) :=
  Submodule.addCommGroup (R := ℂ) (M := finiteParts m × finiteParts m) (swappedAnti m)

instance finiteParts_finite (m : ℕ) : FiniteDimensional ℂ (finiteParts m) :=
  FiniteDimensional.of_injective (finitePartsEquiv m).symm.toLinearMap
    (finitePartsEquiv m).symm.injective

instance swappedAnti_finite (m : ℕ) : FiniteDimensional ℂ (swappedAnti m) :=
  FiniteDimensional.of_injective (V := swappedAnti m) (V₂ := finiteParts m)
    (swappedAntiEquiv m).symm.toLinearMap
    (swappedAntiEquiv m).symm.injective

variable {R U : Type*} [Fintype R] [Fintype U]

/-- An actual product of the previously constructed local subspaces. -/
abbrev Space (r : R → ℕ) (u : U → ℕ) :=
  ((i : R) → antiFiniteParts (r i)) × ((j : U) → swappedAnti (u j))

theorem totalUnramified_finrank (u : U → ℕ) :
    Module.finrank ℂ ((j : U) → swappedAnti (u j)) = ∑ j, u j := by
  letI : ∀ j : U, Module.Free ℂ (swappedAnti (u j)) :=
    fun j => Module.Free.of_divisionRing ℂ (swappedAnti (u j))
  letI : ∀ j : U, Module.Finite ℂ (swappedAnti (u j)) := fun j => inferInstance
  rw [Module.finrank_pi_fintype]
  simp only [swappedAnti_finrank]

theorem mixed_finrank (r : R → ℕ) (u : U → ℕ) :
    Module.finrank ℂ (Space r u) = (∑ i, (r i + 1)/2) + ∑ j, u j := by
  letI : Module.Free ℂ ((i : R) → antiFiniteParts (r i)) :=
    Module.Free.of_divisionRing ℂ ((i : R) → antiFiniteParts (r i))
  letI : Module.Free ℂ ((j : U) → swappedAnti (u j)) :=
    Module.Free.of_divisionRing ℂ ((j : U) → swappedAnti (u j))
  change Module.finrank ℂ
    (((i : R) → antiFiniteParts (r i)) × ((j : U) → swappedAnti (u j))) = _
  rw [Module.finrank_prod, totalRamified_finrank, totalUnramified_finrank]

/-- Rank-nullity for any actual linear obstruction on this mixed local space.
No numerical rank-nullity identity is assumed as an input. -/
def obstruction_rank_nullity {H : Type*} [AddCommGroup H] [Module ℂ H]
    (r : R → ℕ) (u : U → ℕ) (d : Space r u →ₗ[ℂ] H) :=
  Problem32.GeometricAlgebra.rank_nullity (V := Space r u) (W := H) d

#print axioms mixed_finrank
#print axioms obstruction_rank_nullity
end Problem32.MixedPrincipalParts
