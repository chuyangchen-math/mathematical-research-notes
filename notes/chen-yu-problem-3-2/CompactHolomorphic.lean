import Mathlib.Geometry.Manifold.Complex
import Mathlib.Tactic

/-!
The genuine compact-complex-manifold step: holomorphic functions are constant,
and hence anti-invariant holomorphic functions vanish. This uses Mathlib's
proved maximum-modulus/compactness theorem, not a constancy axiom.
The quadratic-differential orientation cover still has to be constructed as
such a manifold, and the zero-principal-part/holomorphic bridge is still needed.
-/

namespace Problem32.CompactHolomorphic

open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ, ℂ) 1 M] [CompactSpace M] [PreconnectedSpace M]

theorem holomorphic_fixed_under_map (f : M → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f) (tau : M → M) :
    ∀ x, f (tau x) = f x := by
  intro x
  exact hf.apply_eq_of_compactSpace (tau x) x

/-- This applies in particular to the deck transformation of a connected
compact orientation cover, once that geometric object is supplied. -/
theorem anti_holomorphic_eq_zero (f : M → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f) (tau : M → M)
    (hanti : ∀ x, f (tau x) = -f x) : f = 0 := by
  funext x
  have hc := holomorphic_fixed_under_map f hf tau x
  have ha := hanti x
  change f x = 0
  linear_combination (1/2 : ℂ) * (ha - hc)

variable {S P : Type*} [AddCommGroup S] [Module ℂ S]
  [AddCommGroup P] [Module ℂ P]

/-- Discharge invariant-kernel conditions from a faithful realization by
global functions whose zero-principal-part elements are holomorphic.
The representation and holomorphicity bridge are explicit remaining data. -/
theorem kernel_fixed_of_holomorphic
    (evaluation : S →ₗ[ℂ] (M → ℂ)) (hinj : Function.Injective evaluation)
    (action : S →ₗ[ℂ] S) (tau : M → M)
    (hequiv : ∀ s x, evaluation (action s) x = evaluation s (tau x))
    (q : S →ₗ[ℂ] P)
    (hhol : ∀ s, q s = 0 → MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (evaluation s)) :
    ∀ s, q s = 0 → action s = s := by
  intro s hs
  apply hinj
  funext x
  rw [hequiv]
  exact holomorphic_fixed_under_map (evaluation s) (hhol s hs) tau x

#print axioms anti_holomorphic_eq_zero
#print axioms kernel_fixed_of_holomorphic

end Problem32.CompactHolomorphic
