import LaurentOverlap
import CompactHolomorphic

/-! The compactness input is derived from genuine holomorphic constancy.
The faithful global realization and its holomorphicity criterion remain
explicit hypotheses; this is not yet a construction of the orientation cover. -/
noncomputable section
set_option maxHeartbeats 1600000

namespace Problem32.CompactBridge
open Problem32.LocalLaurent Problem32.PrincipalParts
open Problem32.LaurentOverlap Problem32.OverlapObstruction
open Problem32.GeometricAlgebra Problem32.CompactHolomorphic
open scoped Manifold

variable {I C M : Type*} [AddCommGroup C] [Module ℂ C]
  [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ, ℂ) 1 M] [CompactSpace M] [PreconnectedSpace M]

def compactAntiObstructionEquiv
    (D : (I → Series) →ₗ[ℂ] C) (u : C →ₗ[ℂ] C)
    (hD : ∀ f, D (familyDeck f) = u (D f))
    (evaluation : LinearMap.ker D →ₗ[ℂ] (M → ℂ))
    (hinj : Function.Injective evaluation) (tau : M → M)
    (hequiv : ∀ f x, evaluation (compatibleDeck D u hD f) x = evaluation f (tau x))
    (hhol : ∀ f : LinearMap.ker D, familyPrincipalMap f.val = 0 →
      MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (evaluation f)) :
    ↥(antiSpace (V := LinearMap.ker D) (compatibleDeck D u hD)) ≃ₗ[ℂ]
      ↥(antiKernel (W := I → negative) (familyPrincipalDeck (I := I)) (laurentObstruction (I := I) D)) := by
  apply antiLaurentObstructionEquiv (I := I) D u hD
  intro f hf
  have h := kernel_fixed_of_holomorphic (S := LinearMap.ker D) (P := I → negative) evaluation hinj (compatibleDeck D u hD)
    tau hequiv (compatiblePrincipalMap (V := I → Series) (P := I → negative) (C := C) familyPrincipalMap D)
    hhol f hf
  exact congrArg Subtype.val h

#print axioms compactAntiObstructionEquiv
end Problem32.CompactBridge

