import PrincipalParts
import OverlapObstruction
import GeometricAlgebra

/-!
Instantiate the overlap-obstruction construction with the actual local
principal-part maps and lifts constructed from Laurent coefficients.
The remaining data are overlap differences and their geometric realization;
compactness enters explicitly as an invariant-kernel condition, not as an
assumed anti-invariant kernel isomorphism.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace Problem32.LaurentOverlap

open Problem32.LocalLaurent Problem32.PrincipalParts
open Problem32.OverlapObstruction Problem32.GeometricAlgebra

variable {I : Type*}

def familyPrincipalMap : (I → Series) →ₗ[ℂ] (I → negative) where
  toFun f i := ⟨principalPart (f i), principalPart_negative (f i)⟩
  map_add' f g := by funext i; apply Subtype.ext; exact principalPart.map_add _ _
  map_smul' c f := by funext i; apply Subtype.ext; exact principalPart.map_smul c _

def familyLift : (I → negative) →ₗ[ℂ] (I → Series) where
  toFun p i := (p i).val
  map_add' p q := rfl
  map_smul' c p := rfl

theorem familyLift_rightInverse (p : I → negative) :
    familyPrincipalMap (familyLift p) = p := by
  funext i
  apply Subtype.ext
  exact principalPart_eq_self (p i).val (p i).property

def familyDeck : (I → Series) →ₗ[ℂ] (I → Series) where
  toFun f i := deck (f i)
  map_add' f g := by funext i; exact deck.map_add _ _
  map_smul' c f := by funext i; exact deck.map_smul c _

theorem familyDeck_involutive (f : I → Series) : familyDeck (familyDeck f) = f := by
  funext i
  exact deck_involutive (f i)

def negativeDeck : negative →ₗ[ℂ] negative where
  toFun p := ⟨deck p.val, by
    intro n hn
    rw [deck_coeff, p.property n hn]
    split_ifs <;> simp⟩
  map_add' p q := by apply Subtype.ext; exact deck.map_add _ _
  map_smul' c p := by apply Subtype.ext; exact deck.map_smul c _

def familyPrincipalDeck : (I → negative) →ₗ[ℂ] (I → negative) where
  toFun p i := negativeDeck (p i)
  map_add' p q := by funext i; exact negativeDeck.map_add _ _
  map_smul' c p := by funext i; exact negativeDeck.map_smul c _

theorem familyPrincipalMap_deck (f : I → Series) :
    familyPrincipalMap (familyDeck f) = familyPrincipalDeck (familyPrincipalMap f) := by
  funext i
  apply Subtype.ext
  exact principalPart_deck (f i)

variable {C : Type*} [AddCommGroup C] [Module ℂ C]

abbrev laurentObstruction (D : (I → Series) →ₗ[ℂ] C) :=
  obstruction (V := I → Series) (P := I → negative) (C := C) (familyPrincipalMap (I := I)) D (familyLift (I := I))

/-- No local lift or exactness assumption is required: the lift was explicitly
constructed above from the principal part itself. -/
def laurentObstruction_kernel (D : (I → Series) →ₗ[ℂ] C) :=
  obstruction_kernel (V := I → Series) (P := I → negative) (C := C) (familyPrincipalMap (I := I)) D
    (familyLift (I := I)) (familyLift_rightInverse (I := I))

def compatibleDeck (D : (I → Series) →ₗ[ℂ] C) (u : C →ₗ[ℂ] C)
    (hD : ∀ f, D (familyDeck f) = u (D f)) : LinearMap.ker D →ₗ[ℂ] LinearMap.ker D where
  toFun f := ⟨familyDeck f.val, by
    change D (familyDeck f.val) = 0
    rw [hD, f.property, map_zero]⟩
  map_add' f g := by apply Subtype.ext; exact familyDeck.map_add _ _
  map_smul' c f := by apply Subtype.ext; exact familyDeck.map_smul c _

/-- Combine the computed obstruction exactness with the proved anti-part
lemma. The compact-geometric invariant-kernel condition is still explicit.
The involution here acts within each local Laurent chart; exchanged charts
and the global covering action must still be supplied in a geometric model. -/
def antiLaurentObstructionEquiv
    (D : (I → Series) →ₗ[ℂ] C) (u : C →ₗ[ℂ] C)
    (hD : ∀ f, D (familyDeck f) = u (D f))
    (hcompact : ∀ f : LinearMap.ker D,
      familyPrincipalMap f.val = 0 → familyDeck f.val = f.val) :
    ↥(antiSpace (V := LinearMap.ker D) (compatibleDeck D u hD)) ≃ₗ[ℂ]
      ↥(antiKernel (W := I → negative) (familyPrincipalDeck (I := I)) (laurentObstruction (I := I) D)) := by
  apply antiKernelEquiv (V := LinearMap.ker D) (W := I → negative) (compatibleDeck D u hD) familyPrincipalDeck
    (compatiblePrincipalMap (V := I → Series) (P := I → negative) (C := C) familyPrincipalMap D) (laurentObstruction (I := I) D)
  · intro f
    apply Subtype.ext
    exact familyDeck_involutive f.val
  · intro f
    exact familyPrincipalMap_deck f.val
  · exact (laurentObstruction_kernel (I := I) D).symm
  · intro f hf
    apply Subtype.ext
    exact hcompact f hf

#print axioms familyLift_rightInverse
#print axioms laurentObstruction_kernel
#print axioms antiLaurentObstructionEquiv

end Problem32.LaurentOverlap



