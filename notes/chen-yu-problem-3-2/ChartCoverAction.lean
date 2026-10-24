import LaurentOverlap
import CompactHolomorphic

/-! Formal local charts with an involution on their indices. Fixed charts may
carry w ↦ -w, while paired charts may be exchanged with unchanged coordinate.
These are formal local data, not a constructed compact analytic cover. -/
noncomputable section
namespace Problem32.ChartCoverAction
open Problem32.LocalLaurent Problem32.PrincipalParts Problem32.LaurentOverlap
open Problem32.GeometricAlgebra Problem32.OverlapObstruction

variable {I : Type*}

structure ChartAction (I : Type*) where
  exchange : I → I
  exchange_twice : Function.Involutive exchange
  reflect : I → Bool
  reflect_exchange : ∀ i, reflect (exchange i) = reflect i

def action (a : ChartAction I) : (I → Series) →ₗ[ℂ] (I → Series) where
  toFun f i := if a.reflect i then deck (f (a.exchange i)) else f (a.exchange i)
  map_add' f g := by funext i; cases h : a.reflect i <;> simp [h, map_add]
  map_smul' c f := by funext i; cases h : a.reflect i <;> simp [h, map_smul]

theorem action_twice (a : ChartAction I) (f : I → Series) :
    action a (action a f) = f := by
  funext i
  change (if a.reflect i then deck (if a.reflect (a.exchange i) then
    deck (f (a.exchange (a.exchange i))) else f (a.exchange (a.exchange i)))
    else (if a.reflect (a.exchange i) then deck (f (a.exchange (a.exchange i)))
    else f (a.exchange (a.exchange i)))) = f i
  rw [a.reflect_exchange, a.exchange_twice]
  cases a.reflect i <;> simp [deck_involutive]

def principalAction (a : ChartAction I) : (I → negative) →ₗ[ℂ] (I → negative) where
  toFun p i := if a.reflect i then negativeDeck (p (a.exchange i)) else p (a.exchange i)
  map_add' p q := by funext i; cases h : a.reflect i <;> simp [h, map_add]
  map_smul' c p := by funext i; cases h : a.reflect i <;> simp [h, map_smul]

theorem principal_equivariant (a : ChartAction I) (f : I → Series) :
    familyPrincipalMap (action a f) = principalAction a (familyPrincipalMap f) := by
  funext i
  apply Subtype.ext
  cases h : a.reflect i
  · simp [action, principalAction, familyPrincipalMap, h]
  · simpa [action, principalAction, familyPrincipalMap, h, negativeDeck] using
      principalPart_deck (f (a.exchange i))

/-- All charts fixed with reflection: the previously implemented ramified model. -/
def ramified : ChartAction I where
  exchange := id
  exchange_twice := fun _ => rfl
  reflect := fun _ => true
  reflect_exchange := fun _ => rfl

/-- Two charts over each index exchanged without changing the base coordinate. -/
def unramified : ChartAction (I × Bool) where
  exchange := fun i => (i.1, !i.2)
  exchange_twice := by intro i; cases i with | mk i b => cases b <;> rfl
  reflect := fun _ => false
  reflect_exchange := fun _ => rfl

theorem ramified_action (f : I → Series) : action ramified f = familyDeck f := rfl

theorem unramified_anti_iff (f : I × Bool → Series) :
    action unramified f = -f ↔ ∀ i, f (i, true) = -f (i, false) := by
  constructor
  · intro h i
    exact congrFun h (i, false)
  · intro h
    funext i
    rcases i with ⟨i, b⟩
    cases b
    · exact h i
    · change f (i, false) = -f (i, true)
      rw [h, neg_neg]

/-- Direct sum of ramified charts and pairs of unramified charts. -/
def mixed (R U : Type*) : ChartAction (R ⊕ (U × Bool)) where
  exchange := fun i => match i with
    | .inl r => .inl r
    | .inr (u, b) => .inr (u, !b)
  exchange_twice := by
    intro i
    rcases i with r | ⟨u, b⟩
    · rfl
    · cases b <;> rfl
  reflect := fun i => match i with | .inl _ => true | .inr _ => false
  reflect_exchange := by intro i; cases i <;> rfl

theorem mixed_anti_iff {R U : Type*} (f : R ⊕ (U × Bool) → Series) :
    action (mixed R U) f = -f ↔
      (∀ r, deck (f (.inl r)) = -f (.inl r)) ∧
      (∀ u, f (.inr (u, true)) = -f (.inr (u, false))) := by
  constructor
  · intro h
    exact ⟨fun r => congrFun h (.inl r), fun u => congrFun h (.inr (u, false))⟩
  · rintro ⟨hr, hu⟩
    funext i
    rcases i with r | ⟨u, b⟩
    · exact hr r
    · cases b
      · exact hu u
      · change f (.inr (u, false)) = -f (.inr (u, true))
        rw [hu, neg_neg]

variable {C : Type*} [AddCommGroup C] [Module ℂ C]

def compatibleAction (a : ChartAction I) (D : (I → Series) →ₗ[ℂ] C)
    (u : C →ₗ[ℂ] C) (hD : ∀ f, D (action a f) = u (D f)) :
    LinearMap.ker D →ₗ[ℂ] LinearMap.ker D where
  toFun f := ⟨action a f.val, by
    change D (action a f.val) = 0
    rw [hD, f.property, map_zero]⟩
  map_add' f g := by apply Subtype.ext; exact (action a).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (action a).map_smul _ _

def antiObstructionEquiv (a : ChartAction I) (D : (I → Series) →ₗ[ℂ] C)
    (u : C →ₗ[ℂ] C) (hD : ∀ f, D (action a f) = u (D f))
    (hfixed : ∀ f : LinearMap.ker D,
      familyPrincipalMap f.val = 0 → action a f.val = f.val) :
    antiSpace (V := LinearMap.ker D) (compatibleAction a D u hD) ≃ₗ[ℂ]
      antiKernel (W := I → negative) (principalAction a) (laurentObstruction (I := I) D) := by
  apply antiKernelEquiv (V := LinearMap.ker D) (W := I → negative)
    (compatibleAction a D u hD) (principalAction a)
    (compatiblePrincipalMap (V := I → Series) (P := I → negative) (C := C)
      (familyPrincipalMap (I := I)) D) (laurentObstruction (I := I) D)
  · intro f; apply Subtype.ext; exact action_twice a f.val
  · intro f; exact principal_equivariant a f.val
  · exact (laurentObstruction_kernel (I := I) D).symm
  · intro f hf; apply Subtype.ext; exact hfixed f hf

open scoped Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ, ℂ) 1 M] [CompactSpace M] [PreconnectedSpace M]

/-- Compactness discharges the invariant-kernel condition, provided a faithful
global realization and the zero-principal-part holomorphicity bridge exist. -/
def compactAntiObstructionEquiv (a : ChartAction I) (D : (I → Series) →ₗ[ℂ] C)
    (u : C →ₗ[ℂ] C) (hD : ∀ f, D (action a f) = u (D f))
    (evaluation : LinearMap.ker D →ₗ[ℂ] (M → ℂ))
    (hinj : Function.Injective evaluation) (tau : M → M)
    (hequiv : ∀ f x, evaluation (compatibleAction a D u hD f) x = evaluation f (tau x))
    (hhol : ∀ f : LinearMap.ker D, familyPrincipalMap f.val = 0 →
      MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (evaluation f)) :
    antiSpace (V := LinearMap.ker D) (compatibleAction a D u hD) ≃ₗ[ℂ]
      antiKernel (W := I → negative) (principalAction a) (laurentObstruction (I := I) D) := by
  apply antiObstructionEquiv a D u hD
  intro f hf
  have h := Problem32.CompactHolomorphic.kernel_fixed_of_holomorphic
    (S := LinearMap.ker D) (P := I → negative) evaluation hinj
    (compatibleAction a D u hD) tau hequiv
    (compatiblePrincipalMap (V := I → Series) (P := I → negative) (C := C)
      (familyPrincipalMap (I := I)) D) hhol f hf
  exact congrArg Subtype.val h

#print axioms action_twice
#print axioms principal_equivariant
#print axioms unramified_anti_iff
#print axioms compactAntiObstructionEquiv
end Problem32.ChartCoverAction
