import ChartCoverAction

/-! Differential coefficients carry the Jacobian sign under w ↦ -w.
These identities concern formal Laurent series; they do not supply convergence. -/
noncomputable section
namespace Problem32.ChartDifferential
open Problem32.LocalLaurent Problem32.ChartCoverAction

theorem derivative_deck (f : Series) :
    LaurentSeries.derivative ℂ (deck f) = -deck (LaurentSeries.derivative ℂ f) := by
  ext n
  rw [derivative_coeff, deck_coeff, HahnSeries.coeff_neg, deck_coeff, derivative_coeff]
  by_cases hn : n%2 = 0
  · have hs : (n+1)%2 ≠ 0 := by omega
    simp [hn, hs]
  · have hs : (n+1)%2 = 0 := by omega
    simp [hn, hs]

theorem primitive_neg_deck (f : Series) :
    primitive (-deck f) = deck (primitive f) := by
  ext n
  rw [primitive_coeff, HahnSeries.coeff_neg, deck_coeff, deck_coeff, primitive_coeff]
  by_cases hn : n%2 = 0
  · have hs : (n-1)%2 ≠ 0 := by omega
    simp [hn, hs]
  · have hs : (n-1)%2 = 0 := by omega
    simp [hn, hs, neg_div]

variable {I : Type*}

def formAction (a : ChartAction I) : (I → Series) →ₗ[ℂ] (I → Series) where
  toFun w i := if a.reflect i then -deck (w (a.exchange i)) else w (a.exchange i)
  map_add' w v := by
    funext i
    cases h : a.reflect i <;> simp [h, map_add, add_comm]
  map_smul' c w := by
    funext i
    cases h : a.reflect i <;> simp [h, map_smul, smul_neg]

theorem formAction_twice (a : ChartAction I) (w : I → Series) :
    formAction a (formAction a w) = w := by
  funext i
  change (if a.reflect i then -deck (if a.reflect (a.exchange i) then
    -deck (w (a.exchange (a.exchange i))) else w (a.exchange (a.exchange i)))
    else (if a.reflect (a.exchange i) then -deck (w (a.exchange (a.exchange i)))
    else w (a.exchange (a.exchange i)))) = w i
  rw [a.reflect_exchange, a.exchange_twice]
  cases a.reflect i <;> simp [map_neg, deck_involutive]

def differentiate : (I → Series) →ₗ[ℂ] (I → Series) where
  toFun f i := LaurentSeries.derivative ℂ (f i)
  map_add' f g := by funext i; exact (LaurentSeries.derivative ℂ).map_add _ _
  map_smul' c f := by funext i; exact (LaurentSeries.derivative ℂ).map_smul _ _

def primitiveFamily : (I → Series) →ₗ[ℂ] (I → Series) where
  toFun w i := primitive (w i)
  map_add' w v := by funext i; exact primitive.map_add _ _
  map_smul' c w := by funext i; exact primitive.map_smul _ _

theorem differentiate_equivariant (a : ChartAction I) (f : I → Series) :
    differentiate (action a f) = formAction a (differentiate f) := by
  funext i
  change LaurentSeries.derivative ℂ
    (if a.reflect i then deck (f (a.exchange i)) else f (a.exchange i)) =
    if a.reflect i then -deck (LaurentSeries.derivative ℂ (f (a.exchange i)))
    else LaurentSeries.derivative ℂ (f (a.exchange i))
  split
  · exact derivative_deck _
  · rfl

theorem primitive_equivariant (a : ChartAction I) (w : I → Series) :
    primitiveFamily (formAction a w) = action a (primitiveFamily w) := by
  funext i
  cases h : a.reflect i <;>
    simp [primitiveFamily, action, formAction, h, primitive_neg_deck]

theorem anti_primitive (a : ChartAction I) (w : I → Series)
    (hw : formAction a w = -w) :
    action a (primitiveFamily w) = -primitiveFamily w := by
  rw [← primitive_equivariant, hw, map_neg]

theorem anti_derivative (a : ChartAction I) (f : I → Series)
    (hf : action a f = -f) :
    formAction a (differentiate f) = -differentiate f := by
  rw [← differentiate_equivariant, hf, map_neg]

#print axioms derivative_deck
#print axioms primitive_neg_deck
#print axioms formAction_twice
#print axioms anti_primitive
#print axioms anti_derivative
end Problem32.ChartDifferential
