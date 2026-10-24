import LocalLaurent

/-! Residual cubic identities for actual Laurent coefficients. These prove the
local regularity test and tensor-weight transformation, not existence of global
Abelian differentials or the degree of a geometric divisor. -/
noncomputable section
namespace Problem32.ResidualCubicLocal
open Problem32.LocalLaurent HahnSeries

theorem bounded_iff_order (f : Series) (hf : f ≠ 0) (k : ℤ) :
    f ∈ bounded k ↔ k ≤ f.order := by
  constructor
  · intro h
    by_contra hn
    have hz := h f.order (by omega)
    exact hf (coeff_order_eq_zero.mp hz)
  · intro h n hn
    exact coeff_eq_zero_of_lt_order (by omega)

theorem order_inverse (f : Series) (hf : f ≠ 0) : f⁻¹.order = -f.order := by
  have h := order_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, order_one] at h
  omega

theorem order_quotient (f g : Series) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f/g).order = f.order - g.order := by
  rw [div_eq_mul_inv, order_mul hf (inv_ne_zero hg), order_inverse g hg]
  rfl

def residual (eta q : Series) : Series := eta^3 / q

theorem residual_ne_zero (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0) :
    residual eta q ≠ 0 := div_ne_zero (pow_ne_zero 3 he) hq

theorem residual_order (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0) :
    (residual eta q).order = 3 * eta.order - q.order := by
  rw [residual, order_quotient _ _ (pow_ne_zero 3 he) hq, order_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

theorem recover_quadratic (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0) :
    eta^3 / residual eta q = q := by
  unfold residual
  field_simp

/-- The simple pole allowance is small enough that integrality forces the
same vanishing bound on eta as in the holomorphic case. -/
theorem residual_regular_iff (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0)
    (d p : ℤ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (horder : q.order = 3*d-p) :
    residual eta q ∈ bounded 0 ↔ eta ∈ bounded d := by
  rw [bounded_iff_order _ (residual_ne_zero eta q he hq), bounded_iff_order _ he,
    residual_order eta q he hq, horder]
  omega

theorem residual_divisor_identity (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0)
    (d p : ℤ) (horder : q.order = 3*d-p) :
    (residual eta q).order = 3*(eta.order-d)+p := by
  rw [residual_order eta q he hq, horder]
  ring

theorem effective_residual_order (eta q : Series) (he : eta ≠ 0) (hq : q ≠ 0)
    (d p : ℤ) (horder : q.order = 3*d-p) (heta : eta ∈ bounded d) :
    ∃ r : ℤ, 0 ≤ r ∧ eta.order = d+r ∧ (residual eta q).order = 3*r+p := by
  have hb := (bounded_iff_order eta he d).mp heta
  refine ⟨eta.order-d, by omega, by omega, ?_⟩
  exact residual_divisor_identity eta q he hq d p horder

/-- Weight one divided into weight two gives weight one for eta^3/q.
An actual analytic coordinate transition must still supply the Jacobian. -/
theorem residual_coordinate_weight (eta q j : Series) (hq : q ≠ 0) (hj : j ≠ 0) :
    residual (eta*j) (q*j^2) = residual eta q * j := by
  unfold residual
  field_simp

/-- Algebraic transition-law compatibility. J must eventually come from actual
analytic coordinate changes; no such geometric existence is assumed here. -/
def Compatible {I : Type*} (weight : ℕ) (J : I → I → Series) (f : I → Series) : Prop :=
  ∀ i j, f j = f i * J i j ^ weight

theorem residual_compatible {I : Type*} (J : I → I → Series)
    (eta q : I → Series) (hq : ∀ i, q i ≠ 0) (hJ : ∀ i j, J i j ≠ 0)
    (he : Compatible 1 J eta) (hquad : Compatible 2 J q) :
    Compatible 1 J (fun i => residual (eta i) (q i)) := by
  intro i j
  change residual (eta j) (q j) = residual (eta i) (q i) * J i j ^ 1
  have heij := he i j
  simp only [pow_one] at heij
  rw [heij, hquad i j, residual_coordinate_weight _ _ _ (hq i) (hJ i j), pow_one]

#print axioms bounded_iff_order
#print axioms residual_regular_iff
#print axioms recover_quadratic
#print axioms residual_coordinate_weight
#print axioms effective_residual_order
#print axioms residual_compatible
end Problem32.ResidualCubicLocal
