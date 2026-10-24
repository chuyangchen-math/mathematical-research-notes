import LocalLaurent

/-! All local cases used in Theorem 3.2, including regular points (r=0).
The quotient and its pole-bound equivalence are constructed, not postulated. -/
noncomputable section
namespace Problem32.PaperOrientationLocal
open Problem32.LocalLaurent HahnSeries

inductive ChartKind where
  | unramified (r : ℕ)
  | ramified (r : ℕ)
  | simplePole

def baseOrder : ChartKind → ℤ
  | .unramified r => 2*(r : ℤ)
  | .ramified r => 2*(r : ℤ)+1
  | .simplePole => 0

def coverOrder : ChartKind → ℤ
  | .unramified r => -(r : ℤ)
  | .ramified r => -(2*(r : ℤ)+1)
  | .simplePole => 0

def quotient : ChartKind → Series →ₗ[ℂ] Series
  | .unramified r => shift (-3*(r : ℤ))
  | .ramified r => ramifiedQuotient (2*(r : ℤ)+1)
  | .simplePole => doubleShift 1

def pullback : ChartKind → Series → Series
  | .unramified _ => id
  | .ramified _ => pullbackDifferential
  | .simplePole => pullbackDifferential

def omegaLocal : ChartKind → Series
  | .unramified r => single (3*(r : ℤ)) 1
  | .ramified r => ramifiedOmega (2*(r : ℤ)+1)
  | .simplePole => single 0 2

theorem omegaLocal_ne_zero (c : ChartKind) : omegaLocal c ≠ 0 := by
  cases c with
  | unramified r => exact single_ne_zero (by norm_num)
  | ramified r => exact single_ne_zero (by norm_num)
  | simplePole => exact single_ne_zero (by norm_num)

theorem quotient_mul_omega (c : ChartKind) (f : Series) :
    quotient c f * omegaLocal c = pullback c f := by
  cases c with
  | unramified r =>
    have h := shift_shift_neg (3*(r : ℤ)) f
    change single (3*(r : ℤ)) 1 * (single (-(3*(r : ℤ))) 1 * f) = f at h
    change (single (-3*(r : ℤ)) 1 * f) * single (3*(r : ℤ)) 1 = f
    convert (mul_comm _ _).trans h using 1 <;> congr 2 <;> ring
  | ramified r => exact ramifiedQuotient_mul_omega (2*(r : ℤ)+1) f
  | simplePole =>
    change doubleShift 1 f * single 0 2 = (2 : ℂ) • doubleShift 1 f
    ext n
    simp [coeff_mul_single, coeff_smul, smul_eq_mul, mul_comm]

theorem quotient_eq_div (c : ChartKind) (f : Series) :
    quotient c f = pullback c f / omegaLocal c :=
  (eq_div_iff (omegaLocal_ne_zero c)).mpr (quotient_mul_omega c f)

theorem quotient_bound_iff (c : ChartKind) (f : Series) :
    quotient c f ∈ bounded (coverOrder c) ↔ f ∈ bounded (baseOrder c) := by
  cases c with
  | unramified r =>
    change shift (-3*(r : ℤ)) f ∈ bounded (-(r : ℤ)) ↔ f ∈ bounded (2*(r : ℤ))
    constructor
    · intro h
      have hb := shift_bounded (-(r : ℤ)) (3*(r : ℤ)) _ h
      have hi : shift (3*(r : ℤ)) (shift (-3*(r : ℤ)) f) = f := by
        convert shift_shift_neg (3*(r : ℤ)) f using 1 <;> congr 2 <;> ring
      rw [hi] at hb
      convert hb using 1 <;> congr 1 <;> ring
    · intro h
      have hb := shift_bounded (2*(r : ℤ)) (-3*(r : ℤ)) f h
      convert hb using 1 <;> congr 1 <;> ring
  | ramified r =>
    constructor
    · intro h
      have hb := ramifiedQuotient_descent_bound (2*(r : ℤ)+1) _ h
      simpa only [quotient, ramifiedQuotient, descend_doubleShift, baseOrder] using hb
    · exact ramifiedQuotient_pole_bound (2*(r : ℤ)+1) f
  | simplePole =>
    constructor
    · intro h
      have hb := odd_holomorphic_vanishes (doubleShift 1 f) (doubleShift_parity 1 f) h
      have hd := descend_bounded 0 1 (doubleShift 1 f) (by simpa using hb)
      simpa only [descend_doubleShift, baseOrder] using hd
    · intro h
      exact (simplePoleSectionEquiv ⟨f, h⟩).property.2

/-- Generic germ evaluation law: pullback of a differential has a reference
coefficient v, and omega has coefficient eval(w)*v. The quotient law follows
algebraically from these ordinary coordinate rules. -/
theorem germ_quotient {F : Type*} [Field F] (eval : F →+* Series)
    (c : ChartKind) (x w : F) (v f : Series) (hv : v ≠ 0)
    (hx : pullback c f = eval x * v) (hw : omegaLocal c = eval w * v) :
    eval (x/w) = quotient c f := by
  rw [map_div₀, quotient_eq_div, hx, hw]
  exact (mul_div_mul_right (eval x) (eval w) hv).symm

#print axioms quotient_eq_div
#print axioms quotient_bound_iff
#print axioms germ_quotient
end Problem32.PaperOrientationLocal
