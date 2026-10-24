import Mathlib

/-! Lemma 5.2 relative to ordinary meromorphic divisor calculus.
Fix a meromorphic reference one-form with divisor K; a weight-k differential
is represented by a nonzero function-field coefficient f, with divisor
principal(f) + k K. No residual-cubic equivalence is assumed. -/
noncomputable section
namespace Problem32.PaperResidualGlobal

variable {F X : Type*} [Field F]
abbrev Divisor (X : Type*) := X →₀ ℤ

/-- External standard divisor laws for nonzero meromorphic functions. -/
structure DivisorTheory (F X : Type*) [Field F] where
  principal : F → Divisor X
  mul : ∀ f g, f ≠ 0 → g ≠ 0 → principal (f*g) = principal f + principal g
  inv : ∀ f, f ≠ 0 → principal f⁻¹ = -principal f

def tensorDivisor (A : DivisorTheory F X) (K : Divisor X) (weight : ℤ) (f : F) : Divisor X :=
  A.principal f + weight • K

def Effective (D : Divisor X) : Prop := ∀ x, 0 ≤ D x
def Holomorphic (A : DivisorTheory F X) (K : Divisor X) (f : F) : Prop :=
  Effective (tensorDivisor A K 1 f)

theorem cube_divisor (A : DivisorTheory F X) (f : F) (hf : f ≠ 0) :
    A.principal (f^3) = 3 • A.principal f := by
  rw [show f^3 = (f*f)*f by ring, A.mul _ _ (mul_ne_zero hf hf) hf, A.mul _ _ hf hf]
  abel

theorem quotient_divisor (A : DivisorTheory F X) (f g : F) (hf : f ≠ 0) (hg : g ≠ 0) :
    A.principal (f/g) = A.principal f - A.principal g := by
  rw [div_eq_mul_inv, A.mul _ _ hf (inv_ne_zero hg), A.inv _ hg, sub_eq_add_neg]

theorem cubic_tensor_divisor (A : DivisorTheory F X) (K : Divisor X)
    (eta q : F) (he : eta ≠ 0) (hq : q ≠ 0) :
    tensorDivisor A K 1 (eta^3/q) = 3 • tensorDivisor A K 1 eta - tensorDivisor A K 2 q := by
  rw [tensorDivisor, quotient_divisor A _ _ (pow_ne_zero 3 he) hq, cube_divisor A eta he]
  simp only [tensorDivisor, one_smul]
  module

/-- The effective residual divisor is constructed as div(eta)-D. -/
def residualDivisor (A : DivisorTheory F X) (K D : Divisor X) (eta : F) : Divisor X :=
  tensorDivisor A K 1 eta - D

theorem residual_data (A : DivisorTheory F X) (K D P : Divisor X)
    (eta q : F) (he : eta ≠ 0) (hq : q ≠ 0)
    (hbound : ∀ x, D x ≤ tensorDivisor A K 1 eta x)
    (hqdiv : tensorDivisor A K 2 q = 3 • D - P) :
    Effective (residualDivisor A K D eta) ∧
      tensorDivisor A K 1 eta = D + residualDivisor A K D eta ∧
      tensorDivisor A K 1 (eta^3/q) = 3 • residualDivisor A K D eta + P := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change 0 ≤ tensorDivisor A K 1 eta x - D x
    exact sub_nonneg.mpr (hbound x)
  · unfold residualDivisor
    abel
  · rw [cubic_tensor_divisor A K eta q he hq, hqdiv]
    unfold residualDivisor
    module

/-- Converse at simple poles: integrality, not a fractional bound, forces
the required vanishing of eta. This is the internal converse argument. -/
theorem bound_of_holomorphic_quotient (A : DivisorTheory F X) (K D P : Divisor X)
    (eta q : F) (he : eta ≠ 0) (hq : q ≠ 0)
    (hp : ∀ x, 0 ≤ P x ∧ P x ≤ 1)
    (hqdiv : tensorDivisor A K 2 q = 3 • D - P)
    (htheta : Holomorphic A K (eta^3/q)) :
    ∀ x, D x ≤ tensorDivisor A K 1 eta x := by
  intro x
  have h := htheta x
  change 0 ≤ tensorDivisor A K 1 (eta^3/q) x at h
  rw [cubic_tensor_divisor A K eta q he hq, hqdiv] at h
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
  have hp' := hp x
  omega

def ResidualCubic (A : DivisorTheory F X) (K D P : Divisor X)
    (degree : Divisor X →+ ℤ) (g : ℤ) (q : F) : Prop :=
  ∃ eta theta : F, ∃ R : Divisor X,
    eta ≠ 0 ∧ theta ≠ 0 ∧ Holomorphic A K eta ∧ Holomorphic A K theta ∧
    Effective R ∧ degree R = g-2 ∧
    tensorDivisor A K 1 eta = D+R ∧
    tensorDivisor A K 1 theta = 3 • R+P ∧ q = eta^3/theta

/-- Lemma 5.2. The only theorem-level geometric input is the standard degree
of the divisor of a nonzero meromorphic one-form. deg(D)=g is signature data. -/
theorem lemma_5_2 (A : DivisorTheory F X) (K D P : Divisor X)
    (degree : Divisor X →+ ℤ) (g : ℤ) (q : F) (hq : q ≠ 0)
    (hD : Effective D) (hP : Effective P)
    (hqdiv : tensorDivisor A K 2 q = 3 • D-P)
    (hdegD : degree D = g)
    (canonical_degree : ∀ f : F, f ≠ 0 → degree (tensorDivisor A K 1 f) = 2*g-2) :
    (∃ eta : F, eta ≠ 0 ∧ ∀ x, D x ≤ tensorDivisor A K 1 eta x) ↔
      ResidualCubic A K D P degree g q := by
  constructor
  · rintro ⟨eta, he, hb⟩
    obtain ⟨hR, hediv, htdiv⟩ := residual_data A K D P eta q he hq hb hqdiv
    refine ⟨eta, eta^3/q, residualDivisor A K D eta, he,
      div_ne_zero (pow_ne_zero 3 he) hq, ?_, ?_, hR, ?_, hediv, htdiv, ?_⟩
    · intro x
      exact le_trans (hD x) (hb x)
    · intro x
      change 0 ≤ tensorDivisor A K 1 (eta^3/q) x
      rw [htdiv]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
      have hr := hR x
      have hp := hP x
      omega
    · unfold residualDivisor
      rw [map_sub, canonical_degree eta he, hdegD]
      omega
    · field_simp
  · rintro ⟨eta, theta, R, he, _, _, _, hR, _, hediv, _, _⟩
    refine ⟨eta, he, ?_⟩
    intro x
    rw [hediv, Finsupp.add_apply]
    exact le_add_of_nonneg_right (hR x)

#print axioms cubic_tensor_divisor
#print axioms bound_of_holomorphic_quotient
#print axioms lemma_5_2
end Problem32.PaperResidualGlobal
