import LocalPrimitiveGluing
import GeometricAlgebra

noncomputable section
namespace Problem32.PaperDifferentialBridge
open Problem32.LocalLaurent Problem32.PrincipalParts Problem32.LocalPrimitiveGluing
open Problem32.GeometricAlgebra

theorem integrated_principal_derivative (f : Series) :
    primitive (principalPart (LaurentSeries.derivative ℂ f)) = principalPart f := by
  rw [principalPart_derivative]
  exact primitive_derivative _ (principalPart_negative f 0 (by omega))

theorem principal_integrated_derivative (f : Series) :
    principalPart (primitive (LaurentSeries.derivative ℂ f)) = principalPart f := by
  apply (primitive_recovers_principalPart _ _ (principalPart_negative f)).mp
  rw [derivative_primitive _ (derivative_residue_zero f), principalPart_derivative]

variable {V S P I : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]

/-- The global b(d f)=p(f) law follows from the local derivative identity
and the DEFINITIONS of the principal-coordinate maps. -/
theorem differentiated_principal_identity
    (d : V →ₗ[ℂ] S) (b : S →ₗ[ℂ] P) (p : V →ₗ[ℂ] P)
    (functionGerm : I → V →ₗ[ℂ] Series) (formGerm : I → S →ₗ[ℂ] Series)
    (coordinates : P →ₗ[ℂ] (I → Series)) (faithful : Function.Injective coordinates)
    (derivative_germ : ∀ f i, formGerm i (d f) = LaurentSeries.derivative ℂ (functionGerm i f))
    (b_definition : ∀ s i, coordinates (b s) i = primitive (principalPart (formGerm i s)))
    (p_definition : ∀ f i, coordinates (p f) i = principalPart (functionGerm i f)) :
    ∀ f, b (d f) = p f := by
  intro f
  apply faithful
  funext i
  rw [b_definition, p_definition, derivative_germ, integrated_principal_derivative]

/-- A primitive with prescribed principal part has the same pole bound,
provided the allowed function pole order is nonnegative. -/
theorem primitive_bound_from_principal (f p : Series) (k : ℤ) (hk : k ≤ 0)
    (hp : p ∈ negative) (hbound : p ∈ bounded k)
    (hderivative : principalPart (LaurentSeries.derivative ℂ f) = LaurentSeries.derivative ℂ p) :
    f ∈ bounded k := by
  have hpp := (primitive_recovers_principalPart f p hp).mp hderivative
  intro n hn
  have hn0 : n < 0 := lt_of_lt_of_le hn hk
  have heq := congrArg (fun s : Series => s.coeff n) hpp
  change (if n < 0 then f.coeff n else 0) = p.coeff n at heq
  rw [if_pos hn0] at heq
  rw [heq]
  exact hbound n hn

variable {C T : Type*} [AddCommGroup C] [Module ℂ C]
  [AddCommGroup T] [Module ℂ T]

/-- For an anti-invariant form, testing anti cycles suffices. This is the
linear algebra behind using only the anti-period coordinates. -/
theorem anti_cycles_determine_periods
    (formAction : S →ₗ[ℂ] S) (cycleAction : C →ₗ[ℂ] C)
    (hc : ∀ c, cycleAction (cycleAction c) = c)
    (pairing : S →ₗ[ℂ] C →ₗ[ℂ] T)
    (natural : ∀ f c, pairing (formAction f) c = pairing f (cycleAction c))
    (f : S) (hf : formAction f = -f)
    (zero_anti : ∀ c : antiSpace cycleAction, pairing f c.val = 0) :
    ∀ c, pairing f c = 0 := by
  intro c
  have hn : pairing f (cycleAction c) = -(pairing f c) := by
    rw [← natural, hf, map_neg]
    rfl
  have h := zero_anti (minusProjection cycleAction hc c)
  change pairing f ((2 : ℂ)⁻¹ • (c-cycleAction c)) = 0 at h
  rw [map_smul, map_sub, hn, sub_neg_eq_add, ← two_smul ℂ (pairing f c), smul_smul] at h
  simpa using h

#print axioms differentiated_principal_identity
#print axioms primitive_bound_from_principal
#print axioms anti_cycles_determine_periods
end Problem32.PaperDifferentialBridge
