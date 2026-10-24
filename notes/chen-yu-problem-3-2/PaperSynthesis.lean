import PaperComponentCriterion
import PaperObstructionGlobal

noncomputable section
namespace Problem32.PaperSynthesis
open Problem32.GeometricAlgebra Problem32.LocalLaurent
open Problem32.PaperOrientationLocal Problem32.PaperOrientationGlobal
open Problem32.PaperResidualGlobal Problem32.PaperComponentCriterion
open Problem32.PaperSignatureData
variable {F I X : Type*} [Field F] [Algebra ℂ F]

/-- The base meromorphic field, realized as invariant cover functions. -/
def invariantField (t : F ≃ₐ[ℂ] F) : IntermediateField ℂ F where
  carrier := {f | t f = f}
  zero_mem' := map_zero t
  one_mem' := map_one t
  add_mem' := by intro x y hx hy; change t (x+y) = x+y; rw [map_add, hx, hy]
  mul_mem' := by intro x y hx hy; change t (x*y) = x*y; rw [map_mul, hx, hy]
  algebraMap_mem' := by intro c; exact t.commutes c
  inv_mem' := by intro x hx; change t x⁻¹ = x⁻¹; rw [map_inv₀, hx]

def invariantCoefficientEquiv (t : F ≃ₐ[ℂ] F) :
    invariantField t ≃ₗ[ℂ] invariantSpace t.toLinearMap where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientSections (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind)
    (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series) : Submodule ℂ (invariantField t) :=
  (baseSections t kind germ).comap (invariantCoefficientEquiv t).toLinearMap

def coefficientSectionsEquiv (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind)
    (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series) :
    coefficientSections t kind germ ≃ₗ[ℂ] baseSections t kind germ :=
  Problem32.PaperLinearAssembly.restrictEquiv (invariantCoefficientEquiv t) _ _ (by intro x; rfl)

/-- Passage from local Laurent bounds to the divisor definition of H^0(K-D).
Only the ordinary valuation law and a covering of points are inputs. -/
theorem section_definition (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind)
    (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series)
    (A : DivisorTheory (invariantField t) X) (K D : Divisor X)
    (point : I → X) (covers : Function.Surjective point)
    (orders : ∀ i, baseOrder (kind i) = D (point i))
    (valuation : ∀ f : invariantField t, f ≠ 0 → ∀ i n,
      germ i (invariantCoefficientEquiv t f) ∈ bounded n ↔
        n ≤ tensorDivisor A K 1 f (point i)) :
    ∀ f : invariantField t, f ∈ coefficientSections t kind germ ↔
      f = 0 ∨ ∀ x, D x ≤ tensorDivisor A K 1 f x := by
  intro f
  by_cases hf : f = 0
  · subst f; simp
  · simp only [hf, false_or]
    constructor
    · intro h x
      obtain ⟨i, rfl⟩ := covers x
      have hi := (valuation f hf i (baseOrder (kind i))).mp (h i)
      rwa [orders] at hi
    · intro h i
      apply (valuation f hf i (baseOrder (kind i))).mpr
      rw [orders]
      exact h (point i)

variable (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w)
  (kind : I → ChartKind) (eval : I → Germ F)
  (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series)
  (reference : I → Series) (href : ∀ i, reference i ≠ 0)
  (hpull : ∀ i x, pullback (kind i) (germ i x) = (eval i).ring x.val * reference i)
  (homega : ∀ i, omegaLocal (kind i) = (eval i).ring w * reference i)

def coefficientOrientationEquiv :
    coefficientSections t kind germ ≃ₗ[ℂ] coverSections t kind eval :=
  (coefficientSectionsEquiv t kind germ).trans
    (theorem_3_2 t w hw htw kind eval germ reference href hpull homega)

include hw htw href hpull homega in
theorem orientation_positive_iff_residual
    [FiniteDimensional ℂ (coefficientSections t kind germ)]
    (A : DivisorTheory (invariantField t) X) (K D P : Divisor X)
    (point : I → X) (covers : Function.Surjective point)
    (orders : ∀ i, baseOrder (kind i) = D (point i))
    (valuation : ∀ f : invariantField t, f ≠ 0 → ∀ i n,
      germ i (invariantCoefficientEquiv t f) ∈ bounded n ↔
        n ≤ tensorDivisor A K 1 f (point i))
    (degree : Divisor X →+ ℤ) (g : ℤ) (q : invariantField t) (hq : q ≠ 0)
    (hD : Effective D) (hP : Effective P)
    (hqdiv : tensorDivisor A K 2 q = 3 • D-P) (hdegD : degree D = g)
    (canonical_degree : ∀ f : invariantField t, f ≠ 0 →
      degree (tensorDivisor A K 1 f) = 2*g-2) :
    0 < Module.finrank ℂ (coverSections t kind eval) ↔
      ResidualCubic A K D P degree g q := by
  rw [← (coefficientOrientationEquiv t w hw htw kind eval germ reference href hpull homega).finrank_eq]
  exact positive_iff_residual A K D P degree g q hq hD hP hqdiv hdegD
    canonical_degree (coefficientSections t kind germ)
    (section_definition t kind germ A K D point covers orders valuation)

include hw htw href hpull homega in
theorem complete_component_criterion
    [FiniteDimensional ℂ (coefficientSections t kind germ)]
    (A : DivisorTheory (invariantField t) X) (K D P : Divisor X)
    (point : I → X) (covers : Function.Surjective point)
    (orders : ∀ i, baseOrder (kind i) = D (point i))
    (valuation : ∀ f : invariantField t, f ≠ 0 → ∀ i n,
      germ i (invariantCoefficientEquiv t f) ∈ bounded n ↔
        n ≤ tensorDivisor A K 1 f (point i))
    (degree : Divisor X →+ ℤ) (signature : ExceptionalSignature)
    (q : invariantField t) (hq : q ≠ 0) (hD : Effective D) (hP : Effective P)
    (hqdiv : tensorDivisor A K 2 q = 3 • D-P)
    (signature_degree : degree D = divisorDegree signature)
    (canonical_degree : ∀ f : invariantField t, f ≠ 0 →
      degree (tensorDivisor A K 1 f) = 2*genus signature-2)
    (h0O : ℕ)
    (riemann_roch : (h0O : ℤ) - (Module.finrank ℂ (coefficientSections t kind germ) : ℤ) = 1)
    (nonhyperelliptic : Prop) (eligible : Eligible signature nonhyperelliptic)
    (component : Component)
    (chen_moeller : Eligible signature nonhyperelliptic →
      h0O = match component with | .regular => 1 | .irregular => 2) :
    (0 < Module.finrank ℂ (coverSections t kind eval) ↔
      ResidualCubic A K D P degree (genus signature) q) ∧
    (0 < Module.finrank ℂ (coverSections t kind eval) ↔ 2 ≤ h0O) ∧
    (0 < Module.finrank ℂ (coverSections t kind eval) ↔ component = .irregular) ∧
    (Module.finrank ℂ (coverSections t kind eval) = 0 ↔ component = .regular) := by
  rw [← (coefficientOrientationEquiv t w hw htw kind eval germ reference href hpull homega).finrank_eq]
  obtain ⟨hr, hrr, hi, hreg⟩ := Problem32.PaperComponentCriterion.theorem_5_3 A K D P
    degree signature q hq hD hP hqdiv signature_degree canonical_degree
    (coefficientSections t kind germ)
    (section_definition t kind germ A K D point covers orders valuation)
    h0O riemann_roch nonhyperelliptic eligible component chen_moeller
  exact ⟨hr.symm, hrr, hi, hreg⟩

#print axioms complete_component_criterion
#print axioms section_definition
#print axioms coefficientOrientationEquiv
#print axioms orientation_positive_iff_residual
end Problem32.PaperSynthesis
