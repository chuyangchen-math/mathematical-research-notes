import PaperOrientationLocal
import GeometricAlgebra

/-! Theorem 3.2 in a meromorphic coordinate interface. Standard external
geometry provides the function field of the connected double cover, invariant
descent, faithful germs, and the canonical local normal forms. The required
bounded-section equivalence is PROVED, not one of those interface fields. -/
noncomputable section
namespace Problem32.PaperOrientationGlobal
open Problem32.LocalLaurent Problem32.GeometricAlgebra Problem32.PaperOrientationLocal

variable {F I : Type*} [Field F] [Algebra ℂ F]

/-- A complex-linear Laurent germ, with the coefficientwise scalar action
used by the local modules. These are the ordinary algebraic evaluation laws. -/
structure Germ (F : Type*) [Field F] [Algebra ℂ F] where
  ring : F →+* Series
  scalar : ∀ (c : ℂ) (x : F), ring (c • x) = c • ring x

def baseSections (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind)
    (germ : ∀ i : I, invariantSpace t.toLinearMap →ₗ[ℂ] Series) :
    Submodule ℂ (invariantSpace t.toLinearMap) where
  carrier := {x | ∀ i, germ i x ∈ bounded (baseOrder (kind i))}
  zero_mem' := by intro i; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by intro x y hx hy i; rw [map_add]; exact (bounded _).add_mem (hx i) (hy i)
  smul_mem' := by intro c x hx i; rw [map_smul]; exact (bounded _).smul_mem c (hx i)

def coverSections (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind) (eval : I → Germ F) :
    Submodule ℂ (antiSpace t.toLinearMap) where
  carrier := {f | ∀ i, (eval i).ring f.val ∈ bounded (coverOrder (kind i))}
  zero_mem' := by intro i; change (eval i).ring 0 ∈ _; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by
    intro f g hf hg i
    change (eval i).ring (f.val+g.val) ∈ _
    rw [map_add]
    exact (bounded _).add_mem (hf i) (hg i)
  smul_mem' := by
    intro c f hf i
    change (eval i).ring (c • f.val) ∈ _
    rw [(eval i).scalar]
    exact (bounded _).smul_mem c (hf i)

variable (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w)
  (kind : I → ChartKind) (eval : I → Germ F)
  (germ : ∀ i : I, invariantSpace t.toLinearMap →ₗ[ℂ] Series)
  (reference : I → Series) (href : ∀ i, reference i ≠ 0)
  (hpull : ∀ i x, pullback (kind i) (germ i x) = (eval i).ring x.val * reference i)
  (homega : ∀ i, omegaLocal (kind i) = (eval i).ring w * reference i)

include hw htw href hpull homega

theorem quotient_membership (x : invariantSpace t.toLinearMap) :
    divideByAntiEquiv t w hw htw x ∈ coverSections t kind eval ↔
      x ∈ baseSections t kind germ := by
  constructor
  · intro h i
    apply (quotient_bound_iff (kind i) (germ i x)).mp
    have hi := h i
    change (eval i).ring (x.val/w) ∈ bounded (coverOrder (kind i)) at hi
    rw [germ_quotient (eval i).ring (kind i) x.val w (reference i) (germ i x)
      (href i) (hpull i x) (homega i)] at hi
    exact hi
  · intro h i
    change (eval i).ring (x.val/w) ∈ bounded (coverOrder (kind i))
    rw [germ_quotient (eval i).ring (kind i) x.val w (reference i) (germ i x)
      (href i) (hpull i x) (homega i)]
    exact (quotient_bound_iff (kind i) (germ i x)).mpr (h i)

/-- The actual map is division by omega, and the inverse is multiplication.
Both pole bounds come from the local proofs, and both inverse laws from field
arithmetic. No inverse-law or bounded-section-isomorphism hypothesis occurs. -/
def theorem_3_2 :
    ↥(baseSections t kind germ) ≃ₗ[ℂ] ↥(coverSections t kind eval) where
  toFun x := ⟨divideByAntiEquiv t w hw htw x.val,
    (quotient_membership t w hw htw kind eval germ reference href hpull homega x.val).mpr x.property⟩
  invFun f := ⟨(divideByAntiEquiv t w hw htw).symm f.val, by
    apply (quotient_membership t w hw htw kind eval germ reference href hpull homega _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv x := by apply Subtype.ext; exact (divideByAntiEquiv t w hw htw).symm_apply_apply x.val
  right_inv f := by apply Subtype.ext; exact (divideByAntiEquiv t w hw htw).apply_symm_apply f.val
  map_add' x y := by apply Subtype.ext; exact (divideByAntiEquiv t w hw htw).map_add _ _
  map_smul' c x := by apply Subtype.ext; exact (divideByAntiEquiv t w hw htw).map_smul c _

theorem orientation_dimension :
    Module.finrank ℂ (baseSections t kind germ) = Module.finrank ℂ (coverSections t kind eval) :=
  (theorem_3_2 t w hw htw kind eval germ reference href hpull homega).finrank_eq

#print axioms quotient_membership
#print axioms theorem_3_2
#print axioms orientation_dimension
end Problem32.PaperOrientationGlobal

