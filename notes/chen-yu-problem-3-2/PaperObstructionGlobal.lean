import PaperOrientationGlobal
import PaperLinearAssembly
import PaperPeriodComparison

noncomputable section
namespace Problem32.PaperObstructionGlobal
open Problem32.GeometricAlgebra Problem32.LocalLaurent
open Problem32.PaperOrientationLocal Problem32.PaperOrientationGlobal
open Problem32.PaperLinearAssembly
variable {F I P H : Type*} [Field F] [Algebra ℂ F]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup H] [Module ℂ H]

def boundedFunctions (kind : I → ChartKind) (eval : I → Germ F) : Submodule ℂ F where
  carrier := {f | ∀ i, (eval i).ring f ∈ bounded (coverOrder (kind i))}
  zero_mem' := by intro i; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by intro f g hf hg i; rw [map_add]; exact (bounded _).add_mem (hf i) (hg i)
  smul_mem' := by intro c f hf i; rw [(eval i).scalar]; exact (bounded _).smul_mem c (hf i)

def boundedAntiEquiv (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind) (eval : I → Germ F)
    (stable : ∀ f ∈ boundedFunctions kind eval, t.toLinearMap f ∈ boundedFunctions kind eval) :
    coverSections t kind eval ≃ₗ[ℂ]
      antiSpace (restrictedAction t.toLinearMap (boundedFunctions kind eval) stable) where
  toFun f := ⟨⟨f.val.val, f.property⟩, Subtype.ext f.val.property⟩
  invFun f := ⟨⟨f.val.val, congrArg Subtype.val f.property⟩, f.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compact connected holomorphic functions are constant; constants are
fixed by an algebra automorphism. Only the former is the analytic input. -/
theorem fixed_kernel_from_constants (t : F ≃ₐ[ℂ] F) (kind : I → ChartKind)
    (eval : I → Germ F)
    (stable : ∀ f ∈ boundedFunctions kind eval, t.toLinearMap f ∈ boundedFunctions kind eval)
    (principal : boundedFunctions kind eval →ₗ[ℂ] P)
    (compact_constancy : ∀ f, principal f = 0 → ∃ c : ℂ, f.val = algebraMap ℂ F c) :
    ∀ f, principal f = 0 → restrictedAction t.toLinearMap (boundedFunctions kind eval) stable f = f := by
  intro f hf
  obtain ⟨c, hc⟩ := compact_constancy f hf
  apply Subtype.ext
  change t f.val = f.val
  rw [hc]
  exact t.commutes c

variable (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w)
  (kind : I → ChartKind) (eval : I → Germ F)
  (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series)
  (reference : I → Series) (href : ∀ i, reference i ≠ 0)
  (hpull : ∀ i x, pullback (kind i) (germ i x) = (eval i).ring x.val * reference i)
  (homega : ∀ i, omegaLocal (kind i) = (eval i).ring w * reference i)
  (stable : ∀ f ∈ boundedFunctions kind eval, t.toLinearMap f ∈ boundedFunctions kind eval)
  (ht : ∀ f, t (t f) = f)
  (principal : boundedFunctions kind eval →ₗ[ℂ] P) (action : P →ₗ[ℂ] P)
  (delta : P →ₗ[ℂ] H)
  (equivariant : ∀ f, principal (restrictedAction t.toLinearMap (boundedFunctions kind eval) stable f) = action (principal f))
  (mittag_leffler : LinearMap.range principal = LinearMap.ker delta)
  (compact_constants : ∀ f, principal f = 0 →
    restrictedAction t.toLinearMap (boundedFunctions kind eval) stable f = f)

/-- Composition of the constructed orientation quotient with the derived
anti-part of the ordinary Mittag--Leffler exact sequence. -/
def theorem_4_1 : baseSections t kind germ ≃ₗ[ℂ] antiKernel action delta :=
  (theorem_3_2 t w hw htw kind eval germ reference href hpull homega).trans
    ((boundedAntiEquiv t kind eval stable).trans
      (antiKernelEquiv
        (restrictedAction t.toLinearMap (boundedFunctions kind eval) stable)
        action principal delta
        (by intro f; apply Subtype.ext; exact ht f.val)
        equivariant mittag_leffler compact_constants))

theorem positive_kernel_iff_not_injective
    (action : P →ₗ[ℂ] P) (delta : P →ₗ[ℂ] H)
    [FiniteDimensional ℂ (antiKernel action delta)] :
    0 < Module.finrank ℂ (antiKernel action delta) ↔
      ¬ Function.Injective (delta.comp (antiSpace action).subtype) := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨x, hx⟩ hi
    apply hx
    apply Subtype.ext
    have h := hi (a₁ := ⟨x.val, x.property.1⟩) (a₂ := 0) (by
      change delta x.val = delta 0
      rw [map_zero]
      exact x.property.2)
    exact congrArg (fun v : antiSpace action => v.val) h
  · intro hn
    by_contra h
    apply hn
    intro x y hxy
    have hz : delta (x.val-y.val) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy
    let z : antiKernel action delta := ⟨x.val-y.val,
      (antiSpace action).sub_mem x.property y.property, hz⟩
    have hall : ∀ x : antiKernel action delta, x = 0 := by simpa only [not_exists, not_not] using h
    have hzero : z = 0 := hall z
    apply Subtype.ext
    exact sub_eq_zero.mp (congrArg Subtype.val hzero)

include hw htw href hpull homega ht equivariant mittag_leffler compact_constants in
theorem orientation_obstruction_criterion [FiniteDimensional ℂ P] :
    0 < Module.finrank ℂ (coverSections t kind eval) ↔
      ¬ Function.Injective (delta.comp (antiSpace action).subtype) := by
  rw [← orientation_dimension t w hw htw kind eval germ reference href hpull homega]
  rw [(theorem_4_1 t w hw htw kind eval germ reference href hpull homega
    stable ht principal action delta equivariant mittag_leffler compact_constants).finrank_eq]
  exact positive_kernel_iff_not_injective action delta

#print axioms orientation_obstruction_criterion
#print axioms theorem_4_1
#print axioms fixed_kernel_from_constants
#print axioms positive_kernel_iff_not_injective
end Problem32.PaperObstructionGlobal

