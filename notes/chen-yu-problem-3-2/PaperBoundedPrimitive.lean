import PaperDifferentialBridge

noncomputable section
namespace Problem32.PaperBoundedPrimitive
open Problem32.LocalLaurent Problem32.PrincipalParts Problem32.PaperDifferentialBridge
variable {U S T C I : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [AddCommGroup C] [Module ℂ C]

def functions (germ : I → U →ₗ[ℂ] Series) (bound : I → ℤ) : Submodule ℂ U where
  carrier := {f | ∀ i, germ i f ∈ bounded (bound i)}
  zero_mem' := by intro i; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by intro f g hf hg i; rw [map_add]; exact (bounded _).add_mem (hf i) (hg i)
  smul_mem' := by intro c f hf i; rw [map_smul]; exact (bounded _).smul_mem c (hf i)

/-- The bounded version of the zero-period primitive theorem is DERIVED
from the ordinary unbounded theorem and local principal-part recovery. -/
theorem bounded_exactness
    (functionGerm : I → U →ₗ[ℂ] Series) (formGerm : I → S →ₗ[ℂ] Series)
    (bound : I → ℤ) (nonpositive : ∀ i, bound i ≤ 0)
    (derivative : U →ₗ[ℂ] T) (inclusion : S →ₗ[ℂ] T)
    (faithful : Function.Injective inclusion)
    (d : functions functionGerm bound →ₗ[ℂ] S)
    (d_definition : ∀ f, derivative f.val = inclusion (d f))
    (local_derivative : ∀ f s, derivative f = inclusion s → ∀ i,
      LaurentSeries.derivative ℂ (functionGerm i f) = formGerm i s)
    (principal_bounds : ∀ s i, ∃ p : Series, p ∈ negative ∧ p ∈ bounded (bound i) ∧
      principalPart (formGerm i s) = LaurentSeries.derivative ℂ p)
    (period : S →ₗ[ℂ] C)
    (global_primitive : ∀ s, period s = 0 ↔ ∃ f : U, derivative f = inclusion s) :
    LinearMap.ker period = LinearMap.range d := by
  ext s
  constructor
  · intro hs
    obtain ⟨f, hf⟩ := (global_primitive s).mp hs
    have hb : f ∈ functions functionGerm bound := by
      intro i
      obtain ⟨p, hp, hbound, heq⟩ := principal_bounds s i
      apply primitive_bound_from_principal (functionGerm i f) p (bound i) (nonpositive i) hp hbound
      rwa [local_derivative f s hf i]
    refine ⟨⟨f, hb⟩, faithful ?_⟩
    rw [← d_definition, hf]
  · rintro ⟨f, rfl⟩
    exact (global_primitive (d f)).mpr ⟨f.val, d_definition f⟩

#print axioms bounded_exactness
end Problem32.PaperBoundedPrimitive
