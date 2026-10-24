import ChartDifferential
import LocalPrimitiveGluing

/-! Average a compatible primitive to an anti-invariant primitive. Analytic
restriction maps and comparison with topological periods remain external data. -/
noncomputable section
namespace Problem32.AntiPrimitiveGluing
open Problem32.LocalLaurent Problem32.ChartCoverAction
open Problem32.ChartDifferential Problem32.LocalPrimitiveGluing

variable {I C : Type*} [AddCommGroup C] [Module ℂ C]

theorem exists_anti_primitive_iff
    (a : ChartAction I) (D : (I → Series) →ₗ[ℂ] C) (u : C →ₗ[ℂ] C)
    (hD : ∀ f, D (action a f) = u (D f))
    (w : I → Series) (hw : formAction a w = -w) :
    (∃ f, D f = 0 ∧ differentiate f = w) ↔
      ∃ f, D f = 0 ∧ differentiate f = w ∧ action a f = -f := by
  constructor
  · rintro ⟨f, hf, hdf⟩
    let g : I → Series := (2 : ℂ)⁻¹ • (f - action a f)
    refine ⟨g, ?_, ?_, ?_⟩
    · dsimp [g]
      rw [map_smul, map_sub, hD, hf, map_zero, sub_self, smul_zero]
    · dsimp [g]
      rw [map_smul, map_sub, differentiate_equivariant, hdf, hw, sub_neg_eq_add]
      rw [← two_smul ℂ w, smul_smul]
      norm_num
    · dsimp [g]
      rw [map_smul, map_sub, action_twice]
      funext i
      change (2 : ℂ)⁻¹ • (action a f i - f i) =
        -((2 : ℂ)⁻¹ • (f i - action a f i))
      simp only [smul_sub]
      abel
  · rintro ⟨f, hf, hdf, _⟩
    exact ⟨f, hf, hdf⟩

theorem zero_obstruction_iff_anti_primitive
    (a : ChartAction I) (D : (I → Series) →ₗ[ℂ] C) (u : C →ₗ[ℂ] C)
    (hD : ∀ f, D (action a f) = u (D f))
    (w : I → zeroCoefficient (-1))
    (hw : formAction a (fun i => (w i).val) = -(fun i => (w i).val)) :
    primitiveObstruction (I := I) D w = 0 ↔
      ∃ f, D f = 0 ∧ differential f = w ∧ action a f = -f := by
  constructor
  · intro hz
    obtain ⟨f, hf, hdf⟩ := (primitiveObstruction_zero_iff D w).mp hz
    have hd : differentiate f = fun i => (w i).val := by
      funext i
      exact congrArg Subtype.val (congrFun hdf i)
    obtain ⟨g, hg, hdg, hag⟩ :=
      (exists_anti_primitive_iff a D u hD (fun i => (w i).val) hw).mp ⟨f, hf, hd⟩
    refine ⟨g, hg, ?_, hag⟩
    funext i
    apply Subtype.ext
    exact congrFun hdg i
  · rintro ⟨f, hf, hdf, _⟩
    exact (primitiveObstruction_zero_iff D w).mpr ⟨f, hf, hdf⟩

#print axioms exists_anti_primitive_iff
#print axioms zero_obstruction_iff_anti_primitive
end Problem32.AntiPrimitiveGluing
