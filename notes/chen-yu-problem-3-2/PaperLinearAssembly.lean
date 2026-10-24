import GeometricAlgebra
noncomputable section
namespace Problem32.PaperLinearAssembly
open Problem32.GeometricAlgebra
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def restrictEquiv (e : V ≃ₗ[ℂ] W) (A : Submodule ℂ V) (B : Submodule ℂ W)
    (h : ∀ x, e x ∈ B ↔ x ∈ A) : A ≃ₗ[ℂ] B where
  toFun x := ⟨e x.val, (h x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (h _).mp (by rw [e.apply_symm_apply]; exact y.property)⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact e.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c _

def within (A B : Submodule ℂ V) : Submodule ℂ A := B.comap A.subtype

def restrictedAction (t : V →ₗ[ℂ] V) (B : Submodule ℂ V) (h : ∀ x ∈ B, t x ∈ B) : B →ₗ[ℂ] B where
  toFun x := ⟨t x.val, h x.val x.property⟩
  map_add' x y := by apply Subtype.ext; exact t.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact t.map_smul c _

def fixedWithinEquiv (t : V →ₗ[ℂ] V) (B : Submodule ℂ V) (h : ∀ x ∈ B, t x ∈ B) :
    invariantSpace (restrictedAction t B h) ≃ₗ[ℂ] within (invariantSpace t) B where
  toFun x := ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
  invFun y := ⟨⟨y.val.val, y.property⟩, Subtype.ext y.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def antiWithinEquiv (t : V →ₗ[ℂ] V) (B : Submodule ℂ V) (h : ∀ x ∈ B, t x ∈ B) :
    antiSpace (restrictedAction t B h) ≃ₗ[ℂ] within (antiSpace t) B where
  toFun x := ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
  invFun y := ⟨⟨y.val.val, y.property⟩, Subtype.ext y.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bounded_dimension_split (t : V →ₗ[ℂ] V) (B : Submodule ℂ V)
    [FiniteDimensional ℂ B] (ht : ∀ x, t (t x) = x) (h : ∀ x ∈ B, t x ∈ B) :
    Module.finrank ℂ B = Module.finrank ℂ (within (invariantSpace t) B) +
      Module.finrank ℂ (within (antiSpace t) B) := by
  have hsplit := involution_finrank (restrictedAction t B h) (by
    intro x; apply Subtype.ext; exact ht x.val)
  rw [(fixedWithinEquiv t B h).finrank_eq, (antiWithinEquiv t B h).finrank_eq] at hsplit
  exact hsplit

#print axioms bounded_dimension_split
end Problem32.PaperLinearAssembly
