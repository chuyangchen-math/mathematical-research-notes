import Mathlib

/-!
Explicit gluing of functions on a set cover, and transport of compatible
local section families along overlap-compatible linear equivalences.
The cover, geometric local section spaces, and overlap compatibility for
the paper have NOT been constructed by this file.
-/

noncomputable section
namespace Problem32.Gluing

section FunctionGluing

variable {X I : Type*} (U : I → Set X)

/-- Families of local functions agreeing on actual set intersections. -/
def compatibleFunctions : Submodule ℂ ((i : I) → U i → ℂ) where
  carrier := {s | ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), s i ⟨x, hi⟩ = s j ⟨x, hj⟩}
  zero_mem' := by intro i j x hi hj; rfl
  add_mem' := by intro f g hf hg i j x hi hj; simp only [Pi.add_apply, hf i j x hi hj, hg i j x hi hj]
  smul_mem' := by intro c f hf i j x hi hj; simp only [Pi.smul_apply, hf i j x hi hj]

def restriction : (X → ℂ) →ₗ[ℂ] ↥(compatibleFunctions U) where
  toFun f := ⟨fun _ x => f x.val, by intro i j x hi hj; rfl⟩
  map_add' f g := rfl
  map_smul' c f := rfl

def glue (hcover : ∀ x, ∃ i, x ∈ U i) (s : compatibleFunctions U) : X → ℂ :=
  fun x => s.val (Classical.choose (hcover x)) ⟨x, Classical.choose_spec (hcover x)⟩

/-- The glued value agrees on every patch, independently of the chosen patch. -/
theorem glue_on_patch (hcover : ∀ x, ∃ i, x ∈ U i)
    (s : compatibleFunctions U) (i : I) (x : U i) :
    glue U hcover s x.val = s.val i x :=
  s.property (Classical.choose (hcover x.val)) i x.val
    (Classical.choose_spec (hcover x.val)) x.property

/-- Both existence and uniqueness of gluing, as a linear equivalence.
This statement concerns functions, without an analytic regularity assertion. -/
def functionGluingEquiv (hcover : ∀ x, ∃ i, x ∈ U i) :
    (X → ℂ) ≃ₗ[ℂ] ↥(compatibleFunctions U) where
  toFun := restriction U
  invFun := glue U hcover
  left_inv f := rfl
  right_inv s := by
    apply Subtype.ext
    funext i x
    exact glue_on_patch U hcover s i x
  map_add' := (restriction U).map_add
  map_smul' := (restriction U).map_smul

theorem glued_unique (hcover : ∀ x, ∃ i, x ∈ U i)
    (f g : X → ℂ) (h : ∀ i (x : U i), f x.val = g x.val) : f = g := by
  apply (functionGluingEquiv U hcover).injective
  apply Subtype.ext
  funext i x
  exact h i x

end FunctionGluing

section LocalEquivalences

variable {I : Type*}
  {V W : I → Type*} {O P : I → I → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  [∀ i j, AddCommGroup (O i j)] [∀ i j, Module ℂ (O i j)]
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module ℂ (P i j)]

/-- Equalizer of the two restriction maps to each overlap. -/
def compatibleSections
    (left : ∀ i j, V i →ₗ[ℂ] O i j)
    (right : ∀ i j, V j →ₗ[ℂ] O i j) : Submodule ℂ ((i : I) → V i) where
  carrier := {s | ∀ i j, left i j (s i) = right i j (s j)}
  zero_mem' := by intros; simp
  add_mem' := by intro s t hs ht i j; simp only [Pi.add_apply, map_add, hs i j, ht i j]
  smul_mem' := by intro c s hs i j; simp only [Pi.smul_apply, map_smul, hs i j]

/-- Construct the induced equivalence of compatible families from local
equivalences and commuting restriction squares. Reverse compatibility is
proved using injectivity on overlaps; no global inverse is assumed. -/
def compatibleSectionsEquiv
    (leftV : ∀ i j, V i →ₗ[ℂ] O i j) (rightV : ∀ i j, V j →ₗ[ℂ] O i j)
    (leftW : ∀ i j, W i →ₗ[ℂ] P i j) (rightW : ∀ i j, W j →ₗ[ℂ] P i j)
    (e : ∀ i, V i ≃ₗ[ℂ] W i) (overlap : ∀ i j, O i j ≃ₗ[ℂ] P i j)
    (hleft : ∀ i j x, leftW i j (e i x) = overlap i j (leftV i j x))
    (hright : ∀ i j x, rightW i j (e j x) = overlap i j (rightV i j x)) :
    ↥(compatibleSections leftV rightV) ≃ₗ[ℂ] ↥(compatibleSections leftW rightW) where
  toFun s := ⟨fun i => e i (s.val i), by
    intro i j
    rw [hleft, hright, s.property i j]⟩
  invFun s := ⟨fun i => (e i).symm (s.val i), by
    intro i j
    apply (overlap i j).injective
    rw [← hleft, ← hright, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact s.property i j⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    exact (e i).symm_apply_apply _
  right_inv s := by
    apply Subtype.ext
    funext i
    exact (e i).apply_symm_apply _
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact (e i).map_add _ _
  map_smul' c s := by
    apply Subtype.ext
    funext i
    exact (e i).map_smul c _

end LocalEquivalences

#print axioms functionGluingEquiv
#print axioms compatibleSectionsEquiv

end Problem32.Gluing
