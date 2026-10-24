import PaperSpinLocal
import PaperOrientationGlobal
import PaperLinearAssembly
import ChartCoverAction
import PaperSignatureData

/-! Theorem 2.1 relative to the standard canonical-cover and germ interface.
The eigenspace identifications and dimension splitting are derived below;
Riemann--Roch itself is an explicit external input. -/
noncomputable section
namespace Problem32.PaperSpinGlobal
open Problem32.LocalLaurent Problem32.GeometricAlgebra Problem32.PaperLinearAssembly
open Problem32.PaperSpinLocal
open Problem32.PaperOrientationGlobal (Germ)
variable {F I : Type*} [Field F] [Algebra ℂ F]

def coverSpace (kind : I → SpinKind) (eval : I → Germ F) : Submodule ℂ F where
  carrier := {f | ∀ i, (eval i).ring f ∈ bounded (lowerBound (kind i))}
  zero_mem' := by intro i; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by intro f g hf hg i; rw [map_add]; exact (bounded _).add_mem (hf i) (hg i)
  smul_mem' := by intro c f hf i; rw [(eval i).scalar]; exact (bounded _).smul_mem c (hf i)

def baseSpace (t : F ≃ₐ[ℂ] F) (bound : I → ℤ)
    (germ : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series) :
    Submodule ℂ (invariantSpace t.toLinearMap) where
  carrier := {x | ∀ i, germ i x ∈ bounded (bound i)}
  zero_mem' := by intro i; rw [map_zero]; exact (bounded _).zero_mem
  add_mem' := by intro f g hf hg i; rw [map_add]; exact (bounded _).add_mem (hf i) (hg i)
  smul_mem' := by intro c f hf i; rw [map_smul]; exact (bounded _).smul_mem c (hf i)

theorem deck_preserves_bound (k : ℤ) (f : Series) (hf : f ∈ bounded k) : deck f ∈ bounded k := by
  intro n hn
  rw [deck_coeff, hf n hn]
  split_ifs <;> simp

theorem coverSpace_stable (t : F ≃ₐ[ℂ] F) (kind : I → SpinKind) (eval : I → Germ F)
    (a : Problem32.ChartCoverAction.ChartAction I)
    (hkind : ∀ i, kind (a.exchange i) = kind i)
    (hdeck : ∀ i f, (eval i).ring (t f) =
      if a.reflect i then deck ((eval (a.exchange i)).ring f) else (eval (a.exchange i)).ring f) :
    ∀ f ∈ coverSpace kind eval, t.toLinearMap f ∈ coverSpace kind eval := by
  intro f hf i
  change (eval i).ring (t f) ∈ bounded _
  rw [hdeck]
  have hb := hf (a.exchange i)
  rw [hkind] at hb
  split
  · exact deck_preserves_bound _ _ hb
  · exact hb

variable (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w)
  (kind : I → SpinKind) (eval : I → Germ F)
  (functions differentials : I → invariantSpace t.toLinearMap →ₗ[ℂ] Series)
  (reference : I → Series) (href : ∀ i, reference i ≠ 0)
  (hplus : ∀ i x, (eval i).ring x.val = plusMap (kind i) (functions i x))
  (hpull : ∀ i x, pullback (kind i) (differentials i x) = (eval i).ring x.val * reference i)
  (homega : ∀ i, omegaLocal (kind i) = (eval i).ring w * reference i)

include hplus in
def plusSectionsEquiv :
    ↥(baseSpace t (fun i => -contribution (kind i)) functions) ≃ₗ[ℂ]
      ↥(within (invariantSpace t.toLinearMap) (coverSpace kind eval)) :=
  restrictEquiv (LinearEquiv.refl ℂ _) _ _ (by
    intro x
    change (∀ i, (eval i).ring x.val ∈ bounded (lowerBound (kind i))) ↔ _
    constructor
    · intro h i
      have hi := h i
      rw [hplus] at hi
      exact (plus_bound_iff (kind i) (functions i x)).mp hi
    · intro h i
      rw [hplus]
      exact (plus_bound_iff (kind i) (functions i x)).mpr (h i))

include href hpull homega in
def minusSectionsEquiv :
    ↥(baseSpace t (fun i => contribution (kind i)) differentials) ≃ₗ[ℂ]
      ↥(within (antiSpace t.toLinearMap) (coverSpace kind eval)) :=
  restrictEquiv (divideByAntiEquiv t w hw htw) _ _ (by
    intro x
    change (∀ i, (eval i).ring (x.val/w) ∈ bounded (lowerBound (kind i))) ↔ _
    have he : ∀ i, (eval i).ring (x.val/w) = minusMap (kind i) (differentials i x) := by
      intro i
      exact germ_minus (eval i).ring (kind i) x.val w (reference i) (differentials i x)
        (href i) (hpull i x) (homega i)
    constructor
    · intro h i
      have hi := h i
      rw [he] at hi
      exact (minus_bound_iff (kind i) (differentials i x)).mp hi
    · intro h i
      rw [he]
      exact (minus_bound_iff (kind i) (differentials i x)).mpr (h i))

include hw htw href hplus hpull homega in
theorem theorem_2_1 [FiniteDimensional ℂ (coverSpace kind eval)]
    (ht : ∀ x, t (t x) = x)
    (a : Problem32.ChartCoverAction.ChartAction I)
    (hkind : ∀ i, kind (a.exchange i) = kind i)
    (hdeck : ∀ i f, (eval i).ring (t f) =
      if a.reflect i then deck ((eval (a.exchange i)).ring f) else (eval (a.exchange i)).ring f)
    (degree genus : ℤ)
    (riemann_roch :
      (Module.finrank ℂ (baseSpace t (fun i => -contribution (kind i)) functions) : ℤ) -
      (Module.finrank ℂ (baseSpace t (fun i => contribution (kind i)) differentials) : ℤ) =
      degree+1-genus) :
    (Module.finrank ℂ (coverSpace kind eval) : ℤ) % 2 = (1-genus+degree)%2 := by
  have hs := bounded_dimension_split t.toLinearMap (coverSpace kind eval) ht
    (coverSpace_stable t kind eval a hkind hdeck)
  have hp := (plusSectionsEquiv t kind eval functions hplus).finrank_eq
  have hm := (minusSectionsEquiv t w hw htw kind eval differentials reference href hpull homega).finrank_eq
  omega

include hw htw href hplus hpull homega in
def spinSectionDecomposition
    (ht : ∀ x, t (t x) = x)
    (a : Problem32.ChartCoverAction.ChartAction I)
    (hkind : ∀ i, kind (a.exchange i) = kind i)
    (hdeck : ∀ i f, (eval i).ring (t f) =
      if a.reflect i then deck ((eval (a.exchange i)).ring f) else (eval (a.exchange i)).ring f) :=
  let stable := coverSpace_stable t kind eval a hkind hdeck
  (involutionDecomposition (restrictedAction t.toLinearMap (coverSpace kind eval) stable)
    (by intro x; apply Subtype.ext; exact ht x.val)).trans
    (LinearEquiv.prodCongr
      ((fixedWithinEquiv t.toLinearMap (coverSpace kind eval) stable).trans
        (plusSectionsEquiv t kind eval functions hplus).symm)
      ((antiWithinEquiv t.toLinearMap (coverSpace kind eval) stable).trans
        (minusSectionsEquiv t w hw htw kind eval differentials reference href hpull homega).symm))

include hw htw href hplus hpull homega in
theorem theorem_2_1_floor [FiniteDimensional ℂ (coverSpace kind eval)]
    (ht : ∀ x, t (t x) = x)
    (a : Problem32.ChartCoverAction.ChartAction I)
    (hkind : ∀ i, kind (a.exchange i) = kind i)
    (hdeck : ∀ i f, (eval i).ring (t f) =
      if a.reflect i then deck ((eval (a.exchange i)).ring f) else (eval (a.exchange i)).ring f)
    {J : Type*} (singularities : Finset J) (orders : J → SpinKind) (genus : ℤ)
    (riemann_roch :
      (Module.finrank ℂ (baseSpace t (fun i => -contribution (kind i)) functions) : ℤ) -
      (Module.finrank ℂ (baseSpace t (fun i => contribution (kind i)) differentials) : ℤ) =
      (∑ j ∈ singularities, contribution (orders j))+1-genus) :
    (Module.finrank ℂ (coverSpace kind eval) : ℤ) % 2 =
      (1-genus+∑ j ∈ singularities, (order (orders j)+1)/4)%2 := by
  have h := theorem_2_1 t w hw htw kind eval functions differentials reference href
    hplus hpull homega ht a hkind hdeck
    (∑ j ∈ singularities, contribution (orders j)) genus riemann_roch
  rwa [Problem32.PaperSignatureData.spin_degree_formula] at h

#print axioms spinSectionDecomposition
#print axioms theorem_2_1_floor
#print axioms plusSectionsEquiv
#print axioms minusSectionsEquiv
#print axioms theorem_2_1
end Problem32.PaperSpinGlobal
