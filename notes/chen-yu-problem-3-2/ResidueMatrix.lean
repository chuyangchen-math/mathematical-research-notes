import AntiPrincipalParts

/-!
A finite residue matrix derived from Laurent multiplication and the explicit
negative-odd-power basis. Its identification with a compact curve's global
Mittag--Leffler map via duality is not asserted here.
-/

noncomputable section
namespace Problem32.ResidueMatrix

open HahnSeries Problem32.LocalLaurent Problem32.AntiPrincipalParts

theorem raw_residue_formula (m : ℕ) (form : Series)
    (v : Fin ((m+1)/2) → ℂ) :
    (fromOddCoefficients m v * form).coeff (-1) =
      ∑ i, v i * form.coeff (2*(i : ℤ)) := by
  change ((∑ i : Fin ((m+1)/2), HahnSeries.single (-2*(i : ℤ)-1) (v i)) *
    form).coeff (-1) = _
  rw [Finset.sum_mul, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [HahnSeries.coeff_single_mul]
  congr 2
  omega

/-- Residues of principal parts multiplied by specified differential
coefficients. The formula uses the actual Laurent-series product. -/
def residueMap (m rows : ℕ) (forms : Fin rows → Series) :
    (Fin ((m+1)/2) → ℂ) →ₗ[ℂ] (Fin rows → ℂ) where
  toFun v j := (fromOddCoefficients m v * forms j).coeff (-1)
  map_add' v w := by
    funext j
    change (fromOddCoefficients m (v+w) * forms j).coeff (-1) = _
    change (fromOddCoefficients m (v+w) * forms j).coeff (-1) =
      (fromOddCoefficients m v * forms j).coeff (-1) +
      (fromOddCoefficients m w * forms j).coeff (-1)
    simp only [raw_residue_formula, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext j
    change (fromOddCoefficients m (c • v) * forms j).coeff (-1) = _
    change (fromOddCoefficients m (c • v) * forms j).coeff (-1) =
      c • (fromOddCoefficients m v * forms j).coeff (-1)
    simp only [raw_residue_formula, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The matrix entries are even Taylor/Laurent coefficients of the forms. -/
def matrix (m rows : ℕ) (forms : Fin rows → Series) :
    Matrix (Fin rows) (Fin ((m+1)/2)) ℂ := fun j i => (forms j).coeff (2*(i : ℤ))

theorem residueMap_apply (m rows : ℕ) (forms : Fin rows → Series)
    (v : Fin ((m+1)/2) → ℂ) (j : Fin rows) :
    residueMap m rows forms v j = ∑ i, v i * (forms j).coeff (2*(i : ℤ)) := by
  change ((∑ i : Fin ((m+1)/2), HahnSeries.single (-2*(i : ℤ)-1) (v i)) *
    forms j).coeff (-1) = _
  rw [Finset.sum_mul, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [HahnSeries.coeff_single_mul]
  congr 2
  omega

/-- The finite matrix is proved to represent the residue map. -/
theorem residueMap_eq_mulVecLin (m rows : ℕ) (forms : Fin rows → Series) :
    residueMap m rows forms = (matrix m rows forms).mulVecLin := by
  apply LinearMap.ext
  intro v
  funext j
  rw [residueMap_apply]
  change (∑ i, v i * (forms j).coeff (2*(i : ℤ))) =
      ∑ i : Fin ((m+1)/2), (forms j).coeff (2*(i : ℤ)) * v i
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem residueMap_rank_nullity (m rows : ℕ) (forms : Fin rows → Series) :
    Module.finrank ℂ (LinearMap.range (residueMap m rows forms)) +
      Module.finrank ℂ (LinearMap.ker (residueMap m rows forms)) = (m+1)/2 := by
  simpa only [Module.finrank_fin_fun] using
    (residueMap m rows forms).finrank_range_add_finrank_ker

theorem full_rank_iff_zero_kernel (m rows : ℕ) (forms : Fin rows → Series) :
    Module.finrank ℂ (LinearMap.range (residueMap m rows forms)) = (m+1)/2 ↔
      Module.finrank ℂ (LinearMap.ker (residueMap m rows forms)) = 0 := by
  have h := residueMap_rank_nullity m rows forms
  omega

#print axioms residueMap_eq_mulVecLin
#print axioms residueMap_rank_nullity

end Problem32.ResidueMatrix
