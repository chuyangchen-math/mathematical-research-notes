import PrincipalParts

/-!
Constructed bases of local anti-invariant principal parts.
Ramified charts retain w⁻¹,w⁻³,...; unramified charts have two exchanged sheets.
No compact curve, global Mittag--Leffler map, or period map is asserted here.
-/

noncomputable section
namespace Problem32.AntiPrincipalParts

open HahnSeries Problem32.LocalLaurent Problem32.PrincipalParts

def antiFiniteParts (m : ℕ) : Submodule ℂ Series := paritySpace 1 ⊓ finiteParts m

/-- Coefficients of the allowed negative odd powers. -/
def fromOddCoefficients (m : ℕ) : (Fin ((m+1)/2) → ℂ) →ₗ[ℂ] Series where
  toFun v := ∑ i : Fin ((m+1)/2), HahnSeries.single (-2*(i : ℤ)-1) (v i)
  map_add' v w := by simp [HahnSeries.single_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ext n
    by_cases h : -2*(i : ℤ)-1 = n
    · subst n; simp
    · simp only [HahnSeries.coeff_smul, HahnSeries.coeff_single, if_neg (Ne.symm h), smul_zero]

theorem fromOddCoefficients_at (m : ℕ) (v : Fin ((m+1)/2) → ℂ)
    (i : Fin ((m+1)/2)) :
    (fromOddCoefficients m v).coeff (-2*(i : ℤ)-1) = v i := by
  simp only [fromOddCoefficients, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact HahnSeries.coeff_single_same _ _
  · intro j hj hji
    apply HahnSeries.coeff_single_of_ne
    intro h
    apply hji
    apply Fin.ext
    omega
  · intro h
    exact False.elim (h (Finset.mem_univ i))

theorem fromOddCoefficients_outside (m : ℕ) (v : Fin ((m+1)/2) → ℂ) (n : ℤ)
    (hn : n < -(m : ℤ) ∨ 0 ≤ n ∨ (n-1)%2 ≠ 0) :
    (fromOddCoefficients m v).coeff n = 0 := by
  simp only [fromOddCoefficients, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply HahnSeries.coeff_single_of_ne
  have hlt := i.isLt
  omega

theorem fromOddCoefficients_mem (m : ℕ) (v : Fin ((m+1)/2) → ℂ) :
    fromOddCoefficients m v ∈ antiFiniteParts m := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact fromOddCoefficients_outside m v n (Or.inr (Or.inr hn))
  · intro n hn
    exact fromOddCoefficients_outside m v n (Or.inl hn)
  · intro n hn
    exact fromOddCoefficients_outside m v n (Or.inr (Or.inl hn))

/-- The negative odd monomials form a genuine basis, expressed as an
explicit equivalence with a coordinate vector space. -/
def antiFinitePartsEquiv (m : ℕ) :
    (Fin ((m+1)/2) → ℂ) ≃ₗ[ℂ] ↥(antiFiniteParts m) where
  toFun v := ⟨fromOddCoefficients m v, fromOddCoefficients_mem m v⟩
  invFun f i := f.val.coeff (-2*(i : ℤ)-1)
  left_inv v := by funext i; exact fromOddCoefficients_at m v i
  right_inv f := by
    apply Subtype.ext
    ext n
    by_cases hn : n < -(m : ℤ) ∨ 0 ≤ n ∨ (n-1)%2 ≠ 0
    · rw [fromOddCoefficients_outside m _ n hn]
      rcases hn with hn | hn | hn
      · exact (f.property.2.1 n hn).symm
      · exact (f.property.2.2 n hn).symm
      · exact (f.property.1 n hn).symm
    · let i : Fin ((m+1)/2) := ⟨((-n-1)/2).toNat, by omega⟩
      have heq : -2*(i : ℤ)-1=n := by dsimp [i]; omega
      rw [← heq, fromOddCoefficients_at]
  map_add' v w := by apply Subtype.ext; exact (fromOddCoefficients m).map_add _ _
  map_smul' c v := by apply Subtype.ext; exact (fromOddCoefficients m).map_smul c _

instance antiFiniteParts_finite (m : ℕ) : FiniteDimensional ℂ (antiFiniteParts m) :=
  FiniteDimensional.of_injective (antiFinitePartsEquiv m).symm.toLinearMap
    (antiFinitePartsEquiv m).symm.injective

theorem antiFiniteParts_finrank (m : ℕ) :
    Module.finrank ℂ (antiFiniteParts m) = (m+1)/2 := by
  rw [← (antiFinitePartsEquiv m).finrank_eq, Module.finrank_fin_fun]

/-- The two unramified sheets are exchanged by the deck involution;
anti-invariance therefore means the second principal part is minus the first. -/
def swappedAnti (m : ℕ) : Submodule ℂ (finiteParts m × finiteParts m) where
  carrier := {p | p.2 = -p.1}
  zero_mem' := by
    change (0 : finiteParts m) = -0
    apply Subtype.ext
    change (0 : Series) = -0
    simp
  add_mem' := by
    intro p q hp hq
    change p.2 + q.2 = -(p.1 + q.1)
    rw [hp, hq]
    abel
  smul_mem' := by
    intro c p hp
    change c • p.2 = -(c • p.1)
    rw [hp]
    exact smul_neg c p.1

def swappedAntiEquiv (m : ℕ) : ↥(finiteParts m) ≃ₗ[ℂ] ↥(swappedAnti m) where
  toFun f := ⟨(f, -f), rfl⟩
  invFun p := p.val.1
  left_inv f := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact p.property.symm
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -(f+g) = -f + -g
      abel
  map_smul' c f := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (smul_neg c f).symm

theorem swappedAnti_finrank (m : ℕ) : Module.finrank ℂ (swappedAnti m) = m := by
  rw [← (swappedAntiEquiv m).finrank_eq, finiteParts_finrank]

/-- Dimension of a product of the constructed ramified local spaces. -/
theorem totalRamified_finrank {I : Type*} [Fintype I] (m : I → ℕ) :
    Module.finrank ℂ ((i : I) → antiFiniteParts (m i)) =
      ∑ i, (m i + 1)/2 := by
  letI : ∀ i : I, Module.Free ℂ (antiFiniteParts (m i)) :=
    fun i => Module.Free.of_divisionRing ℂ (antiFiniteParts (m i))
  letI : ∀ i : I, Module.Finite ℂ (antiFiniteParts (m i)) := fun i => inferInstance
  rw [Module.finrank_pi_fintype]
  simp only [antiFiniteParts_finrank]

/-- A concrete local anti-invariant holomorphic function with zero principal
part. This prevents incorrectly treating the local principal-part map as
injective on the anti-part; the compact global case needs extra geometry. -/
theorem local_anti_kernel_nontrivial :
    ∃ f : Series, f ≠ 0 ∧ deck f = -f ∧ principalPart f = 0 := by
  let f : Series := HahnSeries.single 1 (1 : ℂ)
  refine ⟨f, HahnSeries.single_ne_zero (by norm_num), ?_, ?_⟩
  · apply (parity_odd_iff_anti 1 (by norm_num) f).mp
    intro n hn
    exact HahnSeries.coeff_single_of_ne (by omega)
  · have hf : f ∈ bounded 0 := by
      intro n hn
      exact HahnSeries.coeff_single_of_ne (by omega)
    rw [← principalPart_ker] at hf
    exact hf

#print axioms antiFinitePartsEquiv
#print axioms antiFiniteParts_finrank
#print axioms swappedAntiEquiv
#print axioms totalRamified_finrank
#print axioms local_anti_kernel_nontrivial

end Problem32.AntiPrincipalParts
