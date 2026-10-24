import LocalLaurent

/-!
Concrete local principal parts of formal Laurent series.
The kernel and quotient identifications below are proved, not assumed.
This is NOT the global Mittag--Leffler boundary map of a compact curve.
-/

noncomputable section
namespace Problem32.PrincipalParts

open HahnSeries Problem32.LocalLaurent

/-- Series with only strictly negative powers. -/
def negative : Submodule ℂ Series where
  carrier := {f | ∀ n, 0 ≤ n → f.coeff n = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg n hn; simp [hf n hn, hg n hn]
  smul_mem' := by intro c f hf n hn; simp [hf n hn]

/-- Remove the holomorphic part by taking negative coefficients. -/
def principalPart : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.ofSuppBddBelow
    (fun n => if n < 0 then f.coeff n else 0) (by
      refine ⟨f.order, ?_⟩
      intro n hn
      by_contra h
      have hz := HahnSeries.coeff_eq_zero_of_lt_order (show n < f.order by omega)
      simp only [Function.mem_support] at hn
      split_ifs at hn <;> simp_all)
  map_add' f g := by
    ext n
    change (if n<0 then (f+g).coeff n else 0) =
      (if n<0 then f.coeff n else 0) + (if n<0 then g.coeff n else 0)
    split_ifs <;> simp only [HahnSeries.coeff_add, add_zero]
  map_smul' c f := by
    ext n
    change (if n<0 then (c • f).coeff n else 0) = c • (if n<0 then f.coeff n else 0)
    split_ifs <;> simp only [HahnSeries.coeff_smul, smul_zero]

@[simp] theorem principalPart_coeff (f : Series) (n : ℤ) :
    (principalPart f).coeff n = if n<0 then f.coeff n else 0 := rfl

theorem principalPart_negative (f : Series) : principalPart f ∈ negative := by
  intro n hn
  simp [show ¬ n<0 by omega]

theorem principalPart_eq_self (f : Series) (hf : f ∈ negative) :
    principalPart f = f := by
  ext n
  rw [principalPart_coeff]
  split_ifs with h
  · rfl
  · exact (hf n (by omega)).symm

theorem principalPart_idempotent (f : Series) :
    principalPart (principalPart f) = principalPart f :=
  principalPart_eq_self _ (principalPart_negative f)

theorem principalPart_ker : LinearMap.ker principalPart = bounded 0 := by
  ext f
  constructor
  · intro hf n hn
    have h := congrArg (fun g : Series => g.coeff n) hf
    simpa only [principalPart_coeff, hn, if_true, HahnSeries.coeff_zero] using h
  · intro hf
    apply HahnSeries.ext
    funext n
    rw [principalPart_coeff, HahnSeries.coeff_zero]
    split_ifs with hn
    · exact hf n hn
    · rfl

theorem principalPart_range : LinearMap.range principalPart = negative := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact principalPart_negative g
  · intro hf
    exact ⟨f, principalPart_eq_self f hf⟩

/-- The local quotient by holomorphic series is the principal-part space. -/
def quotientEquivPrincipalParts : (Series ⧸ bounded 0) ≃ₗ[ℂ] ↥negative := by
  rw [← principalPart_ker, ← principalPart_range]
  exact LinearMap.quotKerEquivRange principalPart

theorem principalPart_finite_support (f : Series) :
    (principalPart f).support.Finite := by
  apply (Set.finite_Icc f.order (-1)).subset
  intro n hn
  have hc : (principalPart f).coeff n ≠ 0 := hn
  rw [principalPart_coeff] at hc
  split_ifs at hc with hneg
  · constructor
    · by_contra h
      exact hc (HahnSeries.coeff_eq_zero_of_lt_order (by omega))
    · omega
  · exact False.elim (hc rfl)

theorem principalPart_preserves_bound (k : ℤ) (f : Series) (hf : f ∈ bounded k) :
    principalPart f ∈ bounded k := by
  intro n hn
  rw [principalPart_coeff]
  split_ifs
  · exact hf n hn
  · rfl

theorem principalPart_deck (f : Series) :
    principalPart (deck f) = deck (principalPart f) := by
  ext n
  simp only [principalPart_coeff, deck_coeff]
  split_ifs <;> simp

/-- Taking the principal part commutes with the actual Laurent derivative. -/
theorem principalPart_derivative (f : Series) :
    principalPart (LaurentSeries.derivative ℂ f) =
      LaurentSeries.derivative ℂ (principalPart f) := by
  ext n
  rw [principalPart_coeff, derivative_coeff, derivative_coeff, principalPart_coeff]
  by_cases hn : n < -1
  · simp only [show n<0 by omega, show n+1<0 by omega, if_true]
  · by_cases hz : n = -1
    · subst n
      norm_num
    · simp only [show ¬n<0 by omega, show ¬n+1<0 by omega, if_false, mul_zero]

/-- Pole order ≤ m with no nonnegative terms. -/
def finiteParts (m : ℕ) : Submodule ℂ Series := bounded (-(m : ℤ)) ⊓ negative

/-- Construct a principal part from its m coefficients of w⁻¹,...,w⁻ᵐ. -/
def fromCoefficients (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] Series where
  toFun v := ∑ i : Fin m, HahnSeries.single (-(i : ℤ)-1) (v i)
  map_add' v w := by simp [HahnSeries.single_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ext n
    by_cases h : -(i : ℤ)-1 = n
    · subst n
      simp
    · simp [HahnSeries.coeff_single_of_ne (Ne.symm h)]

theorem fromCoefficients_at (m : ℕ) (v : Fin m → ℂ) (i : Fin m) :
    (fromCoefficients m v).coeff (-(i : ℤ)-1) = v i := by
  simp only [fromCoefficients, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_sum]
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

theorem fromCoefficients_outside (m : ℕ) (v : Fin m → ℂ) (n : ℤ)
    (hn : n < -(m : ℤ) ∨ 0 ≤ n) : (fromCoefficients m v).coeff n = 0 := by
  simp only [fromCoefficients, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply HahnSeries.coeff_single_of_ne
  have hlt := i.isLt
  omega

theorem fromCoefficients_mem (m : ℕ) (v : Fin m → ℂ) :
    fromCoefficients m v ∈ finiteParts m := by
  constructor
  · intro n hn
    exact fromCoefficients_outside m v n (Or.inl hn)
  · intro n hn
    exact fromCoefficients_outside m v n (Or.inr hn)

def finitePartsEquiv (m : ℕ) : (Fin m → ℂ) ≃ₗ[ℂ] ↥(finiteParts m) where
  toFun v := ⟨fromCoefficients m v, fromCoefficients_mem m v⟩
  invFun f i := f.val.coeff (-(i : ℤ)-1)
  left_inv v := by funext i; exact fromCoefficients_at m v i
  right_inv f := by
    apply Subtype.ext
    ext n
    by_cases hn : n < -(m : ℤ) ∨ 0 ≤ n
    · rw [fromCoefficients_outside m _ n hn]
      rcases hn with hn | hn
      · exact (f.property.1 n hn).symm
      · exact (f.property.2 n hn).symm
    · let i : Fin m := ⟨(-n-1).toNat, by omega⟩
      have heq : -(i : ℤ)-1 = n := by dsimp [i]; omega
      rw [← heq, fromCoefficients_at]
  map_add' v w := by apply Subtype.ext; exact (fromCoefficients m).map_add _ _
  map_smul' c v := by apply Subtype.ext; exact (fromCoefficients m).map_smul c _

theorem finiteParts_finrank (m : ℕ) : Module.finrank ℂ (finiteParts m) = m := by
  rw [← (finitePartsEquiv m).finrank_eq, Module.finrank_fin_fun]

#print axioms quotientEquivPrincipalParts
#print axioms principalPart_ker
#print axioms principalPart_derivative
#print axioms finitePartsEquiv
#print axioms finiteParts_finrank

end Problem32.PrincipalParts
