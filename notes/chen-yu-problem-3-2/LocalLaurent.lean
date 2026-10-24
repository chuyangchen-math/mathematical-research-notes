import Mathlib

/-!
Formal Laurent-series local models for the orientation-cover section map.
These are genuine Laurent series, not integer-only order certificates.
Convergence, geometric charts, and global gluing remain separate obligations.
-/

noncomputable section
namespace Problem32.LocalLaurent

open HahnSeries
abbrev Series := LaurentSeries ℂ

/-- Series with no terms below k; includes the zero series. -/
def bounded (k : ℤ) : Submodule ℂ Series where
  carrier := {f | ∀ n, n < k → f.coeff n = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg n hn; simp [hf n hn, hg n hn]
  smul_mem' := by intro c f hf n hn; simp [hf n hn]

@[simp] theorem mem_bounded (k : ℤ) (f : Series) :
    f ∈ bounded k ↔ ∀ n, n < k → f.coeff n = 0 := Iff.rfl

/-- The parity-supported subspace: only powers congruent to b modulo 2. -/
def paritySpace (b : ℤ) : Submodule ℂ Series where
  carrier := {f | ∀ n, (n - b) % 2 ≠ 0 → f.coeff n = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg n hn; simp [hf n hn, hg n hn]
  smul_mem' := by intro c f hf n hn; simp [hf n hn]

/-- Formal substitution and monomial multiplication: f(z) ↦ w^b f(w²). -/
def doubleShift (b : ℤ) : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.ofSuppBddBelow
    (fun n => if (n - b) % 2 = 0 then f.coeff ((n - b) / 2) else 0) (by
      refine ⟨2 * f.order + b, ?_⟩
      intro n hn
      by_contra h
      have hlt : (n - b) / 2 < f.order := by omega
      have hz := HahnSeries.coeff_eq_zero_of_lt_order hlt
      simp only [Function.mem_support] at hn
      split_ifs at hn <;> simp_all)
  map_add' f g := by
    ext n
    change (if (n-b)%2=0 then (f+g).coeff ((n-b)/2) else 0) =
      (if (n-b)%2=0 then f.coeff ((n-b)/2) else 0) +
      (if (n-b)%2=0 then g.coeff ((n-b)/2) else 0)
    split_ifs <;> simp only [HahnSeries.coeff_add, add_zero]
  map_smul' c f := by
    ext n
    change (if (n-b)%2=0 then (c • f).coeff ((n-b)/2) else 0) =
      c • (if (n-b)%2=0 then f.coeff ((n-b)/2) else 0)
    split_ifs <;> simp only [HahnSeries.coeff_smul, smul_zero]

@[simp] theorem doubleShift_coeff (b : ℤ) (f : Series) (n : ℤ) :
    (doubleShift b f).coeff n =
      if (n-b)%2=0 then f.coeff ((n-b)/2) else 0 := rfl

/-- Descent extracts the coefficients on the allowed parity. -/
def descend (b : ℤ) : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.ofSuppBddBelow (fun n => f.coeff (2*n+b)) (by
    refine ⟨(f.order-b)/2, ?_⟩
    intro n hn
    by_contra h
    have hlt : 2*n+b < f.order := by omega
    have hz := HahnSeries.coeff_eq_zero_of_lt_order hlt
    exact hn hz)
  map_add' f g := by ext n; exact HahnSeries.coeff_add
  map_smul' c f := by ext n; exact HahnSeries.coeff_smul

@[simp] theorem descend_coeff (b : ℤ) (f : Series) (n : ℤ) :
    (descend b f).coeff n = f.coeff (2*n+b) := rfl

theorem descend_doubleShift (b : ℤ) (f : Series) :
    descend b (doubleShift b f) = f := by
  ext n
  simp only [descend_coeff, doubleShift_coeff]
  have hmod : (2*n+b-b)%2=0 := by omega
  have hdiv : (2*n+b-b)/2=n := by omega
  rw [if_pos hmod, hdiv]

theorem doubleShift_descend (b : ℤ) (f : Series) (hf : f ∈ paritySpace b) :
    doubleShift b (descend b f) = f := by
  ext n
  rw [doubleShift_coeff]
  split_ifs with h
  · rw [descend_coeff]
    congr 1
    omega
  · exact (hf n h).symm

theorem doubleShift_parity (b : ℤ) (f : Series) :
    doubleShift b f ∈ paritySpace b := by
  intro n hn
  simp [hn]

theorem doubleShift_bounded (k b : ℤ) (f : Series) (hf : f ∈ bounded k) :
    doubleShift b f ∈ bounded (2*k+b) := by
  intro n hn
  rw [doubleShift_coeff]
  split_ifs with h
  · exact hf _ (by omega)
  · rfl

theorem descend_bounded (k b : ℤ) (f : Series) (hf : f ∈ bounded (2*k+b)) :
    descend b f ∈ bounded k := by
  intro n hn
  exact hf _ (by omega)

/-- The bounded local section isomorphism is constructed, including descent,
both inverse laws, and both pole-bound implications. -/
def boundedDoubleShiftEquiv (k b : ℤ) :
    ↥(bounded k) ≃ₗ[ℂ] ↥(paritySpace b ⊓ bounded (2*k+b)) where
  toFun f := ⟨doubleShift b f.val,
    doubleShift_parity b f.val, doubleShift_bounded k b f.val f.property⟩
  invFun f := ⟨descend b f.val, descend_bounded k b f.val f.property.2⟩
  left_inv f := by apply Subtype.ext; exact descend_doubleShift b f.val
  right_inv f := by apply Subtype.ext; exact doubleShift_descend b f.val f.property.1
  map_add' f g := by apply Subtype.ext; exact (doubleShift b).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (doubleShift b).map_smul c _

/-- In a ramified chart q=z^(3a)dz² and z=w², the quotient of
2 w f(w²)dw by 2 w^(3a+1)dw is w^(-3a) f(w²). -/
def ramifiedQuotient (a : ℤ) : Series →ₗ[ℂ] Series := doubleShift (-3*a)

theorem ramifiedQuotient_pole_bound (a : ℤ) (f : Series) (hf : f ∈ bounded a) :
    ramifiedQuotient a f ∈ bounded (-a) := by
  have h := doubleShift_bounded a (-3*a) f hf
  have heq : 2*a + -3*a = -a := by ring
  simpa only [ramifiedQuotient, heq] using h

theorem ramifiedQuotient_descent_bound (a : ℤ) (f : Series)
    (hf : f ∈ bounded (-a)) : descend (-3*a) f ∈ bounded a := by
  apply descend_bounded a (-3*a)
  have heq : 2*a + -3*a = -a := by ring
  simpa only [heq] using hf

/-- The local deck action f(w) ↦ f(-w), defined coefficientwise. -/
def deck : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.ofSuppBddBelow
    (fun n => if n%2=0 then f.coeff n else -f.coeff n) (by
      refine ⟨f.order, ?_⟩
      intro n hn
      by_contra h
      have hz := HahnSeries.coeff_eq_zero_of_lt_order (show n < f.order by omega)
      simp only [Function.mem_support] at hn
      split_ifs at hn <;> simp_all)
  map_add' f g := by
    ext n
    change (if n%2=0 then (f+g).coeff n else -(f+g).coeff n) =
      (if n%2=0 then f.coeff n else -f.coeff n) +
      (if n%2=0 then g.coeff n else -g.coeff n)
    split_ifs <;> simp only [HahnSeries.coeff_add] <;> ring
  map_smul' c f := by
    ext n
    change (if n%2=0 then (c • f).coeff n else -(c • f).coeff n) =
      c • (if n%2=0 then f.coeff n else -f.coeff n)
    split_ifs <;> simp only [HahnSeries.coeff_smul, smul_neg]

@[simp] theorem deck_coeff (f : Series) (n : ℤ) :
    (deck f).coeff n = if n%2=0 then f.coeff n else -f.coeff n := rfl

theorem deck_involutive (f : Series) : deck (deck f) = f := by
  ext n
  simp only [deck_coeff]
  split_ifs <;> simp

theorem parity_odd_iff_anti (b : ℤ) (hb : b%2=1) (f : Series) :
    f ∈ paritySpace b ↔ deck f = -f := by
  constructor
  · intro hf
    ext n
    rw [deck_coeff, HahnSeries.coeff_neg]
    split_ifs with h
    · have hz := hf n (by omega)
      simp [hz]
    · rfl
  · intro hf n hn
    have h := congrArg (fun g : Series => g.coeff n) hf
    have heven : n%2=0 := by omega
    simp only [deck_coeff, heven, if_true, HahnSeries.coeff_neg] at h
    linear_combination (1/2 : ℂ) * h

theorem ramifiedQuotient_anti (a : ℤ) (ha : a%2=1) (f : Series) :
    deck (ramifiedQuotient a f) = -(ramifiedQuotient a f) := by
  apply (parity_odd_iff_anti (-3*a) (by omega) _).mp
  exact doubleShift_parity (-3*a) f

/-! Unramified charts: actual multiplication by Laurent monomials. -/

def shift (b : ℤ) : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.single b (1 : ℂ) * f
  map_add' f g := mul_add _ _ _
  map_smul' c f := by
    ext n
    simp only [HahnSeries.coeff_single_mul, HahnSeries.coeff_smul, one_mul, RingHom.id_apply]

@[simp] theorem shift_coeff (b : ℤ) (f : Series) (n : ℤ) :
    (shift b f).coeff n = f.coeff (n-b) := by
  exact (HahnSeries.coeff_single_mul).trans (one_mul _)

theorem shift_bounded (k b : ℤ) (f : Series) (hf : f ∈ bounded k) :
    shift b f ∈ bounded (k+b) := by
  intro n hn
  rw [shift_coeff]
  exact hf _ (by omega)

theorem shift_neg_shift (b : ℤ) (f : Series) : shift (-b) (shift b f) = f := by
  ext n
  simp only [shift_coeff]
  congr 1
  omega

theorem shift_shift_neg (b : ℤ) (f : Series) : shift b (shift (-b) f) = f := by
  ext n
  simp only [shift_coeff]
  congr 1
  omega

def boundedShiftEquiv (k b : ℤ) : ↥(bounded k) ≃ₗ[ℂ] ↥(bounded (k+b)) where
  toFun f := ⟨shift b f.val, shift_bounded k b f.val f.property⟩
  invFun f := ⟨shift (-b) f.val, by
    have h := shift_bounded (k+b) (-b) f.val f.property
    simpa only [add_neg_cancel_right] using h⟩
  left_inv f := by apply Subtype.ext; exact shift_neg_shift b f.val
  right_inv f := by apply Subtype.ext; exact shift_shift_neg b f.val
  map_add' f g := by apply Subtype.ext; exact (shift b).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (shift b).map_smul c _

def unramifiedQuotient (a : ℤ) : Series →ₗ[ℂ] Series := shift (-3*(a/2))

theorem unramifiedQuotient_pole_bound (a : ℤ) (ha : a%2=0)
    (f : Series) (hf : f ∈ bounded a) :
    unramifiedQuotient a f ∈ bounded (-(a/2)) := by
  have h := shift_bounded a (-3*(a/2)) f hf
  have heq : a + -3*(a/2) = -(a/2) := by omega
  simpa only [unramifiedQuotient, heq] using h

theorem unramified_descent_bound (a : ℤ) (ha : a%2=0)
    (f : Series) (hf : f ∈ bounded (-(a/2))) :
    shift (3*(a/2)) f ∈ bounded a := by
  have h := shift_bounded (-(a/2)) (3*(a/2)) f hf
  have heq : -(a/2) + 3*(a/2) = a := by omega
  simpa only [heq] using h

/-! Identify the constructed ramified map with the actual quotient of
formal differential coefficients, including the Jacobian factor 2w. -/

def pullbackDifferential (f : Series) : Series := (2 : ℂ) • doubleShift 1 f
def ramifiedOmega (a : ℤ) : Series := HahnSeries.single (3*a+1) (2 : ℂ)

theorem ramifiedQuotient_mul_omega (a : ℤ) (f : Series) :
    ramifiedQuotient a f * ramifiedOmega a = pullbackDifferential f := by
  ext n
  change (doubleShift (-3*a) f * HahnSeries.single (3*a+1) (2 : ℂ)).coeff n = _
  rw [HahnSeries.coeff_mul_single, doubleShift_coeff]
  change (if (n-(3*a+1)-(-3*a))%2=0 then
      f.coeff ((n-(3*a+1)-(-3*a))/2) else 0) * 2 =
    2 * (if (n-1)%2=0 then f.coeff ((n-1)/2) else 0)
  have heq : n-(3*a+1)-(-3*a)=n-1 := by ring
  rw [heq, mul_comm]

theorem ramifiedQuotient_eq_div (a : ℤ) (f : Series) :
    ramifiedQuotient a f = pullbackDifferential f / ramifiedOmega a := by
  have hn : ramifiedOmega a ≠ 0 := by
    intro h
    have hc := congrArg (fun g : Series => g.coeff (3*a+1)) h
    norm_num [ramifiedOmega] at hc
  exact (eq_div_iff hn).mpr (ramifiedQuotient_mul_omega a f)

/-! Simple poles: anti-invariance removes the constant coefficient,
so a holomorphic anti-invariant function is divisible by w. -/

theorem odd_holomorphic_vanishes (f : Series)
    (hodd : f ∈ paritySpace 1) (hhol : f ∈ bounded 0) : f ∈ bounded 1 := by
  intro n hn
  by_cases hneg : n < 0
  · exact hhol n hneg
  · have hn0 : n = 0 := by omega
    subst n
    exact hodd 0 (by norm_num)

def simplePoleSectionEquiv :
    ↥(bounded 0) ≃ₗ[ℂ] ↥(paritySpace 1 ⊓ bounded 0) where
  toFun f := ⟨doubleShift 1 f.val, doubleShift_parity 1 f.val, by
    intro n hn
    exact doubleShift_bounded 0 1 f.val f.property n (by omega)⟩
  invFun f := ⟨descend 1 f.val, by
    have h := odd_holomorphic_vanishes f.val f.property.1 f.property.2
    exact descend_bounded 0 1 f.val h⟩
  left_inv f := by apply Subtype.ext; exact descend_doubleShift 1 f.val
  right_inv f := by apply Subtype.ext; exact doubleShift_descend 1 f.val f.property.1
  map_add' f g := by apply Subtype.ext; exact (doubleShift 1).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (doubleShift 1).map_smul c _

/-! Spin-line local eigensheaves: parity sharpens the raw pole bound. -/

theorem parity_bounded_congr (b l₁ l₂ : ℤ)
    (h : ∀ n : ℤ, (n-b)%2=0 → (n < l₁ ↔ n < l₂)) :
    paritySpace b ⊓ bounded l₁ = paritySpace b ⊓ bounded l₂ := by
  ext f
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨hp, ?_⟩
    intro n hn
    by_cases hm : (n-b)%2=0
    · exact hb n ((h n hm).mpr hn)
    · exact hp n hm
  · rintro ⟨hp, hb⟩
    refine ⟨hp, ?_⟩
    intro n hn
    by_cases hm : (n-b)%2=0
    · exact hb n ((h n hm).mp hn)
    · exact hp n hm

def boundedDoubleShiftEquivRounded (k b l : ℤ)
    (h : ∀ n : ℤ, (n-b)%2=0 → (n < 2*k+b ↔ n < l)) :
    ↥(bounded k) ≃ₗ[ℂ] ↥(paritySpace b ⊓ bounded l) := by
  rw [← parity_bounded_congr b (2*k+b) l h]
  exact boundedDoubleShiftEquiv k b

/-- m=4r+1: even Laurent sections of the spin line descend with pole ≤ r. -/
def spinInvariantFourRPlusOne (r : ℕ) :
    ↥(bounded (-(r : ℤ))) ≃ₗ[ℂ]
      ↥(paritySpace 0 ⊓ bounded (-(2*(r : ℤ)+1))) :=
  boundedDoubleShiftEquivRounded (-(r : ℤ)) 0 (-(2*(r : ℤ)+1)) (by
    intro n hn; omega)

/-- m=4r+1: dividing the pulled-back differential by omega gives exactly
the odd local spin sections, with base differential vanishing to order r. -/
def spinAntiFourRPlusOne (r : ℕ) :
    ↥(bounded (r : ℤ)) ≃ₗ[ℂ]
      ↥(paritySpace (-(4*(r : ℤ)+1)) ⊓ bounded (-(2*(r : ℤ)+1))) :=
  boundedDoubleShiftEquivRounded (r : ℤ) (-(4*(r : ℤ)+1)) (-(2*(r : ℤ)+1)) (by
    intro n hn; omega)

/-- m=4r+3: the even local sections descend with pole ≤ r+1. -/
def spinInvariantFourRPlusThree (r : ℕ) :
    ↥(bounded (-((r : ℤ)+1))) ≃ₗ[ℂ]
      ↥(paritySpace 0 ⊓ bounded (-(2*(r : ℤ)+2))) :=
  boundedDoubleShiftEquivRounded (-((r : ℤ)+1)) 0 (-(2*(r : ℤ)+2)) (by
    intro n hn; omega)

/-- m=4r+3: the forbidden even leading term is removed by odd parity;
the descended differential vanishes to order r+1. -/
def spinAntiFourRPlusThree (r : ℕ) :
    ↥(bounded ((r : ℤ)+1)) ≃ₗ[ℂ]
      ↥(paritySpace (-(4*(r : ℤ)+3)) ⊓ bounded (-(2*(r : ℤ)+2))) :=
  boundedDoubleShiftEquivRounded ((r : ℤ)+1) (-(4*(r : ℤ)+3)) (-(2*(r : ℤ)+2)) (by
    intro n hn; omega)

theorem parity_even_iff_fixed (b : ℤ) (hb : b%2=0) (f : Series) :
    f ∈ paritySpace b ↔ deck f = f := by
  constructor
  · intro hf
    ext n
    rw [deck_coeff]
    split_ifs with h
    · rfl
    · have hz := hf n (by omega)
      simp [hz]
  · intro hf n hn
    have h := congrArg (fun g : Series => g.coeff n) hf
    have hodd : n%2 ≠ 0 := by omega
    simp only [deck_coeff, hodd, if_false] at h
    linear_combination (-1/2 : ℂ) * h

/-! Local integration: the residue is exactly the obstruction to a formal
Laurent primitive. This is local, not the global period-vanishing theorem. -/

def primitive : Series →ₗ[ℂ] Series where
  toFun f := HahnSeries.ofSuppBddBelow (fun n => f.coeff (n-1) / (n : ℂ)) (by
    refine ⟨f.order+1, ?_⟩
    intro n hn
    by_contra h
    have hz := HahnSeries.coeff_eq_zero_of_lt_order (show n-1 < f.order by omega)
    exact hn (by dsimp; rw [hz, zero_div]))
  map_add' f g := by
    ext n
    change (f+g).coeff (n-1) / (n : ℂ) = f.coeff (n-1)/(n : ℂ) + g.coeff (n-1)/(n : ℂ)
    rw [HahnSeries.coeff_add, add_div]
  map_smul' c f := by
    ext n
    change (c • f).coeff (n-1) / (n : ℂ) = c • (f.coeff (n-1)/(n : ℂ))
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    ring

@[simp] theorem primitive_coeff (f : Series) (n : ℤ) :
    (primitive f).coeff n = f.coeff (n-1)/(n : ℂ) := rfl

theorem derivative_coeff (f : Series) (n : ℤ) :
    (LaurentSeries.derivative ℂ f).coeff n = ((n+1 : ℤ) : ℂ) * f.coeff (n+1) := by
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

theorem derivative_residue_zero (f : Series) :
    (LaurentSeries.derivative ℂ f).coeff (-1) = 0 := by
  rw [derivative_coeff]
  norm_num

theorem derivative_primitive (f : Series) (hf : f.coeff (-1) = 0) :
    LaurentSeries.derivative ℂ (primitive f) = f := by
  ext n
  rw [derivative_coeff, primitive_coeff]
  by_cases hn : n+1=0
  · have heq : n = -1 := by omega
    subst n
    simp [hf]
  · have hc : ((n+1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [add_sub_cancel_right]
    field_simp

theorem primitive_derivative (f : Series) (hf : f.coeff 0 = 0) :
    primitive (LaurentSeries.derivative ℂ f) = f := by
  ext n
  rw [primitive_coeff, derivative_coeff, sub_add_cancel]
  by_cases hn : n=0
  · subst n
    simp [hf]
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp

theorem exists_primitive_iff_residue_zero (f : Series) :
    (∃ g : Series, LaurentSeries.derivative ℂ g = f) ↔ f.coeff (-1) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact derivative_residue_zero g
  · intro hf
    exact ⟨primitive f, derivative_primitive f hf⟩

def zeroCoefficient (n : ℤ) : Submodule ℂ Series where
  carrier := {f | f.coeff n = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg; simp_all
  smul_mem' := by intro c f hf; simp_all

/-- A constructed isomorphism between normalized formal functions and
formal differential coefficients with zero residue. -/
def derivativeEquiv : ↥(zeroCoefficient 0) ≃ₗ[ℂ] ↥(zeroCoefficient (-1)) where
  toFun f := ⟨LaurentSeries.derivative ℂ f.val, derivative_residue_zero f.val⟩
  invFun f := ⟨primitive f.val, by change (primitive f.val).coeff 0 = 0; simp⟩
  left_inv f := by apply Subtype.ext; exact primitive_derivative f.val f.property
  right_inv f := by apply Subtype.ext; exact derivative_primitive f.val f.property
  map_add' f g := by apply Subtype.ext; exact (LaurentSeries.derivative ℂ).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (LaurentSeries.derivative ℂ).map_smul c _

theorem primitive_pole_bound (k : ℤ) (f : Series) (hf : f ∈ bounded k) :
    primitive f ∈ bounded (k+1) := by
  intro n hn
  rw [primitive_coeff, hf (n-1) (by omega), zero_div]

theorem derivative_pole_bound (k : ℤ) (f : Series) (hf : f ∈ bounded k) :
    LaurentSeries.derivative ℂ f ∈ bounded (k-1) := by
  intro n hn
  rw [derivative_coeff, hf (n+1) (by omega), mul_zero]

#print axioms boundedDoubleShiftEquiv
#print axioms ramifiedQuotient_anti
#print axioms boundedShiftEquiv
#print axioms ramifiedQuotient_eq_div
#print axioms simplePoleSectionEquiv
#print axioms spinInvariantFourRPlusOne
#print axioms spinAntiFourRPlusThree
#print axioms derivativeEquiv
#print axioms exists_primitive_iff_residue_zero

end Problem32.LocalLaurent
