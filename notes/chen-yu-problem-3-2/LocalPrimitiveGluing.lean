import LocalLaurent
import PrincipalParts
import OverlapObstruction

/-! Formal local primitives and their gluing obstruction. The correction space
is proved to consist of chartwise constants. The obstruction has not been
identified with integration over topological cycles on a compact curve. -/
noncomputable section
namespace Problem32.LocalPrimitiveGluing
open Problem32.LocalLaurent Problem32.OverlapObstruction Problem32.PrincipalParts

/-- Integrating a differential with prescribed differentiated principal part
recovers that principal part exactly: the integration constant cannot alter it. -/
theorem primitive_recovers_principalPart (f p : Series)
    (hp : p ∈ Problem32.PrincipalParts.negative) :
    Problem32.PrincipalParts.principalPart (LaurentSeries.derivative ℂ f) =
      LaurentSeries.derivative ℂ p ↔ Problem32.PrincipalParts.principalPart f = p := by
  constructor
  · intro h
    rw [principalPart_derivative] at h
    calc
      principalPart f = primitive (LaurentSeries.derivative ℂ (principalPart f)) :=
        (primitive_derivative _ (principalPart_negative f 0 (by omega))).symm
      _ = primitive (LaurentSeries.derivative ℂ p) := congrArg primitive h
      _ = p := primitive_derivative p (hp 0 (by omega))
  · intro h
    rw [principalPart_derivative, h]

theorem derivative_zero_iff_constant (f : Series) :
    LaurentSeries.derivative ℂ f = 0 ↔
      f = HahnSeries.single 0 (f.coeff 0) := by
  constructor
  · intro hf
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · have h := congrArg (fun g : Series => g.coeff (n-1)) hf
      rw [derivative_coeff, sub_add_cancel, HahnSeries.coeff_zero] at h
      have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hz : f.coeff n = 0 := (mul_eq_zero.mp h).resolve_left hc
      rw [hz, HahnSeries.coeff_single_of_ne hn]
  · intro hf
    ext n
    rw [derivative_coeff, hf, HahnSeries.coeff_zero]
    by_cases hn : n+1 = 0
    · rw [hn]; simp
    · rw [HahnSeries.coeff_single_of_ne hn, mul_zero]

theorem same_derivative_iff_constant_difference (f g : Series) :
    LaurentSeries.derivative ℂ f = LaurentSeries.derivative ℂ g ↔
      f-g = HahnSeries.single 0 ((f-g).coeff 0) := by
  rw [← sub_eq_zero, ← map_sub, derivative_zero_iff_constant]

variable {I : Type*}

def differential : (I → Series) →ₗ[ℂ] (I → zeroCoefficient (-1)) where
  toFun f i := ⟨LaurentSeries.derivative ℂ (f i), derivative_residue_zero (f i)⟩
  map_add' f g := by funext i; apply Subtype.ext; exact (LaurentSeries.derivative ℂ).map_add _ _
  map_smul' c f := by funext i; apply Subtype.ext; exact (LaurentSeries.derivative ℂ).map_smul _ _

def integrate : (I → zeroCoefficient (-1)) →ₗ[ℂ] (I → Series) where
  toFun w i := primitive (w i).val
  map_add' w v := by funext i; exact primitive.map_add _ _
  map_smul' c w := by funext i; exact primitive.map_smul _ _

theorem integrate_rightInverse (w : I → zeroCoefficient (-1)) :
    differential (integrate w) = w := by
  funext i
  apply Subtype.ext
  exact derivative_primitive (w i).val (w i).property

theorem differential_kernel (f : I → Series) :
    differential f = 0 ↔ ∀ i, f i = HahnSeries.single 0 ((f i).coeff 0) := by
  constructor
  · intro hf i
    apply (derivative_zero_iff_constant (f i)).mp
    exact congrArg Subtype.val (congrFun hf i)
  · intro hf
    funext i
    apply Subtype.ext
    exact (derivative_zero_iff_constant (f i)).mpr (hf i)

variable {C : Type*} [AddCommGroup C] [Module ℂ C]

/-- Differences of normalized local primitives, modulo differences of constants. -/
abbrev primitiveObstruction (D : (I → Series) →ₗ[ℂ] C) :=
  obstruction (V := I → Series) (P := I → zeroCoefficient (-1)) (C := C)
    (differential (I := I)) D (integrate (I := I))

/-- Exactness follows from the explicit Laurent primitive, not an assumed
global existence theorem. D is still supplied overlap data. -/
def primitiveObstruction_zero_iff (D : (I → Series) →ₗ[ℂ] C)
    (w : I → zeroCoefficient (-1)) :=
  obstruction_zero_iff (V := I → Series) (P := I → zeroCoefficient (-1)) (C := C)
    (differential (I := I)) D (integrate (I := I))
    (integrate_rightInverse (I := I)) w

def primitiveObstruction_kernel (D : (I → Series) →ₗ[ℂ] C) :=
  obstruction_kernel (V := I → Series) (P := I → zeroCoefficient (-1)) (C := C)
    (differential (I := I)) D (integrate (I := I))
    (integrate_rightInverse (I := I))

/-- A concrete criterion: adjust the normalized primitives by one constant
on each chart until all supplied overlap differences vanish. -/
theorem zero_iff_constant_correction (D : (I → Series) →ₗ[ℂ] C)
    (w : I → zeroCoefficient (-1)) :
    primitiveObstruction (I := I) D w = 0 ↔
      ∃ c : I → ℂ, D (integrate w - fun i => HahnSeries.single 0 (c i)) = 0 := by
  constructor
  · intro hw
    obtain ⟨f, hf, hdf⟩ := (primitiveObstruction_zero_iff D w).mp hw
    have hk : differential (integrate w - f) = 0 := by
      rw [map_sub, integrate_rightInverse, hdf]
      funext i
      apply Subtype.ext
      exact sub_self ((w i).val)
    have hc := (differential_kernel (integrate w - f)).mp hk
    refine ⟨fun i => ((integrate w - f) i).coeff 0, ?_⟩
    have heq : (fun i => HahnSeries.single 0 (((integrate w - f) i).coeff 0)) =
        integrate w - f := by funext i; exact (hc i).symm
    rw [heq, sub_sub_cancel, hf]
  · rintro ⟨c, hc⟩
    apply (primitiveObstruction_zero_iff D w).mpr
    refine ⟨integrate w - (fun i => HahnSeries.single 0 (c i)), hc, ?_⟩
    have hk : differential (fun i => HahnSeries.single 0 (c i)) = 0 := by
      apply (differential_kernel _).mpr
      intro i
      simp
    rw [map_sub, integrate_rightInverse, hk]
    funext i
    apply Subtype.ext
    exact sub_zero ((w i).val)

#print axioms derivative_zero_iff_constant
#print axioms primitive_recovers_principalPart
#print axioms differential_kernel
#print axioms primitiveObstruction_zero_iff
#print axioms primitiveObstruction_kernel
#print axioms zero_iff_constant_correction
end Problem32.LocalPrimitiveGluing
