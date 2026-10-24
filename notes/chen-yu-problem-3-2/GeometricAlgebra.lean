import Mathlib

/-!
Algebraic foundations for Chen--Yu Problem 3.2.

These results use actual vector spaces, linear maps and kernels. They do not
assert that a geometric orientation cover or its Mittag--Leffler sequence has
been constructed. In particular this file is NOT a full-paper formalization.
-/

namespace Problem32.GeometricAlgebra

section Eigenspaces

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def invariantSpace (t : V →ₗ[ℂ] V) : Submodule ℂ V where
  carrier := {x | t x = x}
  zero_mem' := map_zero t
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro c x hx; simp_all

def antiSpace (t : V →ₗ[ℂ] V) : Submodule ℂ V where
  carrier := {x | t x = -x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all; abel
  smul_mem' := by intro c x hx; simp_all

@[simp] theorem mem_invariantSpace (t : V →ₗ[ℂ] V) (x : V) :
    x ∈ invariantSpace t ↔ t x = x := Iff.rfl

@[simp] theorem mem_antiSpace (t : V →ₗ[ℂ] V) (x : V) :
    x ∈ antiSpace t ↔ t x = -x := Iff.rfl

theorem eq_zero_of_fixed_and_anti (t : V →ₗ[ℂ] V) (x : V)
    (hfix : t x = x) (hanti : t x = -x) : x = 0 := by
  have h : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = -x + x := congrArg (fun z => z + x) (hfix.symm.trans hanti)
      _ = 0 := neg_add_cancel x
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

end Eigenspaces

section Decomposition

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The fixed part of a vector, constructed by averaging. -/
noncomputable def plusProjection (t : V →ₗ[ℂ] V) (ht : ∀ x, t (t x) = x) :
    V →ₗ[ℂ] invariantSpace t where
  toFun x := ⟨(2 : ℂ)⁻¹ • (x + t x), by
    change t ((2 : ℂ)⁻¹ • (x + t x)) = _
    rw [map_smul, map_add, ht, add_comm]⟩
  map_add' x y := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • ((x + y) + t (x + y)) =
      (2 : ℂ)⁻¹ • (x + t x) + (2 : ℂ)⁻¹ • (y + t y)
    simp only [map_add]
    module
  map_smul' c x := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • ((c • x) + t (c • x)) =
      c • ((2 : ℂ)⁻¹ • (x + t x))
    simp only [map_smul]
    module

/-- The anti-fixed part of a vector, constructed by averaging. -/
noncomputable def minusProjection (t : V →ₗ[ℂ] V) (ht : ∀ x, t (t x) = x) :
    V →ₗ[ℂ] antiSpace t where
  toFun x := ⟨(2 : ℂ)⁻¹ • (x - t x), by
    change t ((2 : ℂ)⁻¹ • (x - t x)) = _
    rw [map_smul, map_sub, ht]
    module⟩
  map_add' x y := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • ((x + y) - t (x + y)) =
      (2 : ℂ)⁻¹ • (x - t x) + (2 : ℂ)⁻¹ • (y - t y)
    simp only [map_add]
    module
  map_smul' c x := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • ((c • x) - t (c • x)) =
      c • ((2 : ℂ)⁻¹ • (x - t x))
    simp only [map_smul]
    module

/-- Genuine direct-sum decomposition of a vector space with an involution.
No basis decomposition or section-dimension equality is assumed. -/
noncomputable def involutionDecomposition
    (t : V →ₗ[ℂ] V) (ht : ∀ x, t (t x) = x) :
    V ≃ₗ[ℂ] (invariantSpace t × antiSpace t) where
  toFun x := (plusProjection t ht x, minusProjection t ht x)
  invFun x := x.1.val + x.2.val
  left_inv x := by
    change (2 : ℂ)⁻¹ • (x + t x) + (2 : ℂ)⁻¹ • (x - t x) = x
    module
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((x.1.val + x.2.val) + t (x.1.val + x.2.val)) = x.1.val
      rw [map_add, x.1.property, x.2.property]
      module
    · apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((x.1.val + x.2.val) - t (x.1.val + x.2.val)) = x.2.val
      rw [map_add, x.1.property, x.2.property]
      module
  map_add' x y := by
    exact Prod.ext ((plusProjection t ht).map_add x y) ((minusProjection t ht).map_add x y)
  map_smul' c x := by
    exact Prod.ext ((plusProjection t ht).map_smul c x) ((minusProjection t ht).map_smul c x)

theorem involution_finrank [FiniteDimensional ℂ V]
    (t : V →ₗ[ℂ] V) (ht : ∀ x, t (t x) = x) :
    Module.finrank ℂ V = Module.finrank ℂ (invariantSpace t) +
      Module.finrank ℂ (antiSpace t) := by
  have h := (involutionDecomposition t ht).finrank_eq
  simpa only [Module.finrank_prod] using h

/-- Once the geometric Riemann--Roch identity is established for the two
eigenspaces, parity follows from the proved decomposition. The remaining
identity is deliberately visible as a hypothesis. -/
theorem spin_parity_of_eigenspace_riemann_roch [FiniteDimensional ℂ V]
    (t : V →ₗ[ℂ] V) (ht : ∀ x, t (t x) = x) (degree genus : ℤ)
    (hRR : (Module.finrank ℂ (invariantSpace t) : ℤ) -
      (Module.finrank ℂ (antiSpace t) : ℤ) = degree + 1 - genus) :
    (Module.finrank ℂ V : ℤ) % 2 = (degree + 1 - genus) % 2 := by
  have h := involution_finrank t ht
  omega

end Decomposition

section Multiplication

variable {F : Type*} [Field F] [Algebra ℂ F]

/-- Multiplication/division by a nonzero anti-invariant element exchanges
the actual fixed and anti-fixed subspaces of a field automorphism.
This proves both inverse laws instead of assuming them as structure fields.
The geometric identification of F and the pole-bounded subspaces is separate. -/
noncomputable def divideByAntiEquiv
    (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w) :
    invariantSpace t.toLinearMap ≃ₗ[ℂ] antiSpace t.toLinearMap where
  toFun x := ⟨x.val / w, by
    change t (x.val / w) = -(x.val / w)
    have hx : t x.val = x.val := x.property
    rw [map_div₀, hx, htw, div_neg]⟩
  invFun f := ⟨f.val * w, by
    change t (f.val * w) = f.val * w
    have hf : t f.val = -f.val := f.property
    rw [map_mul, hf, htw, neg_mul_neg]⟩
  left_inv x := by
    apply Subtype.ext
    exact div_mul_cancel₀ x.val hw
  right_inv f := by
    apply Subtype.ext
    exact mul_div_cancel_right₀ f.val hw
  map_add' x y := by
    apply Subtype.ext
    exact add_div x.val y.val w
  map_smul' c x := by
    apply Subtype.ext
    change (c • x.val) / w = c • (x.val / w)
    simp [Algebra.smul_def, div_eq_mul_inv, mul_assoc]

theorem divideByAnti_finrank
    (t : F ≃ₐ[ℂ] F) (w : F) (hw : w ≠ 0) (htw : t w = -w) :
    Module.finrank ℂ (invariantSpace t.toLinearMap) =
      Module.finrank ℂ (antiSpace t.toLinearMap) :=
  (divideByAntiEquiv t w hw htw).finrank_eq

end Multiplication

section ExactSequence

variable {V W H : Type*}
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  [AddCommGroup H] [Module ℂ H]

/-- The actual anti-invariant part of the kernel of a linear map. -/
def antiKernel (t : W →ₗ[ℂ] W) (d : W →ₗ[ℂ] H) : Submodule ℂ W :=
  antiSpace t ⊓ LinearMap.ker d

/-- An equivariant map restricts to the anti-invariant obstruction kernel
when the composite vanishes. -/
def antiKernelMap (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W)
    (p : V →ₗ[ℂ] W) (d : W →ₗ[ℂ] H)
    (hcomm : ∀ x, p (s x) = t (p x))
    (hzero : ∀ x, d (p x) = 0) :
    antiSpace s →ₗ[ℂ] antiKernel t d where
  toFun x := ⟨p x.val, by
    constructor
    · change t (p x.val) = -(p x.val)
      rw [← hcomm, x.property, map_neg]
    · exact hzero x.val⟩
  map_add' x y := by apply Subtype.ext; exact p.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact p.map_smul c _

/-- Exactness plus invariant kernel implies an isomorphism on the anti-part.
Surjectivity is proved by averaging (x - s x)/2. Injectivity is proved from
the fact that a vector cannot be both fixed and anti-fixed in characteristic 0.

The hypotheses are the underlying exact sequence and its equivariant action,
NOT an assumed inverse or an assumed isomorphism on the anti-part.
Their geometric instantiation remains to be constructed. -/
noncomputable def antiKernelEquiv
    (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W)
    (p : V →ₗ[ℂ] W) (d : W →ₗ[ℂ] H)
    (hs : ∀ x, s (s x) = x)
    (hcomm : ∀ x, p (s x) = t (p x))
    (hexact : LinearMap.range p = LinearMap.ker d)
    (hfixed : ∀ x, p x = 0 → s x = x) :
    antiSpace s ≃ₗ[ℂ] antiKernel t d := by
  have hzero : ∀ x, d (p x) = 0 := by
    intro x
    have h : p x ∈ LinearMap.range p := ⟨x, rfl⟩
    rw [hexact] at h
    exact h
  apply LinearEquiv.ofBijective (antiKernelMap s t p d hcomm hzero)
  constructor
  · intro x y hxy
    have heq : p x.val = p y.val := congrArg Subtype.val hxy
    have hp : p (x.val - y.val) = 0 := by rw [map_sub, heq, sub_self]
    have hanti : s (x.val - y.val) = -(x.val - y.val) := by
      rw [map_sub, x.property, y.property]
      abel
    have hz := eq_zero_of_fixed_and_anti s (x.val - y.val)
      (hfixed _ hp) hanti
    exact Subtype.ext (sub_eq_zero.mp hz)
  · intro y
    have hy : y.val ∈ LinearMap.range p := by
      rw [hexact]
      exact y.property.2
    obtain ⟨x, hx⟩ := hy
    let z : V := (2 : ℂ)⁻¹ • (x - s x)
    have hz : s z = -z := by
      dsimp [z]
      rw [map_smul, map_sub, hs]
      rw [← smul_neg]
      congr 1
      abel
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    change p z = y.val
    dsimp [z]
    rw [map_smul, map_sub, hcomm, hx]
    have hyanti : t y.val = -y.val := y.property.1
    rw [hyanti, sub_neg_eq_add]
    calc
      (2 : ℂ)⁻¹ • (y.val + y.val) =
          (2 : ℂ)⁻¹ • ((2 : ℂ) • y.val) := by rw [two_smul]
      _ = y.val := by rw [smul_smul]; norm_num

theorem antiKernel_finrank
    (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W)
    (p : V →ₗ[ℂ] W) (d : W →ₗ[ℂ] H)
    (hs : ∀ x, s (s x) = x)
    (hcomm : ∀ x, p (s x) = t (p x))
    (hexact : LinearMap.range p = LinearMap.ker d)
    (hfixed : ∀ x, p x = 0 → s x = x) :
    Module.finrank ℂ (antiSpace s) = Module.finrank ℂ (antiKernel t d) :=
  (antiKernelEquiv s t p d hs hcomm hexact hfixed).finrank_eq

end ExactSequence

section Rank

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V]

/-- Rank-nullity for an actual linear map, not an input numerical identity. -/
theorem rank_nullity (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f) =
      Module.finrank ℂ V := f.finrank_range_add_finrank_ker

theorem full_rank_iff_kernel_dimension_zero (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ V ↔
      Module.finrank ℂ (LinearMap.ker f) = 0 := by
  have h := rank_nullity f
  omega

theorem corank_one_iff_kernel_dimension_one (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ (LinearMap.range f) + 1 = Module.finrank ℂ V ↔
      Module.finrank ℂ (LinearMap.ker f) = 1 := by
  have h := rank_nullity f
  omega

end Rank

#print axioms divideByAntiEquiv
#print axioms involutionDecomposition
#print axioms antiKernelEquiv
#print axioms rank_nullity

end Problem32.GeometricAlgebra
