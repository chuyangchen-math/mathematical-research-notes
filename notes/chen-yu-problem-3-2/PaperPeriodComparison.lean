import OverlapObstruction

/-! Section 4: the equality of the two obstruction kernels is proved here.
External inputs are second-kind existence (surjectivity of b), the ordinary
zero-period primitive theorem, and the Mittag--Leffler exact sequence.
No equality of the two kernels is an input. The compatibility b ∘ d = p
is the differentiated-principal-part identity, separately proved locally. -/
noncomputable section
namespace Problem32.PaperPeriodComparison
open Problem32.OverlapObstruction

variable {F S P T H : Type*}
  [AddCommGroup F] [Module ℂ F] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup T] [Module ℂ T]
  [AddCommGroup H] [Module ℂ H]

/-- Choose a LINEAR second-kind lift using the external existence theorem
and the already formalized splitting theorem for vector spaces. -/
def secondKindLift (b : S →ₗ[ℂ] P) (hexists : Function.Surjective b) : P →ₗ[ℂ] S :=
  Classical.choose (b.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hexists))

theorem secondKindLift_rightInverse (b : S →ₗ[ℂ] P) (hexists : Function.Surjective b)
    (x : P) : b (secondKindLift b hexists x) = x := by
  have h := Classical.choose_spec
    (b.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hexists))
  exact congrArg (fun m : P →ₗ[ℂ] P => m x) h

/-- Periods modulo periods of holomorphic differentials (ker b).
The quotient is constructed; it is not defined by the desired kernel. -/
abbrev periodObstruction (b : S →ₗ[ℂ] P) (period : S →ₗ[ℂ] T)
    (hexists : Function.Surjective b) :=
  obstruction b period (secondKindLift b hexists)

theorem period_kernel_eq_principal_range
    (b : S →ₗ[ℂ] P) (period : S →ₗ[ℂ] T) (hexists : Function.Surjective b)
    (d : F →ₗ[ℂ] S) (p : F →ₗ[ℂ] P)
    (hprimitive : LinearMap.ker period = LinearMap.range d)
    (hlocal : ∀ f, b (d f) = p f) :
    LinearMap.ker (periodObstruction b period hexists) = LinearMap.range p := by
  rw [obstruction_kernel b period (secondKindLift b hexists)
    (secondKindLift_rightInverse b hexists)]
  ext x
  constructor
  · rintro ⟨s, hs⟩
    have hmem : s.val ∈ LinearMap.range d := by rw [← hprimitive]; exact s.property
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f, ?_⟩
    change b s.val = x at hs
    rw [← hf, hlocal] at hs
    exact hs
  · rintro ⟨f, rfl⟩
    have hmem : d f ∈ LinearMap.ker period := by rw [hprimitive]; exact ⟨f, rfl⟩
    exact ⟨⟨d f, hmem⟩, hlocal f⟩

/-- The internal period/Mittag--Leffler comparison, from the two ordinary
external exactness theorems. In particular, kernel equality is not assumed. -/
theorem period_kernel_eq_mittag_leffler
    (b : S →ₗ[ℂ] P) (period : S →ₗ[ℂ] T) (hexists : Function.Surjective b)
    (d : F →ₗ[ℂ] S) (p : F →ₗ[ℂ] P) (delta : P →ₗ[ℂ] H)
    (hprimitive : LinearMap.ker period = LinearMap.range d)
    (hML : LinearMap.ker delta = LinearMap.range p)
    (hlocal : ∀ f, b (d f) = p f) :
    LinearMap.ker (periodObstruction b period hexists) = LinearMap.ker delta := by
  rw [period_kernel_eq_principal_range b period hexists d p hprimitive hlocal, hML]

/-- Restricting to any specified subspace, including anti-invariant principal
parts, preserves the equality as subspaces of the SAME ambient space. -/
theorem restricted_period_kernel_eq
    (b : S →ₗ[ℂ] P) (period : S →ₗ[ℂ] T) (hexists : Function.Surjective b)
    (d : F →ₗ[ℂ] S) (p : F →ₗ[ℂ] P) (delta : P →ₗ[ℂ] H)
    (hprimitive : LinearMap.ker period = LinearMap.range d)
    (hML : LinearMap.ker delta = LinearMap.range p)
    (hlocal : ∀ f, b (d f) = p f) (A : Submodule ℂ P) :
    A ⊓ LinearMap.ker (periodObstruction b period hexists) = A ⊓ LinearMap.ker delta := by
  rw [period_kernel_eq_mittag_leffler b period hexists d p delta hprimitive hML hlocal]

theorem period_class_independent_of_lift
    (b : S →ₗ[ℂ] P) (period : S →ₗ[ℂ] T)
    (l₁ l₂ : P →ₗ[ℂ] S) (h₁ : ∀ x, b (l₁ x) = x) (h₂ : ∀ x, b (l₂ x) = x) :
    obstruction b period l₁ = obstruction b period l₂ :=
  obstruction_independent_of_lift b period l₁ l₂ h₁ h₂

#print axioms period_kernel_eq_mittag_leffler
#print axioms restricted_period_kernel_eq
#print axioms period_class_independent_of_lift
end Problem32.PaperPeriodComparison
