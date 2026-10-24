import PaperPeriodComparison
import GeometricAlgebra

noncomputable section
namespace Problem32.PaperAntiPeriod
open Problem32.GeometricAlgebra Problem32.PaperPeriodComparison
variable {V W H : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup H] [Module ℂ H]

def antiMap (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W) (f : V →ₗ[ℂ] W)
    (equivariant : ∀ x, f (s x) = t (f x)) : antiSpace s →ₗ[ℂ] antiSpace t where
  toFun x := ⟨f x.val, by change t (f x.val) = -f x.val; rw [← equivariant, x.property, map_neg]⟩
  map_add' x y := Subtype.ext (f.map_add _ _)
  map_smul' c x := Subtype.ext (f.map_smul c _)

theorem anti_preimage (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W) (f : V →ₗ[ℂ] W)
    (hs : ∀ x, s (s x) = x) (equivariant : ∀ x, f (s x) = t (f x))
    (y : antiSpace t) (x : V) (hx : f x = y.val) :
    antiMap s t f equivariant (minusProjection s hs x) = y := by
  apply Subtype.ext
  change f ((2 : ℂ)⁻¹ • (x-s x)) = y.val
  rw [map_smul, map_sub, equivariant, hx, y.property, sub_neg_eq_add, ← two_smul ℂ y.val]
  rw [smul_smul]
  norm_num

theorem anti_surjective (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W) (f : V →ₗ[ℂ] W)
    (hs : ∀ x, s (s x) = x) (equivariant : ∀ x, f (s x) = t (f x))
    (surjective : Function.Surjective f) : Function.Surjective (antiMap s t f equivariant) := by
  intro y
  obtain ⟨x, hx⟩ := surjective y.val
  exact ⟨minusProjection s hs x, anti_preimage s t f hs equivariant y x hx⟩

theorem anti_exact (s : V →ₗ[ℂ] V) (t : W →ₗ[ℂ] W)
    (f : V →ₗ[ℂ] W) (delta : W →ₗ[ℂ] H)
    (hs : ∀ x, s (s x) = x) (equivariant : ∀ x, f (s x) = t (f x))
    (exactness : LinearMap.ker delta = LinearMap.range f) :
    LinearMap.ker (delta.comp (antiSpace t).subtype) =
      LinearMap.range (antiMap s t f equivariant) := by
  ext y
  constructor
  · intro hy
    have hm : y.val ∈ LinearMap.range f := by rw [← exactness]; exact hy
    obtain ⟨x, hx⟩ := hm
    exact ⟨minusProjection s hs x, anti_preimage s t f hs equivariant y x hx⟩
  · rintro ⟨x, rfl⟩
    have hm : f x.val ∈ LinearMap.ker delta := by rw [exactness]; exact ⟨x.val, rfl⟩
    exact hm

variable {S P T C : Type*} [AddCommGroup S] [Module ℂ S]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup T] [Module ℂ T]
  [AddCommGroup C] [Module ℂ C]

/-- The anti-period quotient is constructed using anti second-kind lifts.
Its kernel agrees with the anti Mittag--Leffler kernel. Anti existence and
anti exactness are proved by averaging, not assumed as external theorems. -/
def anti_period_kernel_eq
    (s : V →ₗ[ℂ] V) (t : S →ₗ[ℂ] S) (a : P →ₗ[ℂ] P)
    (hs : ∀ x, s (s x) = x) (ht : ∀ x, t (t x) = x)
    (b : S →ₗ[ℂ] P) (d : V →ₗ[ℂ] S) (p : V →ₗ[ℂ] P)
    (period : S →ₗ[ℂ] T) (delta : P →ₗ[ℂ] C)
    (hb : ∀ x, b (t x) = a (b x)) (hd : ∀ x, d (s x) = t (d x))
    (hp : ∀ x, p (s x) = a (p x))
    (second_kind : Function.Surjective b)
    (zero_period_primitive : LinearMap.ker period = LinearMap.range d)
    (mittag_leffler : LinearMap.ker delta = LinearMap.range p)
    (local_derivative : ∀ x, b (d x) = p x) :=
  period_kernel_eq_mittag_leffler
    (antiMap t a b hb) (period.comp (antiSpace t).subtype)
    (anti_surjective t a b ht hb second_kind)
    (antiMap s t d hd) (antiMap s a p hp) (delta.comp (antiSpace a).subtype)
    (anti_exact s t d period hs hd zero_period_primitive)
    (anti_exact s a p delta hs hp mittag_leffler)
    (by intro x; apply Subtype.ext; exact local_derivative x.val)

#print axioms anti_surjective
#print axioms anti_exact
#print axioms anti_period_kernel_eq
end Problem32.PaperAntiPeriod

