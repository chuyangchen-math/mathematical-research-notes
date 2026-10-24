import Gluing

/-!
A constructed overlap-obstruction map: local lifts differ on overlaps,
and their mismatch is taken modulo mismatches of holomorphic corrections.
Its kernel is PROVED to be the image of compatible sections.

This algebraic construction is not identified here with H¹(O) on a compact
curve. A geometric instance still needs actual restriction maps, local
principal-part lifts, and the cohomological comparison.
-/

noncomputable section
namespace Problem32.OverlapObstruction

section Differences

variable {I : Type*} {V : I → Type*} {O : I → I → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i j, AddCommGroup (O i j)] [∀ i j, Module ℂ (O i j)]

def overlapDifference
    (left : ∀ i j, V i →ₗ[ℂ] O i j)
    (right : ∀ i j, V j →ₗ[ℂ] O i j) :
    ((i : I) → V i) →ₗ[ℂ] ((i j : I) → O i j) where
  toFun s i j := left i j (s i) - right i j (s j)
  map_add' s t := by
    funext i j
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c s := by
    funext i j
    simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

theorem overlapDifference_ker
    (left : ∀ i j, V i →ₗ[ℂ] O i j)
    (right : ∀ i j, V j →ₗ[ℂ] O i j) :
    LinearMap.ker (overlapDifference left right) =
      Problem32.Gluing.compatibleSections left right := by
  ext s
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    exact sub_eq_zero.mp hij
  · intro h
    funext i j
    exact sub_eq_zero.mpr (h i j)

end Differences

section Obstruction

variable {V P C : Type*}
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup P] [Module ℂ P]
  [AddCommGroup C] [Module ℂ C]

/-- Mismatches coming from changes with zero principal part. -/
def correctionMap (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) :
    LinearMap.ker q →ₗ[ℂ] C := D.comp (LinearMap.ker q).subtype

/-- The obstruction is constructed using the local lift and the difference
map, not defined as the quotient by the image of the desired global map. -/
def obstruction (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) (lift : P →ₗ[ℂ] V) :
    P →ₗ[ℂ] (C ⧸ LinearMap.range (correctionMap q D)) :=
  (LinearMap.range (correctionMap q D)).mkQ.comp (D.comp lift)

/-- Vanishing is equivalent to correcting a local lift into a compatible
section while retaining exactly the prescribed principal part. -/
theorem obstruction_zero_iff
    (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) (lift : P →ₗ[ℂ] V)
    (hlift : ∀ p, q (lift p) = p) (p : P) :
    obstruction q D lift p = 0 ↔ ∃ s : V, D s = 0 ∧ q s = p := by
  change (Submodule.Quotient.mk (D (lift p)) : C ⧸ LinearMap.range (correctionMap q D)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨h, hh⟩
    have hD : D h.val = D (lift p) := hh
    refine ⟨lift p - h.val, ?_, ?_⟩
    · rw [map_sub, hD, sub_self]
    · rw [map_sub, hlift, h.property, sub_zero]
  · rintro ⟨s, hs, hq⟩
    refine ⟨⟨lift p - s, ?_⟩, ?_⟩
    · change q (lift p - s) = 0
      rw [map_sub, hlift, hq, sub_self]
    · change D (lift p - s) = D (lift p)
      rw [map_sub, hs, sub_zero]

/-- Restrict the principal-part map to genuinely compatible sections. -/
def compatiblePrincipalMap (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) :
    LinearMap.ker D →ₗ[ℂ] P := q.comp (LinearMap.ker D).subtype

/-- Exactness at principal parts is a theorem of the construction. -/
theorem obstruction_kernel
    (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) (lift : P →ₗ[ℂ] V)
    (hlift : ∀ p, q (lift p) = p) :
    LinearMap.ker (obstruction q D lift) = LinearMap.range (compatiblePrincipalMap q D) := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hs, hq⟩ := (obstruction_zero_iff q D lift hlift p).mp hp
    exact ⟨⟨s, hs⟩, hq⟩
  · rintro ⟨s, hs⟩
    exact (obstruction_zero_iff q D lift hlift p).mpr ⟨s.val, s.property, hs⟩

/-- Changing the chosen local lift leaves the obstruction class unchanged. -/
theorem obstruction_independent_of_lift
    (q : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] C) (lift₁ lift₂ : P →ₗ[ℂ] V)
    (h₁ : ∀ p, q (lift₁ p) = p) (h₂ : ∀ p, q (lift₂ p) = p) :
    obstruction q D lift₁ = obstruction q D lift₂ := by
  apply LinearMap.ext
  intro p
  apply sub_eq_zero.mp
  change (LinearMap.range (correctionMap q D)).mkQ (D (lift₁ p)) -
    (LinearMap.range (correctionMap q D)).mkQ (D (lift₂ p)) = 0
  rw [← map_sub, ← map_sub]
  change (Submodule.Quotient.mk (D (lift₁ p - lift₂ p)) :
    C ⧸ LinearMap.range (correctionMap q D)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨lift₁ p - lift₂ p, ?_⟩, rfl⟩
  change q (lift₁ p - lift₂ p) = 0
  rw [map_sub, h₁, h₂, sub_self]

end Obstruction

#print axioms overlapDifference_ker
#print axioms obstruction_kernel
#print axioms obstruction_independent_of_lift

end Problem32.OverlapObstruction
