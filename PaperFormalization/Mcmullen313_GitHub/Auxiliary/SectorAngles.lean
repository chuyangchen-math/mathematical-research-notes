
import SectorGluing

namespace McMullen313

/-!
# Weighted Sector Angles

The angle of a sector may depend on its state.

For a sector cycle of minimal period L(s), define

  totalAngle(s) =
    sum_{j = 0}^{L(s)-1} angle(T^j(s)).

We prove that this sum is positive when each
individual angle is positive, and that it is
invariant under the transition T.

No uniform-angle assumption is made.
-/

/-! ## 1. Gluing with nonuniform corner angles -/

structure AngledGluing (n m k : Nat) where

  gluing : SectorGluing n m k

  angle :
    SectorState n m k → ℝ

  angle_pos :
    ∀ s, 0 < angle s

/-! ## 2. Total angle along a minimal cycle -/

noncomputable def totalConeAngle
    {n m k : Nat}
    (A : AngledGluing n m k)
    (s : SectorState n m k) : ℝ :=

  ∑ j ∈ Finset.range
      (gluingPeriod A.gluing s),
    A.angle
      (iterate
        (asSectorSystem A.gluing) j s)

/-! ## 3. Positivity of the total angle -/

theorem totalConeAngle_positive
    {n m k : Nat}
    (A : AngledGluing n m k)
    (s : SectorState n m k) :
    0 < totalConeAngle A s := by

  unfold totalConeAngle

  apply Finset.sum_pos

  · intro j hj
    exact A.angle_pos _

  · refine ⟨0, Finset.mem_range.mpr ?_⟩
    exact gluingPeriod_positive A.gluing s

/-!
## 4. A general cyclic-sum identity

If T^r(s) = s, then summing an arbitrary
weight over r consecutive states does not
depend on whether the sum starts at s or T(s).
-/

theorem sum_iterate_next
    {n m k : Nat}
    (S : SectorSystem n m k)
    (weight : SectorState n m k → ℝ)
    (s : SectorState n m k)
    (r : Nat)
    (hreturn : iterate S r s = s) :

    (∑ j ∈ Finset.range r,
      weight (iterate S j (S.next s))) =

    (∑ j ∈ Finset.range r,
      weight (iterate S j s)) := by

  let f : Nat → ℝ :=
    fun j => weight (iterate S j s)

  have hshift (j : Nat) :
      weight (iterate S j (S.next s)) =
        f (j + 1) := by

    dsimp [f]

    rw [iterate_next]

    rfl

  have hlast : f r = f 0 := by

    dsimp [f]

    rw [hreturn]

    rfl

  have hrotation :
      (∑ j ∈ Finset.range r, f (j + 1)) =
        (∑ j ∈ Finset.range r, f j) := by

    have h :
        (∑ j ∈ Finset.range r, f (j + 1))
          + f 0 =
        (∑ j ∈ Finset.range r, f j)
          + f 0 := by

      calc

        (∑ j ∈ Finset.range r, f (j + 1))
            + f 0 =

            (∑ j ∈ Finset.range (r + 1), f j) :=
          (Finset.sum_range_succ' f r).symm

        _ = (∑ j ∈ Finset.range r, f j)
              + f r :=
          Finset.sum_range_succ f r

        _ = (∑ j ∈ Finset.range r, f j)
              + f 0 := by
          rw [hlast]

    exact add_right_cancel h

  calc

    (∑ j ∈ Finset.range r,
      weight (iterate S j (S.next s))) =

      (∑ j ∈ Finset.range r,
        f (j + 1)) := by

        apply Finset.sum_congr rfl

        intro j hj

        exact hshift j

    _ = (∑ j ∈ Finset.range r, f j) :=
      hrotation

    _ = (∑ j ∈ Finset.range r,
          weight (iterate S j s)) := by
      rfl

/-! ## 5. Invariance of the total cone angle -/

theorem totalConeAngle_invariant
    {n m k : Nat}
    (A : AngledGluing n m k)
    (s : SectorState n m k) :

    totalConeAngle A
      (gluingNext A.gluing s) =
    totalConeAngle A s := by

  unfold totalConeAngle

  rw [gluingPeriod_invariant A.gluing s]

  exact
    sum_iterate_next
      (asSectorSystem A.gluing)
      A.angle
      s
      (gluingPeriod A.gluing s)
      (gluingPeriod_return A.gluing s)

/-! ## 6. Invariance under any number of steps -/

theorem totalConeAngle_iterate
    {n m k : Nat}
    (A : AngledGluing n m k)
    (t : Nat)
    (s : SectorState n m k) :

    totalConeAngle A
      (iterate (asSectorSystem A.gluing) t s) =
    totalConeAngle A s := by

  induction t with

  | zero =>
      rfl

  | succ t ih =>

      calc

        totalConeAngle A
          (iterate
            (asSectorSystem A.gluing)
            (t + 1) s) =

          totalConeAngle A
            (gluingNext A.gluing
              (iterate
                (asSectorSystem A.gluing)
                t s)) := by
            rfl

        _ =
          totalConeAngle A
            (iterate
              (asSectorSystem A.gluing)
              t s) :=
          totalConeAngle_invariant A _

        _ = totalConeAngle A s :=
          ih

/-! ## 7. Recovery of the uniform-angle formula -/

theorem totalConeAngle_of_constant
    {n m k : Nat}
    (A : AngledGluing n m k)
    (a : ℝ)
    (ha : ∀ s, A.angle s = a)
    (s : SectorState n m k) :

    totalConeAngle A s =
      uniformConeAngle A.gluing a s := by

  simp [totalConeAngle, uniformConeAngle,
        ha, nsmul_eq_mul]

/-! ## 8. Upper bound from individual angles -/

theorem totalConeAngle_le
    {n m k : Nat}
    (A : AngledGluing n m k)
    (b : ℝ)
    (hb : ∀ s, A.angle s ≤ b)
    (s : SectorState n m k) :

    totalConeAngle A s ≤
      (gluingPeriod A.gluing s : ℝ) * b := by

  unfold totalConeAngle

  calc

    (∑ j ∈ Finset.range
      (gluingPeriod A.gluing s),
      A.angle
        (iterate
          (asSectorSystem A.gluing) j s)) ≤

      (∑ _j ∈ Finset.range
        (gluingPeriod A.gluing s), b) := by

        apply Finset.sum_le_sum

        intro j hj

        exact hb _

    _ = (gluingPeriod A.gluing s : ℝ) * b := by
      simp [nsmul_eq_mul]

/-! ## 9. Lower bound from individual angles -/

theorem totalConeAngle_ge
    {n m k : Nat}
    (A : AngledGluing n m k)
    (a : ℝ)
    (ha : ∀ s, a ≤ A.angle s)
    (s : SectorState n m k) :

    (gluingPeriod A.gluing s : ℝ) * a ≤
      totalConeAngle A s := by

  unfold totalConeAngle

  calc

    (gluingPeriod A.gluing s : ℝ) * a =

      (∑ _j ∈ Finset.range
        (gluingPeriod A.gluing s), a) := by
      simp [nsmul_eq_mul]

    _ ≤

      (∑ j ∈ Finset.range
        (gluingPeriod A.gluing s),
        A.angle
          (iterate
            (asSectorSystem A.gluing) j s)) := by

      apply Finset.sum_le_sum

      intro j hj

      exact ha _

end McMullen313
