import Mathlib

/-!
# Mazur–Orlicz Problem 20.1 — strict formalization, stage 2

This stage contains only unconditional Lean mathematics.  In particular there is
no `axiom`, `sorry`, `admit`, custom theorem interface, or typeclass standing for
Bertini or for the desired lower bounds.

Purpose of this stage:
* keep the actual linear-restriction definition from Stage 1;
* prove that restriction along a linear frame preserves homogeneity;
* isolate a uniform cubic witness shape;
* prove that every two-parameter restriction of the cubic witness is a binary
  homogeneous cubic;
* identify every binary homogeneous cubic with the homogenization of its
  dehomogenization `q(X,1)`;
* record the exact root-to-linear-factor bridge that will close the real/complex
  binary-cubic argument in the next stage.

This file does NOT claim the full Problem 20.1 theorem yet.  The remaining hard
items are:
1. close the binary homogeneous cubic reducibility lemma over `ℝ` and `ℂ`;
2. formalize the 2-variable witness `x^2 + y^3`;
3. replace the Stage-1 fixed-point Bertini axiom by a genuine theorem.
-/

namespace PaperFormalization
namespace MazurOrlicz20_1
namespace StrictStage2

noncomputable section

abbrev Poly (K : Type*) [CommSemiring K] (n : ℕ) :=
  MvPolynomial (Fin n) K

abbrev Frame (K : Type*) (n k : ℕ) :=
  Matrix (Fin n) (Fin k) K

def restrictHom
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (A : Frame K n k) : Poly K n →ₐ[K] Poly K k :=
  MvPolynomial.bind₁ A.toMvPolynomial

def restrictLinear
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (f : Poly K n) (A : Frame K n k) : Poly K k :=
  restrictHom A f

/-- Restriction is literally evaluation of the ambient variables at the linear
forms represented by the rows of `A`. -/
lemma restrictLinear_eq_aeval
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (f : Poly K n) (A : Frame K n k) :
    restrictLinear f A = (MvPolynomial.aeval A.toMvPolynomial) f := by
  rfl

/-- Every row of a frame is a homogeneous linear form. -/
lemma frameRow_isHomogeneous
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (A : Frame K n k) (i : Fin n) :
    (A.toMvPolynomial i).IsHomogeneous 1 := by
  exact Matrix.toMvPolynomial_isHomogeneous A i

/-- Linear restriction preserves the homogeneous degree. -/
lemma restrictLinear_isHomogeneous
    {K : Type*} [CommSemiring K] {n k d : ℕ}
    (f : Poly K n) (A : Frame K n k)
    (hf : f.IsHomogeneous d) :
    (restrictLinear f A).IsHomogeneous d := by
  rw [restrictLinear_eq_aeval]
  simpa using
    hf.aeval A.toMvPolynomial
      (fun i => frameRow_isHomogeneous A i)


/-- Coefficient maps do not increase total degree. -/
lemma totalDegree_map_le'
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    {σ : Type*}
    (φ : R →+* S)
    (p : MvPolynomial σ R) :
    (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree := by
  exact
    MvPolynomial.totalDegree_le_of_support_subset
      (MvPolynomial.support_map_subset φ p)

/-- Substitution of homogeneous linear forms does not increase total degree. -/
lemma restrictLinear_totalDegree_le
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (f : Poly K n) (A : Frame K n k) :
    (restrictLinear f A).totalDegree ≤ f.totalDegree := by
  classical
  calc
    (restrictLinear f A).totalDegree =
        (restrictLinear
          (∑ i ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.homogeneousComponent i f) A).totalDegree := by
          rw [MvPolynomial.sum_homogeneousComponent]
    _ =
        (∑ i ∈ Finset.range (f.totalDegree + 1),
          restrictLinear
            (MvPolynomial.homogeneousComponent i f) A).totalDegree := by
          simp [restrictLinear, restrictHom]
    _ ≤ f.totalDegree := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i hi
      have hi' : i ≤ f.totalDegree := by
        simp only [Finset.mem_range] at hi
        omega
      exact
        (restrictLinear_isHomogeneous
          (MvPolynomial.homogeneousComponent i f) A
          (MvPolynomial.homogeneousComponent_isHomogeneous i f)).totalDegree_le.trans
          hi'

/-- The three distinguished ambient indices used by the cubic witness. -/
def idx0 {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩
def idx1 {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨1, by omega⟩
def idx2 {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨2, by omega⟩

@[simp] lemma idx0_val {n : ℕ} (hn : 3 ≤ n) : (idx0 hn).val = 0 := rfl
@[simp] lemma idx1_val {n : ℕ} (hn : 3 ≤ n) : (idx1 hn).val = 1 := rfl
@[simp] lemma idx2_val {n : ℕ} (hn : 3 ≤ n) : (idx2 hn).val = 2 := rfl

lemma idx0_ne_idx1 {n : ℕ} (hn : 3 ≤ n) : idx0 hn ≠ idx1 hn := by
  intro h
  have := congrArg Fin.val h
  omega

lemma idx0_ne_idx2 {n : ℕ} (hn : 3 ≤ n) : idx0 hn ≠ idx2 hn := by
  intro h
  have := congrArg Fin.val h
  omega

lemma idx1_ne_idx2 {n : ℕ} (hn : 3 ≤ n) : idx1 hn ≠ idx2 hn := by
  intro h
  have := congrArg Fin.val h
  omega

/-- Uniform high-dimensional lower-bound candidate:
`X₀² X₂ + X₁³`.

The mathematical point is that it is an irreducible cubic, while every
two-dimensional restriction is a binary homogeneous cubic.  This witness works
for both `ℝ` and `ℂ`; the irreducibility proof will use
`MvPolynomial.irreducible_mul_X_add`.
-/
def cubicWitness
    (K : Type*) [CommRing K]
    {n : ℕ} (hn : 3 ≤ n) : Poly K n :=
  MvPolynomial.X (idx0 hn) ^ 2 * MvPolynomial.X (idx2 hn) +
    MvPolynomial.X (idx1 hn) ^ 3

/-- The witness is homogeneous of degree three. -/
lemma cubicWitness_isHomogeneous
    {K : Type*} [CommRing K]
    {n : ℕ} (hn : 3 ≤ n) :
    (cubicWitness K hn).IsHomogeneous 3 := by
  unfold cubicWitness
  have h0 :
      (MvPolynomial.X (idx0 hn) ^ 2 : Poly K n).IsHomogeneous 2 := by
    simpa using MvPolynomial.isHomogeneous_X_pow
      (R := K) (idx0 hn) 2
  have h2 :
      (MvPolynomial.X (idx2 hn) : Poly K n).IsHomogeneous 1 := by
    exact MvPolynomial.isHomogeneous_X
  have h02 :
      (MvPolynomial.X (idx0 hn) ^ 2 *
          MvPolynomial.X (idx2 hn) : Poly K n).IsHomogeneous 3 := by
    simpa using h0.mul h2
  have h1 :
      (MvPolynomial.X (idx1 hn) ^ 3 : Poly K n).IsHomogeneous 3 := by
    simpa using MvPolynomial.isHomogeneous_X_pow
      (R := K) (idx1 hn) 3
  exact h02.add h1

/-- Every restriction of the witness to two parameters is a binary homogeneous
cubic.  No irreducibility statement is used here. -/
lemma restrict_cubicWitness_two_isHomogeneous
    {K : Type*} [CommRing K]
    {n : ℕ} (hn : 3 ≤ n)
    (A : Frame K n 2) :
    (restrictLinear (cubicWitness K hn) A).IsHomogeneous 3 := by
  exact restrictLinear_isHomogeneous
    (cubicWitness K hn) A (cubicWitness_isHomogeneous hn)

/-- Dehomogenize a binary homogeneous form by setting the second variable equal
to `1`, leaving the first variable as the univariate polynomial variable. -/
def dehom2
    {K : Type*} [CommSemiring K]
    (q : Poly K 2) : Polynomial K :=
  (MvPolynomial.aeval ![Polynomial.X, 1]) q

/-- A binary homogeneous form is recovered exactly by homogenizing its
dehomogenization back to the same degree. -/
lemma homogenize_dehom2_eq
    {K : Type*} [CommSemiring K]
    {d : ℕ} {q : Poly K 2}
    (hq : q.IsHomogeneous d) :
    (dehom2 q).homogenize d = q := by
  apply Polynomial.homogenize_eq_of_isHomogeneous hq
  rfl

/-- In particular every two-dimensional restriction of the cubic witness is
the degree-three homogenization of an ordinary one-variable polynomial. -/
lemma restrict_cubicWitness_two_eq_homogenize
    {K : Type*} [CommRing K]
    {n : ℕ} (hn : 3 ≤ n)
    (A : Frame K n 2) :
    (dehom2 (restrictLinear (cubicWitness K hn) A)).homogenize 3 =
      restrictLinear (cubicWitness K hn) A := by
  exact homogenize_dehom2_eq
    (restrict_cubicWitness_two_isHomogeneous hn A)

/-- A root of a univariate polynomial produces the expected linear divisor.
This is the exact algebraic bridge needed after applying the real-closed or
algebraically-closed root theorem. -/
lemma X_sub_C_dvd_of_isRoot
    {K : Type*} [CommRing K]
    {p : Polynomial K} {r : K}
    (hr : p.IsRoot r) :
    Polynomial.X - Polynomial.C r ∣ p := by
  exact Polynomial.dvd_iff_isRoot.mpr hr

/-- Homogenization transports that linear divisibility into the binary
homogeneous ring (at the natural degrees). -/
lemma homogenized_linear_dvd_of_isRoot
    {K : Type*} [CommRing K] [IsDomain K]
    {p : Polynomial K} {r : K}
    (hr : p.IsRoot r) :
    (Polynomial.X - Polynomial.C r).homogenize
        (Polynomial.X - Polynomial.C r).natDegree ∣
      p.homogenize p.natDegree := by
  exact Polynomial.homogenize_dvd (X_sub_C_dvd_of_isRoot hr)


/-! ## Stage 3: close the high-dimensional two-plane lower bound -/

/-- A single coordinate variable is irreducible over a field.

We prove this from the total-degree-one criterion rather than introducing a
separate polynomial-ring equivalence. -/
lemma irreducible_X
    {K : Type*} [Field K]
    {σ : Type*} (i : σ) :
    Irreducible (MvPolynomial.X i : MvPolynomial σ K) := by
  classical
  apply MvPolynomial.irreducible_of_totalDegree_eq_one
  · simp
  · intro a ha
    apply isUnit_of_dvd_one
    simpa using ha (Finsupp.single i 1)

/-- Distinct coordinate variables do not divide one another.

The proof is deliberately elementary: evaluate `X_i` at `0`, every other
variable at `1`, and a hypothetical divisibility `X_i ∣ X_j` would give
`1 = 0`. -/
lemma X_not_dvd_X_of_ne
    {K : Type*} [Field K]
    {σ : Type*} {i j : σ} (hij : i ≠ j) :
    ¬ (MvPolynomial.X i : MvPolynomial σ K) ∣ MvPolynomial.X j := by
  classical
  intro h
  rcases h with ⟨q, hq⟩
  let v : σ → K := fun k => if k = i then 0 else 1
  have hv := congrArg (MvPolynomial.eval v) hq
  have h10 : (1 : K) = 0 := by
    simpa [v, hij, Ne.symm hij] using hv
  exact one_ne_zero h10

/-- Distinct coordinate variables are relatively prime. -/
lemma isRelPrime_X_X_of_ne
    {K : Type*} [Field K]
    {σ : Type*} {i j : σ} (hij : i ≠ j) :
    IsRelPrime (MvPolynomial.X i : MvPolynomial σ K)
      (MvPolynomial.X j) := by
  exact (irreducible_X (K := K) i).isRelPrime_iff_not_dvd.mpr
    (X_not_dvd_X_of_ne (K := K) hij)

/-- Powers of two distinct coordinate variables remain relatively prime. -/
lemma isRelPrime_X_pow_X_pow_of_ne
    {K : Type*} [Field K]
    {σ : Type*} {i j : σ} (hij : i ≠ j) (a b : ℕ) :
    IsRelPrime
      ((MvPolynomial.X i : MvPolynomial σ K) ^ a)
      ((MvPolynomial.X j : MvPolynomial σ K) ^ b) := by
  exact (isRelPrime_X_X_of_ne (K := K) hij).pow

/-- The uniform cubic witness `X₀² X₂ + X₁³` is irreducible over every field. -/
lemma cubicWitness_irreducible
    {K : Type*} [Field K]
    {n : ℕ} (hn : 3 ≤ n) :
    Irreducible (cubicWitness K hn) := by
  classical
  unfold cubicWitness
  apply MvPolynomial.irreducible_mul_X_add
      (MvPolynomial.X (idx0 hn) ^ 2)
      (MvPolynomial.X (idx1 hn) ^ 3)
      (idx2 hn)
  · simp
  · intro h
    have h' :
        idx2 hn ∈
          (MvPolynomial.X (idx0 hn) : Poly K n).vars :=
      (MvPolynomial.vars_pow
        (MvPolynomial.X (idx0 hn) : Poly K n) 2) h
    simpa [MvPolynomial.vars_X, idx0_ne_idx2 hn,
      Ne.symm (idx0_ne_idx2 hn)] using h'
  · intro h
    have h' :
        idx2 hn ∈
          (MvPolynomial.X (idx1 hn) : Poly K n).vars :=
      (MvPolynomial.vars_pow
        (MvPolynomial.X (idx1 hn) : Poly K n) 3) h
    simpa [MvPolynomial.vars_X, idx1_ne_idx2 hn,
      Ne.symm (idx1_ne_idx2 hn)] using h'
  · exact isRelPrime_X_pow_X_pow_of_ne
      (K := K) (idx0_ne_idx1 hn) 2 3

/-- Dehomogenizing a binary homogeneous degree-`d` form has degree at most `d`. -/
lemma dehom2_natDegree_le_of_isHomogeneous
    {K : Type*} [CommSemiring K]
    {d : ℕ} {q : Poly K 2}
    (hq : q.IsHomogeneous d) :
    (dehom2 q).natDegree ≤ d := by
  have h :=
    MvPolynomial.aeval_natDegree_le q hq.totalDegree_le
      ![Polynomial.X, (1 : Polynomial K)]
      (m := d) (n := 1)
      (by
        intro i
        fin_cases i <;> simp)
  simpa [dehom2] using h

/-- If the dehomogenized polynomial has degree strictly below the requested
homogeneous degree, the missing degree appears as a positive power of the
second homogenizing variable.  Hence `X₁` divides the homogenization. -/
lemma X_one_dvd_homogenize_of_natDegree_lt
    {K : Type*} [CommSemiring K]
    {p : Polynomial K} {d : ℕ}
    (hpd : p.natDegree < d) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣ p.homogenize d := by
  let e := d - p.natDegree
  have he : 0 < e := Nat.sub_pos_of_lt hpd
  have hle : p.natDegree ≤ d := Nat.le_of_lt hpd
  have hsum : p.natDegree + e = d := by
    simpa [e] using Nat.add_sub_of_le hle
  have H0 :=
    Polynomial.homogenize_mul p 1
      (m := p.natDegree) (n := e) le_rfl (by simp)
  have H :
      p.homogenize d =
        p.homogenize p.natDegree *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ e := by
    simpa [hsum] using H0
  have hpow :
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ e :=
    dvd_pow_self _ (Nat.ne_of_gt he)
  rcases hpow with ⟨s, hs⟩
  refine ⟨p.homogenize p.natDegree * s, ?_⟩
  rw [H, hs]
  ac_rfl

/-- Homogenizing the linear factor supplied by a root gives a homogeneous
linear divisor of the degree-three homogenization. -/
lemma homogenized_root_linear_dvd
    {K : Type*} [Field K]
    {p : Polynomial K} {r : K}
    (hp3 : p.natDegree = 3)
    (hr : p.IsRoot r) :
    (Polynomial.X - Polynomial.C r).homogenize 1 ∣
      p.homogenize 3 := by
  have h :=
    Polynomial.homogenize_dvd
      (Polynomial.dvd_iff_isRoot.mpr hr)
  simpa [hp3] using h

/-- The homogenized polynomial `X-r` is nonzero. -/
lemma homogenized_X_sub_C_ne_zero
    {K : Type*} [Field K] (r : K) :
    (Polynomial.X - Polynomial.C r).homogenize 1 ≠
      (0 : MvPolynomial (Fin 2) K) := by
  intro h
  have h0 :
      Polynomial.X - Polynomial.C r = (0 : Polynomial K) :=
    Polynomial.eq_zero_of_homogenize_eq_zero
      (p := Polynomial.X - Polynomial.C r) (n := 1)
      (by simp) h
  simpa using h0

/-- A nonzero homogeneous polynomial of positive degree cannot be a unit. -/
lemma not_isUnit_of_isHomogeneous_pos
    {K : Type*} [Field K]
    {σ : Type*} {p : MvPolynomial σ K} {d : ℕ}
    (hd : 0 < d)
    (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) :
    ¬ IsUnit p := by
  intro hu
  have hunitdeg :
      p.totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have hhomdeg : p.totalDegree = d := hp.totalDegree hp0
  omega

/-- An irreducible homogeneous cubic cannot have a nonzero homogeneous linear
factor. -/
lemma not_irreducible_of_homogeneous_linear_dvd
    {K : Type*} [Field K]
    {q l : MvPolynomial (Fin 2) K}
    (hq : q.IsHomogeneous 3)
    (hq0 : q ≠ 0)
    (hl : l.IsHomogeneous 1)
    (hl0 : l ≠ 0)
    (hldvd : l ∣ q) :
    ¬ Irreducible q := by
  intro hi
  rcases hldvd with ⟨r, hr⟩
  have hor := hi.isUnit_or_isUnit hr
  rcases hor with hlu | hru
  · exact (not_isUnit_of_isHomogeneous_pos
      (K := K) (by omega) hl hl0) hlu
  · have hr0 : r ≠ 0 := by
      intro hz
      apply hq0
      simpa [hr, hz]
    have hdegq : q.totalDegree = 3 := hq.totalDegree hq0
    have hdegl : l.totalDegree = 1 := hl.totalDegree hl0
    have hdegr : r.totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hru).2
    have hmul :
        q.totalDegree = l.totalDegree + r.totalDegree := by
      rw [hr]
      exact MvPolynomial.totalDegree_mul_of_isDomain hl0 hr0
    omega

/-- Main algebraic lemma: over a field in which every degree-three univariate
polynomial has a root, no binary homogeneous cubic is irreducible.

This single statement will be instantiated both for `ℝ` (real closed) and `ℂ`
(algebraically closed). -/
lemma binaryCubic_not_irreducible_of_cubicRoot
    {K : Type*} [Field K]
    (hroot :
      ∀ p : Polynomial K, p.natDegree = 3 →
        ∃ r : K, p.IsRoot r)
    {q : Poly K 2}
    (hq : q.IsHomogeneous 3) :
    ¬ Irreducible q := by
  intro hi
  have hq0 : q ≠ 0 := hi.ne_zero
  let p : Polynomial K := dehom2 q
  have hp_le : p.natDegree ≤ 3 := by
    dsimp [p]
    exact dehom2_natDegree_le_of_isHomogeneous hq
  have hqeq : p.homogenize 3 = q := by
    dsimp [p]
    exact homogenize_dehom2_eq hq
  by_cases hp3 : p.natDegree = 3
  · obtain ⟨r, hr⟩ := hroot p hp3
    let l : Poly K 2 :=
      (Polynomial.X - Polynomial.C r).homogenize 1
    have hldvd0 : l ∣ p.homogenize 3 := by
      dsimp [l]
      exact homogenized_root_linear_dvd hp3 hr
    have hldvd : l ∣ q := by
      rw [hqeq] at hldvd0
      exact hldvd0
    have hl : l.IsHomogeneous 1 := by
      dsimp [l]
      exact Polynomial.isHomogeneous_homogenize _
    have hl0 : l ≠ 0 := by
      dsimp [l]
      exact homogenized_X_sub_C_ne_zero r
    exact
      (not_irreducible_of_homogeneous_linear_dvd
        (K := K) hq hq0 hl hl0 hldvd) hi
  · have hplt : p.natDegree < 3 := by omega
    have hxdiv0 :
        (MvPolynomial.X 1 : Poly K 2) ∣ p.homogenize 3 :=
      X_one_dvd_homogenize_of_natDegree_lt hplt
    have hxdiv :
        (MvPolynomial.X 1 : Poly K 2) ∣ q := by
      rw [hqeq] at hxdiv0
      exact hxdiv0
    have hxhom :
        (MvPolynomial.X 1 : Poly K 2).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X
    have hx0 : (MvPolynomial.X 1 : Poly K 2) ≠ 0 := by simp
    exact
      (not_irreducible_of_homogeneous_linear_dvd
        (K := K) hq hq0 hxhom hx0 hxdiv) hi

/-- Every real binary homogeneous cubic is reducible (or zero), hence is never
irreducible. -/
theorem binaryCubic_not_irreducible_real
    {q : Poly ℝ 2}
    (hq : q.IsHomogeneous 3) :
    ¬ Irreducible q := by
  apply binaryCubic_not_irreducible_of_cubicRoot (K := ℝ)
  · intro p hp3
    have hodd : Odd p.natDegree := by
      rw [hp3]
      decide
    exact IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  · exact hq

/-- Every complex binary homogeneous cubic is reducible (or zero), hence is
never irreducible. -/
theorem binaryCubic_not_irreducible_complex
    {q : Poly ℂ 2}
    (hq : q.IsHomogeneous 3) :
    ¬ Irreducible q := by
  apply binaryCubic_not_irreducible_of_cubicRoot (K := ℂ)
  · intro p hp3
    have hp0 : p ≠ 0 := by
      intro hpz
      simp [hpz] at hp3
    have hdeg : 0 < p.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, hp3]
      norm_num
    exact Complex.exists_root hdeg
  · exact hq

/-- `f` has an irreducible restriction to some `k`-parameter linear space. -/
def DetectableIn
    {K : Type*} [CommSemiring K] {n : ℕ}
    (k : ℕ) (f : Poly K n) : Prop :=
  ∃ A : Frame K n k, Irreducible (restrictLinear f A)

/-- Every irreducible polynomial in `n` variables is detected in `k`
parameters. -/
def UniversalDetects
    (K : Type*) [CommSemiring K] (n k : ℕ) : Prop :=
  ∀ f : Poly K n, Irreducible f → DetectableIn k f

/-- The cubic witness has no irreducible two-parameter restriction over `ℝ`. -/
theorem cubicWitness_not_detectable_two_real
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ DetectableIn 2 (cubicWitness ℝ hn) := by
  rintro ⟨A, hA⟩
  exact
    binaryCubic_not_irreducible_real
      (restrict_cubicWitness_two_isHomogeneous hn A) hA

/-- The cubic witness has no irreducible two-parameter restriction over `ℂ`. -/
theorem cubicWitness_not_detectable_two_complex
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ DetectableIn 2 (cubicWitness ℂ hn) := by
  rintro ⟨A, hA⟩
  exact
    binaryCubic_not_irreducible_complex
      (restrict_cubicWitness_two_isHomogeneous hn A) hA

/-- Sharp high-dimensional lower bound against two parameters over `ℝ`. -/
theorem not_universalDetects_two_real
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ UniversalDetects ℝ n 2 := by
  intro hU
  exact cubicWitness_not_detectable_two_real hn
    (hU (cubicWitness ℝ hn) (cubicWitness_irreducible hn))

/-- Sharp high-dimensional lower bound against two parameters over `ℂ`. -/
theorem not_universalDetects_two_complex
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ UniversalDetects ℂ n 2 := by
  intro hU
  exact cubicWitness_not_detectable_two_complex hn
    (hU (cubicWitness ℂ hn) (cubicWitness_irreducible hn))

/-!
What this stage closes mathematically
------------------------------------

Assuming the proof terms above elaborate against the installed Mathlib version,
the complete high-dimensional `k_n ≥ 3` obstruction has now been reduced to
ordinary library lemmas and explicit algebra; no Bertini input is involved.

The next strict targets are:
1. compile/debug this file against the user's local Mathlib snapshot;
2. prove `k₂ ≥ 2` with an explicit two-variable witness;
3. integrate these lower bounds with Stage 1;
4. finally eliminate the fixed-point Bertini axiom from the upper bound.
-/


/-! ## Stage 4: the sharp two-variable lower bound `k₂ ≥ 2` -/

/-- A plane witness for which every origin-line restriction has a repeated
factor, while the polynomial itself is irreducible. -/
def planeWitness
    (K : Type*) [CommRing K] : Poly K 2 :=
  MvPolynomial.X (0 : Fin 2) ^ 2 +
    MvPolynomial.X (1 : Fin 2) ^ 2 +
    MvPolynomial.X (1 : Fin 2) ^ 3

/-!
For the irreducibility proof we use `finSuccEquiv K 1`, which views a polynomial
in `(X₀,X₁)` as a univariate polynomial in `X₀` with coefficients in `K[X₁]`.
-/

abbrev OneVarCoeff (K : Type*) [CommSemiring K] :=
  MvPolynomial (Fin 1) K

def innerY
    (K : Type*) [CommSemiring K] : OneVarCoeff K :=
  MvPolynomial.X (0 : Fin 1)

def eisensteinPrime
    (K : Type*) [CommRing K] : OneVarCoeff K :=
  innerY K + 1

def eisensteinConst
    (K : Type*) [CommRing K] : OneVarCoeff K :=
  innerY K ^ 2 * eisensteinPrime K

def outerPlaneWitness
    (K : Type*) [CommRing K] :
    Polynomial (OneVarCoeff K) :=
  Polynomial.X ^ 2 + Polynomial.C (eisensteinConst K)

/-- Under `finSuccEquiv`, the explicit plane witness is exactly the quadratic
polynomial used in the Eisenstein proof. -/
lemma finSuccEquiv_planeWitness
    {K : Type*} [CommRing K] :
    MvPolynomial.finSuccEquiv K 1 (planeWitness K) =
      outerPlaneWitness K := by
  simp [planeWitness, outerPlaneWitness, eisensteinConst,
    eisensteinPrime, innerY, pow_two,
    MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ]

/-- `Y+1` is irreducible in the one-variable coefficient ring.

This uses the already verified Mathlib theorem
`MvPolynomial.irreducible_mul_X_add`; no UFD factorization argument is needed
at this point. -/
lemma eisensteinPrime_irreducible
    {K : Type*} [Field K] :
    Irreducible (eisensteinPrime K) := by
  classical
  unfold eisensteinPrime innerY
  simpa using
    (MvPolynomial.irreducible_mul_X_add
      (1 : OneVarCoeff K) (1 : OneVarCoeff K) (0 : Fin 1)
      (by simp) (by simp) (by simp)
      (by simpa using (isRelPrime_one_left : IsRelPrime
        (1 : OneVarCoeff K) 1)))

/-- Hence `Y+1` is prime. -/
lemma eisensteinPrime_prime
    {K : Type*} [Field K] :
    Prime (eisensteinPrime K) := by
  exact (eisensteinPrime_irreducible (K := K)).prime

/-- The principal ideal generated by `Y+1` is prime.

We prove this directly from the definition, avoiding any dependence on the
name/location of a principal-prime-ideal convenience theorem. -/
lemma eisensteinIdeal_isPrime
    {K : Type*} [Field K] :
    (Ideal.span ({eisensteinPrime K} : Set (OneVarCoeff K))).IsPrime := by
  let π : OneVarCoeff K := eisensteinPrime K
  have hp : Prime π := eisensteinPrime_prime (K := K)
  refine ⟨Ideal.span_singleton_ne_top hp.not_isUnit, ?_⟩
  intro a b hab
  rw [Ideal.mem_span_singleton] at hab
  rcases hp.dvd_or_dvd hab with ha | hb
  · exact Or.inl ((Ideal.mem_span_singleton).2 ha)
  · exact Or.inr ((Ideal.mem_span_singleton).2 hb)

/-- `Y+1` does not divide `Y`.  Evaluation at `Y=-1` proves this immediately. -/
lemma eisensteinPrime_not_dvd_innerY
    {K : Type*} [Field K] :
    ¬ eisensteinPrime K ∣ innerY K := by
  classical
  intro h
  rcases h with ⟨q, hq⟩
  let v : Fin 1 → K := fun _ => -1
  have hv := congrArg (MvPolynomial.eval v) hq
  have : (-1 : K) = 0 := by
    simpa [eisensteinPrime, innerY, v] using hv
  exact one_ne_zero (neg_eq_zero.mp this)

/-- Consequently `Y+1` does not divide `Y²`. -/
lemma eisensteinPrime_not_dvd_innerY_sq
    {K : Type*} [Field K] :
    ¬ eisensteinPrime K ∣ innerY K ^ 2 := by
  have hp : Prime (eisensteinPrime K) :=
    eisensteinPrime_prime (K := K)
  rw [hp.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)]
  exact eisensteinPrime_not_dvd_innerY (K := K)

/-- The Eisenstein constant term `Y²(Y+1)` is not divisible by `(Y+1)²`. -/
lemma eisensteinPrime_sq_not_dvd_const
    {K : Type*} [Field K] :
    ¬ eisensteinPrime K ^ 2 ∣ eisensteinConst K := by
  let π : OneVarCoeff K := eisensteinPrime K
  let y : OneVarCoeff K := innerY K
  have hp : Prime π := eisensteinPrime_prime (K := K)
  have hnot : ¬ π ∣ y ^ 2 := by
    simpa [π, y] using eisensteinPrime_not_dvd_innerY_sq (K := K)
  intro hsq
  have hsqπ : π ^ 2 ∣ π := by
    apply hp.pow_dvd_of_dvd_mul_left 2 hnot
    simpa [eisensteinConst, π, y, mul_comm] using hsq
  have hp0 : π ≠ 0 := hp.ne_zero
  rcases hsqπ with ⟨q, hq⟩
  have hone : (1 : OneVarCoeff K) = π * q := by
    apply mul_left_cancel₀ hp0
    simpa [pow_two, mul_assoc] using hq
  have hunit : IsUnit π := by
    apply isUnit_of_dvd_one
    exact ⟨q, hone⟩
  exact hp.not_isUnit hunit

/-- The outer quadratic is monic of degree two. -/
lemma outerPlaneWitness_isMonicOfDegree
    {K : Type*} [Field K] :
    (outerPlaneWitness K).IsMonicOfDegree 2 := by
  simpa [outerPlaneWitness] using
    (Polynomial.isMonicOfDegree_add_add_two
      (R := OneVarCoeff K)
      (0 : OneVarCoeff K) (eisensteinConst K))

/-- Eisenstein at the prime ideal `(Y+1)`. -/
lemma outerPlaneWitness_isEisenstein
    {K : Type*} [Field K] :
    (outerPlaneWitness K).IsEisensteinAt
      (Ideal.span ({eisensteinPrime K} : Set (OneVarCoeff K))) := by
  let P : Ideal (OneVarCoeff K) :=
    Ideal.span ({eisensteinPrime K} : Set (OneVarCoeff K))
  have hprime : P.IsPrime := by
    simpa [P] using eisensteinIdeal_isPrime (K := K)
  have hm : (outerPlaneWitness K).Monic :=
    (outerPlaneWitness_isMonicOfDegree (K := K)).monic
  apply hm.isEisensteinAt_of_mem_of_notMem hprime.ne_top
  · intro n hn
    have hdeg :
        (outerPlaneWitness K).natDegree = 2 :=
      (outerPlaneWitness_isMonicOfDegree (K := K)).natDegree_eq
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · rw [show (outerPlaneWitness K).coeff 0 =
          eisensteinConst K by
        simp [outerPlaneWitness]]
      rw [show P =
          Ideal.span ({eisensteinPrime K} : Set (OneVarCoeff K)) by rfl]
      rw [Ideal.mem_span_singleton]
      exact dvd_mul_left _ _
    · simp [outerPlaneWitness, P]
  · rw [show (outerPlaneWitness K).coeff 0 =
        eisensteinConst K by simp [outerPlaneWitness]]
    rw [show P ^ 2 =
        Ideal.span ({eisensteinPrime K ^ 2} : Set (OneVarCoeff K)) by
      simp [P, Ideal.span_singleton_pow]]
    rw [Ideal.mem_span_singleton]
    exact eisensteinPrime_sq_not_dvd_const (K := K)

/-- The outer quadratic is irreducible by Eisenstein. -/
lemma outerPlaneWitness_irreducible
    {K : Type*} [Field K] :
    Irreducible (outerPlaneWitness K) := by
  let P : Ideal (OneVarCoeff K) :=
    Ideal.span ({eisensteinPrime K} : Set (OneVarCoeff K))
  have hE :
      (outerPlaneWitness K).IsEisensteinAt P := by
    simpa [P] using outerPlaneWitness_isEisenstein (K := K)
  have hP : P.IsPrime := by
    simpa [P] using eisensteinIdeal_isPrime (K := K)
  have hm : (outerPlaneWitness K).Monic :=
    (outerPlaneWitness_isMonicOfDegree (K := K)).monic
  have hdeg :
      0 < (outerPlaneWitness K).natDegree := by
    rw [(outerPlaneWitness_isMonicOfDegree (K := K)).natDegree_eq]
    omega
  exact hE.irreducible hP hm.isPrimitive hdeg

/-- Therefore the original explicit two-variable witness is irreducible. -/
lemma planeWitness_irreducible
    {K : Type*} [Field K] :
    Irreducible (planeWitness K) := by
  apply Irreducible.of_map
    (f := MvPolynomial.finSuccEquiv K 1)
  simpa [finSuccEquiv_planeWitness] using
    outerPlaneWitness_irreducible (K := K)

/-- In one parameter every frame row is a scalar multiple of the unique
variable. -/
lemma frameRow_fin_one
    {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Frame K n 1) (i : Fin n) :
    A.toMvPolynomial i =
      MvPolynomial.C (A i 0) * MvPolynomial.X (0 : Fin 1) := by
  classical
  rw [Matrix.toMvPolynomial]
  simpa only [Fin.sum_univ_one]

/-- Every line restriction of `planeWitness` has an explicit factor `T²`.

Writing `a,b` for the two coordinates of the line direction, the quotient is
`a² + b² + b³T`. -/
lemma restrict_planeWitness_line_factor
    {K : Type*} [CommRing K]
    (A : Frame K 2 1) :
    restrictLinear (planeWitness K) A =
      MvPolynomial.X (0 : Fin 1) *
        (MvPolynomial.X (0 : Fin 1) *
          (MvPolynomial.C ((A 0 0) ^ 2 + (A 1 0) ^ 2) +
            MvPolynomial.C ((A 1 0) ^ 3) *
              MvPolynomial.X (0 : Fin 1))) := by
  rw [restrictLinear_eq_aeval]
  simp [planeWitness, frameRow_fin_one]
  ring

/-- No line restriction of the plane witness is irreducible. -/
lemma planeWitness_line_not_irreducible
    {K : Type*} [Field K]
    (A : Frame K 2 1) :
    ¬ Irreducible (restrictLinear (planeWitness K) A) := by
  intro hI
  let T : Poly K 1 := MvPolynomial.X (0 : Fin 1)
  let H : Poly K 1 :=
    MvPolynomial.C ((A 0 0) ^ 2 + (A 1 0) ^ 2) +
      MvPolynomial.C ((A 1 0) ^ 3) * T
  have hfac :
      T * (T * H) = restrictLinear (planeWitness K) A := by
    symm
    simpa [T, H] using restrict_planeWitness_line_factor A
  have hor : IsUnit T ∨ IsUnit (T * H) :=
    hI.isUnit_or_isUnit hfac.symm
  rcases hor with hT | hTH
  · exact (irreducible_X (K := K) (0 : Fin 1)).not_isUnit hT
  · have hT' : IsUnit T := (IsUnit.mul_iff.mp hTH).1
    exact (irreducible_X (K := K) (0 : Fin 1)).not_isUnit hT'

/-- Thus the two-variable witness is not detectable on one parameter. -/
theorem planeWitness_not_detectable_one
    {K : Type*} [Field K] :
    ¬ DetectableIn 1 (planeWitness K) := by
  rintro ⟨A, hA⟩
  exact planeWitness_line_not_irreducible A hA

/-- Sharp lower bound `k₂ ≥ 2`, uniformly over every field. -/
theorem not_universalDetects_one_twoVars
    {K : Type*} [Field K] :
    ¬ UniversalDetects K 2 1 := by
  intro hU
  exact planeWitness_not_detectable_one (K := K)
    (hU (planeWitness K) planeWitness_irreducible)

/-- Real specialization of the two-variable lower bound. -/
theorem not_universalDetects_one_twoVars_real :
    ¬ UniversalDetects ℝ 2 1 :=
  not_universalDetects_one_twoVars

/-- Complex specialization of the two-variable lower bound. -/
theorem not_universalDetects_one_twoVars_complex :
    ¬ UniversalDetects ℂ 2 1 :=
  not_universalDetects_one_twoVars

/-!
Stage-4 mathematical output
---------------------------

This candidate now contains proof terms for:
* `¬ UniversalDetects K 2 1` over every field `K`;
* `¬ UniversalDetects ℝ n 2` for all `n ≥ 3`;
* `¬ UniversalDetects ℂ n 2` for all `n ≥ 3`.

There is still no `axiom`, `sorry`, or `admit`.

For exact `k_n = 3`, one additional lower-bound bookkeeping item remains:
`¬ UniversalDetects K n 1` for `n ≥ 3`.  The cleanest next step is to prove
that every one-parameter restriction of the homogeneous cubic witness has an
`X` factor twice (indeed three times), rather than prove a general monotonicity
lemma from one to two parameters.

The only large theorem still outside the strict core remains fixed-point
Bertini for the upper bound.
-/


/-! ## Stage 5: close the remaining one-parameter high-dimensional lower bound -/

/-- On a line, the high-dimensional cubic witness is a scalar multiple of
`T³`.  We keep the factorization as `T * (T² * C c)` because this is exactly
what irreducibility needs. -/
lemma restrict_cubicWitness_line_factor
    {K : Type*} [Field K]
    {n : ℕ} (hn : 3 ≤ n)
    (A : Frame K n 1) :
    restrictLinear (cubicWitness K hn) A =
      MvPolynomial.X (0 : Fin 1) *
        (MvPolynomial.X (0 : Fin 1) ^ 2 *
          MvPolynomial.C
            ((A (idx0 hn) 0) ^ 2 * A (idx2 hn) 0 +
              (A (idx1 hn) 0) ^ 3)) := by
  rw [restrictLinear_eq_aeval]
  simp [cubicWitness, frameRow_fin_one]
  ring

/-- Every one-parameter restriction of the cubic witness is non-irreducible. -/
lemma cubicWitness_line_not_irreducible
    {K : Type*} [Field K]
    {n : ℕ} (hn : 3 ≤ n)
    (A : Frame K n 1) :
    ¬ Irreducible (restrictLinear (cubicWitness K hn) A) := by
  intro hI
  let T : Poly K 1 := MvPolynomial.X (0 : Fin 1)
  let H : Poly K 1 :=
    T ^ 2 *
      MvPolynomial.C
        ((A (idx0 hn) 0) ^ 2 * A (idx2 hn) 0 +
          (A (idx1 hn) 0) ^ 3)
  have hfac :
      T * H = restrictLinear (cubicWitness K hn) A := by
    symm
    simpa [T, H] using restrict_cubicWitness_line_factor hn A
  have hor : IsUnit T ∨ IsUnit H :=
    hI.isUnit_or_isUnit hfac.symm
  rcases hor with hT | hH
  · exact (irreducible_X (K := K) (0 : Fin 1)).not_isUnit hT
  · have hT2 :
        IsUnit (T ^ 2) :=
      (IsUnit.mul_iff.mp hH).1
    have hT : IsUnit T := by
      simpa [pow_two, IsUnit.mul_iff] using hT2
    exact (irreducible_X (K := K) (0 : Fin 1)).not_isUnit hT

/-- Hence the cubic witness cannot be detected in one parameter. -/
theorem cubicWitness_not_detectable_one
    {K : Type*} [Field K]
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ DetectableIn 1 (cubicWitness K hn) := by
  rintro ⟨A, hA⟩
  exact cubicWitness_line_not_irreducible hn A hA

/-- High-dimensional lower bound against one parameter, valid over every field. -/
theorem not_universalDetects_one_high
    {K : Type*} [Field K]
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ UniversalDetects K n 1 := by
  intro hU
  exact cubicWitness_not_detectable_one hn
    (hU (cubicWitness K hn) (cubicWitness_irreducible hn))

/-- Real high-dimensional one-parameter obstruction. -/
theorem not_universalDetects_one_high_real
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ UniversalDetects ℝ n 1 :=
  not_universalDetects_one_high hn

/-- Complex high-dimensional one-parameter obstruction. -/
theorem not_universalDetects_one_high_complex
    {n : ℕ} (hn : 3 ≤ n) :
    ¬ UniversalDetects ℂ n 1 :=
  not_universalDetects_one_high hn

/-- All sharp lower bounds needed for Problem 20.1 over the reals. -/
theorem all_lower_bounds_real :
    (¬ UniversalDetects ℝ 2 1) ∧
    (∀ n, 3 ≤ n → ¬ UniversalDetects ℝ n 1) ∧
    (∀ n, 3 ≤ n → ¬ UniversalDetects ℝ n 2) := by
  exact ⟨not_universalDetects_one_twoVars_real,
    fun n hn => not_universalDetects_one_high_real hn,
    fun n hn => not_universalDetects_two_real hn⟩

/-- All sharp lower bounds needed for Problem 20.1 over the complexes. -/
theorem all_lower_bounds_complex :
    (¬ UniversalDetects ℂ 2 1) ∧
    (∀ n, 3 ≤ n → ¬ UniversalDetects ℂ n 1) ∧
    (∀ n, 3 ≤ n → ¬ UniversalDetects ℂ n 2) := by
  exact ⟨not_universalDetects_one_twoVars_complex,
    fun n hn => not_universalDetects_one_high_complex hn,
    fun n hn => not_universalDetects_two_complex hn⟩

/-!
Strict lower-bound milestone
----------------------------

At the proof-term level this candidate now contains *all* lower bounds required
for the exact sequence:

* `k₁ ≥ 1` is tautological from the definition of positive detection dimension;
* `k₂ ≥ 2` over `ℝ` and `ℂ`;
* `kₙ ≥ 3` for every `n ≥ 3` over `ℝ` and `ℂ`.

No mathematical axiom, theorem-interface placeholder, `sorry`, or `admit` is
used in these lower-bound proofs.

After local compilation/debugging, the only genuinely substantial mathematical
gap should therefore be the fixed-point Bertini theorem needed for `kₙ ≤ 3`.
-/


/-! ## Stage 6: coordinate reduction of the remaining Bertini step

Everything in this section is unconditional.  We do **not** postulate a
Bertini theorem.  Instead we put the required codimension-one section into a
single explicit affine chart of the dual projective space.

For `a : Fin m → K`, `graphFrame a` parametrizes the hyperplane
\[
  x_m = \sum_{j<m} a_j x_j.
\]
Thus the only remaining existence statement can be formulated entirely inside
`MvPolynomial`: some `a` makes the corresponding graph restriction
irreducible.
-/

/-- The matrix of the graph embedding
`x ↦ (x₀,…,x_{m-1}, ∑ a_j x_j)`. -/
def graphFrame
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) : Frame K (m + 1) m :=
  fun i j =>
    Fin.lastCases (a j)
      (fun r : Fin m => if r = j then 1 else 0) i

@[simp] lemma graphFrame_castSucc
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) (i j : Fin m) :
    graphFrame a i.castSucc j = if i = j then 1 else 0 := by
  simp [graphFrame]

@[simp] lemma graphFrame_last
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) (j : Fin m) :
    graphFrame a (Fin.last m) j = a j := by
  simp [graphFrame]

/-- The graph point in `K^(m+1)` associated to a parameter vector `a` and an
ordinary point `x ∈ K^m`. -/
def graphPoint
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) : Fin (m + 1) → K :=
  fun i =>
    Fin.lastCases
      (∑ j : Fin m, a j * x j)
      (fun r : Fin m => x r) i

@[simp] lemma graphPoint_castSucc
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) (i : Fin m) :
    graphPoint a x i.castSucc = x i := by
  simp [graphPoint]

@[simp] lemma graphPoint_last
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) :
    graphPoint a x (Fin.last m) = ∑ j : Fin m, a j * x j := by
  simp [graphPoint]

/-- On the first `m` coordinates, `graphFrame a` really is the identity. -/
lemma graphFrame_mulVec_castSucc
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) (i : Fin m) :
    (graphFrame a).mulVec x i.castSucc = x i := by
  classical
  simp [Matrix.mulVec, dotProduct, graphFrame]

/-- The last coordinate of the matrix product is the prescribed linear form. -/
lemma graphFrame_mulVec_last
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) :
    (graphFrame a).mulVec x (Fin.last m) =
      ∑ j : Fin m, a j * x j := by
  classical
  simp [Matrix.mulVec, dotProduct, graphFrame]

/-- Matrix multiplication by `graphFrame a` is exactly `graphPoint a`. -/
lemma graphFrame_mulVec_eq_graphPoint
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a x : Fin m → K) :
    (graphFrame a).mulVec x = graphPoint a x := by
  funext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simpa only [graphPoint_last] using graphFrame_mulVec_last a x
  · simpa only [graphPoint_castSucc] using graphFrame_mulVec_castSucc a x r

/-- In particular the graph frame has trivial kernel (indeed the first `m`
rows already form the identity). -/
lemma graphFrame_mulVec_injective
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) :
    Function.Injective fun x : Fin m → K => (graphFrame a).mulVec x := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i.castSucc
  simpa [graphFrame_mulVec_castSucc] using hi

/-- The polynomial restriction to the graph hyperplane.  This is not a new
notion of restriction: it is literally the existing `restrictLinear` applied
to the concrete graph frame. -/
def graphRestrict
    {K : Type*} [CommSemiring K] {m : ℕ}
    (f : Poly K (m + 1)) (a : Fin m → K) : Poly K m :=
  restrictLinear f (graphFrame a)

@[simp] lemma graphRestrict_eq_restrictLinear
    {K : Type*} [CommSemiring K] {m : ℕ}
    (f : Poly K (m + 1)) (a : Fin m → K) :
    graphRestrict f a = restrictLinear f (graphFrame a) := rfl

/-- Pointwise semantic formula for a linear restriction by an arbitrary
matrix. -/
lemma eval_restrictLinear
    {K : Type*} [CommSemiring K] {n k : ℕ}
    (f : Poly K n) (A : Frame K n k) (x : Fin k → K) :
    MvPolynomial.eval x (restrictLinear f A) =
      MvPolynomial.eval (A.mulVec x) f := by
  change
    MvPolynomial.eval x
        (MvPolynomial.bind₁ A.toMvPolynomial f) =
      MvPolynomial.eval (A.mulVec x) f
  calc
    MvPolynomial.eval x
        (MvPolynomial.bind₁ A.toMvPolynomial f) =
      MvPolynomial.eval
        (fun i => MvPolynomial.eval x (A.toMvPolynomial i)) f := by
          simpa using
            (MvPolynomial.eval₂Hom_bind₁
              (RingHom.id K) x A.toMvPolynomial f)
    _ = MvPolynomial.eval (A.mulVec x) f := by
      congr 1
      funext i
      exact Matrix.toMvPolynomial_eval_eq_apply A i x

/-- Therefore graph restriction has exactly the expected substitution
semantics:
`f(x₀,…,x_{m-1}, Σ a_j x_j)`. -/
lemma eval_graphRestrict
    {K : Type*} [CommSemiring K] {m : ℕ}
    (f : Poly K (m + 1))
    (a x : Fin m → K) :
    MvPolynomial.eval x (graphRestrict f a) =
      MvPolynomial.eval (graphPoint a x) f := by
  rw [graphRestrict, eval_restrictLinear,
    graphFrame_mulVec_eq_graphPoint]

/-- The exact remaining codimension-one statement, written as a proposition
rather than an axiom or a typeclass.

Proving this proposition for `K = ℝ` and `K = ℂ` is now the only genuinely
substantial upper-bound theorem still missing.
-/
def GraphBertiniStatement
    (K : Type*) [Field K] : Prop :=
  ∀ {m : ℕ}, 3 ≤ m →
    ∀ f : Poly K (m + 1), Irreducible f →
      ∃ a : Fin m → K, Irreducible (graphRestrict f a)

/-- The graph version immediately implies the old one-step matrix statement.
This is a reduction theorem, not an assumption. -/
theorem graphBertini_implies_oneStep
    {K : Type*} [Field K]
    (hGB : GraphBertiniStatement K)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly K (m + 1)) (hf : Irreducible f) :
    ∃ A : Frame K (m + 1) m,
      Irreducible (restrictLinear f A) := by
  obtain ⟨a, ha⟩ := hGB hm f hf
  exact ⟨graphFrame a, ha⟩

/-! ### The universal parameter family

For the algebraic attack on `GraphBertiniStatement`, it is useful to keep the
hyperplane coefficients and the surviving coordinates as disjoint variable
sets.  `Sum.inl j` is the parameter `A_j`, and `Sum.inr j` is the space
coordinate `X_j`.
-/

abbrev GraphVar (m : ℕ) := Sum (Fin m) (Fin m)

def paramX
    {K : Type*} [CommSemiring K] {m : ℕ}
    (j : Fin m) : MvPolynomial (GraphVar m) K :=
  MvPolynomial.X (Sum.inl j)

def spaceX
    {K : Type*} [CommSemiring K] {m : ℕ}
    (j : Fin m) : MvPolynomial (GraphVar m) K :=
  MvPolynomial.X (Sum.inr j)

/-- The universal last coordinate `Σ A_j X_j`. -/
def universalGraphLinear
    {K : Type*} [CommSemiring K] {m : ℕ} :
    MvPolynomial (GraphVar m) K :=
  ∑ j : Fin m, paramX j * spaceX j

/-- Universal substitution of the `m+1` ambient coordinates. -/
def universalGraphSubst
    {K : Type*} [CommSemiring K] {m : ℕ} :
    Fin (m + 1) → MvPolynomial (GraphVar m) K :=
  fun i =>
    Fin.lastCases
      universalGraphLinear
      (fun r : Fin m => spaceX r) i

@[simp] lemma universalGraphSubst_castSucc
    {K : Type*} [CommSemiring K] {m : ℕ}
    (i : Fin m) :
    universalGraphSubst (K := K) i.castSucc = spaceX i := by
  simp [universalGraphSubst]

@[simp] lemma universalGraphSubst_last
    {K : Type*} [CommSemiring K] {m : ℕ} :
    universalGraphSubst (K := K) (Fin.last m) =
      universalGraphLinear := by
  simp [universalGraphSubst]

/-- The universal graph section, before choosing numerical hyperplane
coefficients. -/
def universalGraphSection
    {K : Type*} [CommSemiring K] {m : ℕ}
    (f : Poly K (m + 1)) : MvPolynomial (GraphVar m) K :=
  MvPolynomial.bind₁ universalGraphSubst f

/-- Specialize only the parameter variables `A_j ↦ a_j`, leaving `X_j`
untouched. -/
def specializeGraphParams
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) :
    GraphVar m → Poly K m
  | Sum.inl j => MvPolynomial.C (a j)
  | Sum.inr j => MvPolynomial.X j

/-- The universal linear form specializes to the expected graph linear form
pointwise. -/
lemma specialize_universalGraphLinear
    {K : Type*} [CommSemiring K] {m : ℕ}
    (a : Fin m → K) :
    MvPolynomial.bind₁ (specializeGraphParams a)
        (universalGraphLinear (K := K)) =
      ∑ j : Fin m,
        MvPolynomial.C (a j) * MvPolynomial.X j := by
  classical
  unfold universalGraphLinear paramX spaceX
  simp only [map_sum, map_mul,
    MvPolynomial.bind₁_X_right,
    specializeGraphParams]

/-- Specializing the universal section gives exactly the concrete graph
restriction.  This is the key bridge between a future generic-parameter proof
and the original statement.

The proof is intentionally phrased through `bind₁_bind₁`, so there is no
scheme-theoretic content hidden here.
-/
lemma specialize_universalGraphSection
    {K : Type*} [CommSemiring K] {m : ℕ}
    (f : Poly K (m + 1)) (a : Fin m → K) :
    MvPolynomial.bind₁ (specializeGraphParams a)
        (universalGraphSection f) =
      graphRestrict f a := by
  classical
  unfold universalGraphSection graphRestrict restrictLinear restrictHom
  rw [MvPolynomial.bind₁_bind₁]
  apply congrArg
    (fun h : Fin (m + 1) → Poly K m =>
      MvPolynomial.bind₁ h f)
  funext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simp [universalGraphSubst, specialize_universalGraphLinear,
      graphFrame, Matrix.toMvPolynomial,
      MvPolynomial.C_mul_X_eq_monomial]
  · change MvPolynomial.X r =
        Matrix.toMvPolynomial (graphFrame a) r.castSucc
    simp [graphFrame, Matrix.toMvPolynomial]

/-!
Stage-6 status
--------------

The fixed-point hyperplane step has now been reduced to the single explicit
statement `GraphBertiniStatement K`.

Everything around it is formal algebra:
* a concrete full-rank graph matrix;
* the exact pointwise graph-substitution formula;
* the universal graph-section polynomial;
* exact specialization of that universal family back to `graphRestrict`.

No Bertini assumption is introduced anywhere in this section.

A direct algebraic proof can therefore focus on the universal polynomial
`universalGraphSection f`: show that the bad parameter locus (parameters `a`
for which specialization factors) is contained in a proper algebraic subset,
then use infinitude of `ℝ` or `ℂ` to choose a point outside it.  This is now a
precisely isolated formalization target rather than a geometric black box.
-/


/-! ## Stage 7: certificate layer for the final Bertini existence theorem

Over an infinite field, a nonzero multivariate polynomial cannot vanish at
every point.  This elementary fact lets us turn a *principal-open
irreducibility certificate* into an actual graph hyperplane.

For `ℂ`, such a certificate is the right algebraic replacement for the
geometric phrase "a general hyperplane section is irreducible".

For `ℝ`, one must be more careful: ordinary real irreducibility is not in
general a Zariski-open condition in arbitrary polynomial families.  The final
real proof will therefore descend a complex/geometric certificate, treating
the possible conjugate-pair decomposition separately.
-/

/-- A nonzero multivariate polynomial over an infinite field has a point where
it does not vanish.

This is an immediate contrapositive of `MvPolynomial.funext`; recording it
explicitly keeps the eventual Bertini argument independent of topology. -/
lemma exists_eval_ne_zero
    {K : Type*} [Field K] [Infinite K]
    {σ : Type*} (p : MvPolynomial σ K)
    (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa [h x]

/-- A principal-open certificate for irreducibility of graph sections.

`Δ` is a polynomial in the hyperplane parameters.  Off its zero locus, every
corresponding graph section is irreducible.
-/
def HasGraphIrreducibilityCertificate
    (K : Type*) [Field K]
    {m : ℕ} (f : Poly K (m + 1)) : Prop :=
  ∃ Δ : MvPolynomial (Fin m) K,
    Δ ≠ 0 ∧
    ∀ a : Fin m → K,
      MvPolynomial.eval a Δ ≠ 0 →
        Irreducible (graphRestrict f a)

/-- A certificate produces an actual good graph hyperplane over any infinite
field. -/
theorem exists_irreducible_graphRestrict_of_certificate
    {K : Type*} [Field K] [Infinite K]
    {m : ℕ} {f : Poly K (m + 1)}
    (hcert : HasGraphIrreducibilityCertificate K f) :
    ∃ a : Fin m → K, Irreducible (graphRestrict f a) := by
  rcases hcert with ⟨Δ, hΔ, hgood⟩
  obtain ⟨a, ha⟩ := exists_eval_ne_zero Δ hΔ
  exact ⟨a, hgood a ha⟩

/-- A uniform certificate theorem immediately implies the graph-Bertini
existence statement. -/
theorem graphBertini_of_certificates
    {K : Type*} [Field K] [Infinite K]
    (hcert :
      ∀ {m : ℕ}, 3 ≤ m →
        ∀ f : Poly K (m + 1), Irreducible f →
          HasGraphIrreducibilityCertificate K f) :
    GraphBertiniStatement K := by
  intro m hm f hf
  exact exists_irreducible_graphRestrict_of_certificate
    (hcert hm f hf)

/-! ### Complex target

Because `ℂ` is algebraically closed, irreducibility and geometric
irreducibility agree for hypersurface equations.  Consequently the strongest
clean algebraic target for the complex case is the following proposition.

It is deliberately a `def` (a target statement), not an axiom and not an
assumed typeclass.
-/

def ComplexGraphBertiniCertificateStatement : Prop :=
  ∀ {m : ℕ}, 3 ≤ m →
    ∀ f : Poly ℂ (m + 1), Irreducible f →
      HasGraphIrreducibilityCertificate ℂ f

/-- Once the complex certificate statement is proved, the complex
codimension-one Bertini existence theorem follows with no further geometry. -/
theorem complex_graphBertini_of_certificate_statement
    (h : ComplexGraphBertiniCertificateStatement) :
    GraphBertiniStatement ℂ := by
  exact graphBertini_of_certificates h

/-! ### Why the same statement is not adopted blindly over `ℝ`

For arbitrary real polynomial families, ordinary irreducibility need not be a
Zariski-open property.  Thus the correct real route is not to *define* the
remaining theorem as a real certificate theorem and silently assume it.

Instead the proof must use complexification:
1. if the complexification stays irreducible, use a conjugation-stable complex
   certificate and choose a real parameter outside its real norm-zero locus;
2. if the complexification splits, real irreducibility forces the complex
   factors to form a conjugate pair; choose a real parameter where the two
   specialized conjugate factors remain irreducible and distinct, and descend
   that pair back to a real irreducible polynomial.

The next formal layer should therefore concern scalar extension and conjugation,
not an unjustified "real irreducibility is open" assertion.
-/

/-- The precise complex certificate statement for one fixed polynomial.  This
alias is useful when isolating the eventual Noether-form/Bertini proof. -/
def ComplexCertificateFor
    {m : ℕ} (f : Poly ℂ (m + 1)) : Prop :=
  HasGraphIrreducibilityCertificate ℂ f

/-- The final unresolved complex algebraic core, stripped of all matrix and
parameter-selection bookkeeping. -/
def ComplexBertiniCore : Prop :=
  ∀ {m : ℕ}, 3 ≤ m →
    ∀ f : Poly ℂ (m + 1), Irreducible f →
      ComplexCertificateFor f

theorem complexBertiniCore_iff_certificateStatement :
    ComplexBertiniCore ↔ ComplexGraphBertiniCertificateStatement := by
  rfl

/-!
Stage-7 audit
-------------

At this point the upper-bound architecture is:

`ComplexBertiniCore`
  → nonzero certificate polynomial `Δ`
  → an actual complex parameter `a`
  → `GraphBertiniStatement ℂ`
  → the one-step matrix reduction
  → repeated reduction to three variables.

Every arrow after `ComplexBertiniCore` has a proof term in this file.

The real case is intentionally *not* packaged behind an unjustified openness
axiom.  It will require a separate conjugation/descent layer.

Thus the remaining research problem is now genuinely concentrated in:
* construction of the complex certificate (`ComplexBertiniCore`);
* real descent from the complex statement.

No `axiom`, `sorry`, `admit`, or theorem-interface assumption has been added.
-/


/-! ## Stage 8: scalar extension and conjugation for the real descent

This section proves only functorial algebra.  It does not assume any
factorization theorem for real polynomials.

The key point is that graph restriction commutes with *every* coefficient
ring homomorphism.  Complexification and complex conjugation are then immediate
special cases.
-/

/-- Apply a coefficient ring homomorphism entrywise to a graph frame. -/
lemma graphFrame_map
    {K L : Type*} [CommSemiring K] [CommSemiring L]
    (φ : K →+* L) {m : ℕ} (a : Fin m → K) :
    (graphFrame a).map φ =
      graphFrame (fun j => φ (a j)) := by
  ext i j
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simp [graphFrame]
  · by_cases h : r = j
    · simp [graphFrame, h]
    · simp [graphFrame, h]

/-- Mapping coefficients through a ring homomorphism commutes with graph
restriction. -/
lemma map_graphRestrict
    {K L : Type*} [CommSemiring K] [CommSemiring L]
    (φ : K →+* L) {m : ℕ}
    (f : Poly K (m + 1)) (a : Fin m → K) :
    MvPolynomial.map φ (graphRestrict f a) =
      graphRestrict (MvPolynomial.map φ f) (fun j => φ (a j)) := by
  classical
  unfold graphRestrict restrictLinear restrictHom
  rw [MvPolynomial.map_bind₁]
  apply congrArg
    (fun h : Fin (m + 1) → Poly L m =>
      MvPolynomial.bind₁ h (MvPolynomial.map φ f))
  funext i
  rw [← Matrix.toMvPolynomial_map]
  rw [graphFrame_map]

/-- Real-to-complex scalar extension for multivariate polynomials. -/
def complexify
    {n : ℕ} (f : Poly ℝ n) : Poly ℂ n :=
  MvPolynomial.map Complex.ofRealHom f

/-- Coefficientwise complex conjugation of a multivariate polynomial. -/
def conjugatePoly
    {n : ℕ} (f : Poly ℂ n) : Poly ℂ n :=
  MvPolynomial.map (starRingEnd ℂ) f

@[simp] lemma complexify_C
    {n : ℕ} (r : ℝ) :
    complexify (n := n) (MvPolynomial.C r) =
      MvPolynomial.C (r : ℂ) := by
  simp [complexify]

@[simp] lemma complexify_X
    {n : ℕ} (i : Fin n) :
    complexify (MvPolynomial.X i : Poly ℝ n) =
      (MvPolynomial.X i : Poly ℂ n) := by
  simp [complexify]

@[simp] lemma conjugatePoly_C
    {n : ℕ} (z : ℂ) :
    conjugatePoly (n := n) (MvPolynomial.C z) =
      MvPolynomial.C (star z) := by
  simp [conjugatePoly]

@[simp] lemma conjugatePoly_X
    {n : ℕ} (i : Fin n) :
    conjugatePoly (MvPolynomial.X i : Poly ℂ n) =
      MvPolynomial.X i := by
  simp [conjugatePoly]

/-- Complex conjugation is involutive on multivariate polynomials. -/
lemma conjugatePoly_conjugatePoly
    {n : ℕ} (f : Poly ℂ n) :
    conjugatePoly (conjugatePoly f) = f := by
  unfold conjugatePoly
  rw [MvPolynomial.map_map]
  have hcomp :
      (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [hcomp]
  exact MvPolynomial.map_id f

/-- A real polynomial becomes fixed by coefficientwise conjugation after
complexification. -/
lemma conjugatePoly_complexify
    {n : ℕ} (f : Poly ℝ n) :
    conjugatePoly (complexify f) = complexify f := by
  unfold conjugatePoly complexify
  rw [MvPolynomial.map_map]
  have hcomp :
      (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    simp
  rw [hcomp]

/-- Complexification commutes exactly with graph restriction at real
parameters. -/
lemma complexify_graphRestrict
    {m : ℕ} (f : Poly ℝ (m + 1))
    (a : Fin m → ℝ) :
    complexify (graphRestrict f a) =
      graphRestrict (complexify f) (fun j => (a j : ℂ)) := by
  exact map_graphRestrict Complex.ofRealHom f a

/-- Conjugation commutes with graph restriction, conjugating the graph
parameters. -/
lemma conjugatePoly_graphRestrict
    {m : ℕ} (f : Poly ℂ (m + 1))
    (a : Fin m → ℂ) :
    conjugatePoly (graphRestrict f a) =
      graphRestrict (conjugatePoly f) (fun j => star (a j)) := by
  exact map_graphRestrict (starRingEnd ℂ) f a

/-- In particular, conjugation commutes with restriction at a real parameter. -/
lemma conjugatePoly_graphRestrict_realParams
    {m : ℕ} (f : Poly ℂ (m + 1))
    (a : Fin m → ℝ) :
    conjugatePoly
        (graphRestrict f (fun j => (a j : ℂ))) =
      graphRestrict (conjugatePoly f)
        (fun j => (a j : ℂ)) := by
  simpa using
    conjugatePoly_graphRestrict f (fun j => (a j : ℂ))

/-- Complexification preserves products. -/
lemma complexify_mul
    {n : ℕ} (f g : Poly ℝ n) :
    complexify (f * g) = complexify f * complexify g := by
  simp [complexify]

/-- Conjugation preserves products. -/
lemma conjugatePoly_mul
    {n : ℕ} (f g : Poly ℂ n) :
    conjugatePoly (f * g) =
      conjugatePoly f * conjugatePoly g := by
  simp [conjugatePoly]

/-- Any complex factorization of a complexified real polynomial yields its
conjugate factorization as well. -/
lemma conjugate_factorization_of_complexify
    {n : ℕ} {f : Poly ℝ n} {g h : Poly ℂ n}
    (hfac : complexify f = g * h) :
    complexify f = conjugatePoly g * conjugatePoly h := by
  calc
    complexify f = conjugatePoly (complexify f) := by
      symm
      exact conjugatePoly_complexify f
    _ = conjugatePoly (g * h) := by rw [← hfac]
    _ = conjugatePoly g * conjugatePoly h := conjugatePoly_mul g h

/-! ### Norming a complex certificate down to real parameters

If `Δ` is a complex parameter polynomial, the product
`Δ * conjugate(Δ)` takes real values on real parameter points.  For choosing a
real point it is more convenient to keep its real and imaginary coefficient
parts separate; the next target will construct an actual real polynomial
certificate from these two parts.

The compatibility lemmas above are the hard bookkeeping needed for that
descent: all section operations now commute definitionally/propositionally
with scalar extension and conjugation.
-/

/-- A complex polynomial is conjugation-fixed exactly when it is a candidate
for descent to real coefficients.  We record the predicate without yet
postulating surjectivity of complexification onto the fixed subring. -/
def IsConjugationFixed
    {n : ℕ} (f : Poly ℂ n) : Prop :=
  conjugatePoly f = f

lemma complexify_isConjugationFixed
    {n : ℕ} (f : Poly ℝ n) :
    IsConjugationFixed (complexify f) := by
  exact conjugatePoly_complexify f

/-!
Stage-8 status
--------------

The real-descent bookkeeping no longer involves matrices or substitutions:

* `map_graphRestrict` proves restriction is natural under coefficient maps;
* `complexify_graphRestrict` handles `ℝ → ℂ`;
* `conjugatePoly_graphRestrict_realParams` shows real graph parameters are
  compatible with conjugation;
* every complex factorization of a real polynomial automatically comes with
  the conjugate factorization.

The next genuinely mathematical real lemma is the Galois/UFD statement:
an irreducible real polynomial that becomes reducible over `ℂ` has exactly one
conjugate pair of complex irreducible factors (up to units), and a specialized
pair that remains irreducible and nonassociate descends to a real irreducible
product.

No form of that theorem has been assumed here.
-/


/-! ## Stage 9: exact real descent for certificate polynomials

This section closes a point that was intentionally left open in Stage 8.
A coefficientwise conjugation-fixed complex multivariate polynomial really does
come from a real multivariate polynomial.  The proof uses Mathlib's exact
`MvPolynomial.mem_range_map_iff_coeffs_subset` criterion and the elementary
characterization of conjugation-fixed complex numbers.

The main payoff is a fully algebraic real-point lemma:

* every nonzero complex parameter polynomial `Δ` is nonzero at some point of
  `ℝ^m` (viewed inside `ℂ^m`);
* hence every complex principal-open Bertini certificate has a real parameter
  point in its principal open;
* if the resulting complexified real section is irreducible, then the original
  real section is irreducible.

No openness statement for real irreducibility is used.
-/

/-- Coefficientwise conjugation acts on each coefficient exactly as expected. -/
@[simp] lemma coeff_conjugatePoly
    {n : ℕ} (f : Poly ℂ n) (d : Fin n →₀ ℕ) :
    (conjugatePoly f).coeff d = star (f.coeff d) := by
  simp [conjugatePoly, MvPolynomial.coeff_map]

/-- Every coefficient of a conjugation-fixed polynomial is itself fixed by
complex conjugation. -/
lemma coeff_fixed_of_isConjugationFixed
    {n : ℕ} {f : Poly ℂ n}
    (hf : IsConjugationFixed f) (d : Fin n →₀ ℕ) :
    star (f.coeff d) = f.coeff d := by
  unfold IsConjugationFixed at hf
  have h := congrArg (fun p : Poly ℂ n => p.coeff d) hf
  simpa using h

/-- A conjugation-fixed complex multivariate polynomial has real coefficients,
in the strong sense that it lies in the range of coefficientwise
complexification. -/
lemma exists_real_poly_of_isConjugationFixed
    {n : ℕ} {f : Poly ℂ n}
    (hf : IsConjugationFixed f) :
    ∃ g : Poly ℝ n, complexify g = f := by
  have hrange :
      f ∈ Set.range
        (MvPolynomial.map Complex.ofRealHom : Poly ℝ n → Poly ℂ n) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    change c ∈ f.coeffs at hc
    rw [MvPolynomial.mem_coeffs_iff] at hc
    rcases hc with ⟨d, _, rfl⟩
    have hstar : star (f.coeff d) = f.coeff d :=
      coeff_fixed_of_isConjugationFixed hf d
    rcases (RCLike.conj_eq_iff_real.mp hstar) with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa using hr.symm
  rcases hrange with ⟨g, hg⟩
  exact ⟨g, hg⟩

/-- The product of a complex polynomial with its conjugate is fixed by
conjugation. -/
lemma mul_conjugate_isConjugationFixed
    {n : ℕ} (f : Poly ℂ n) :
    IsConjugationFixed (f * conjugatePoly f) := by
  unfold IsConjugationFixed
  calc
    conjugatePoly (f * conjugatePoly f) =
        conjugatePoly f * conjugatePoly (conjugatePoly f) :=
      conjugatePoly_mul f (conjugatePoly f)
    _ = conjugatePoly f * f := by
      rw [conjugatePoly_conjugatePoly]
    _ = f * conjugatePoly f := by
      exact mul_comm _ _

/-- Conjugation cannot turn a nonzero polynomial into zero. -/
lemma conjugatePoly_ne_zero
    {n : ℕ} {f : Poly ℂ n} (hf : f ≠ 0) :
    conjugatePoly f ≠ 0 := by
  intro hzero
  apply hf
  calc
    f = conjugatePoly (conjugatePoly f) :=
      (conjugatePoly_conjugatePoly f).symm
    _ = conjugatePoly 0 := by rw [hzero]
    _ = 0 := by simp [conjugatePoly]

/-- The complex norm polynomial `f * conjugate(f)` descends to an actual real
multivariate polynomial. -/
lemma exists_real_norm_poly
    {n : ℕ} (f : Poly ℂ n) :
    ∃ N : Poly ℝ n,
      complexify N = f * conjugatePoly f := by
  exact exists_real_poly_of_isConjugationFixed
    (mul_conjugate_isConjugationFixed f)

/-- If `f` is nonzero, its descended real norm polynomial is nonzero. -/
lemma exists_nonzero_real_norm_poly
    {n : ℕ} {f : Poly ℂ n} (hf : f ≠ 0) :
    ∃ N : Poly ℝ n,
      N ≠ 0 ∧ complexify N = f * conjugatePoly f := by
  obtain ⟨N, hN⟩ := exists_real_norm_poly f
  have hconj : conjugatePoly f ≠ 0 := conjugatePoly_ne_zero hf
  have hprod : f * conjugatePoly f ≠ 0 := mul_ne_zero hf hconj
  refine ⟨N, ?_, hN⟩
  intro hzero
  apply hprod
  calc
    f * conjugatePoly f = complexify N := hN.symm
    _ = complexify 0 := by rw [hzero]
    _ = 0 := by simp [complexify]

/-- Evaluating a complexified real polynomial at a real point agrees with
complexifying its real evaluation. -/
lemma eval_complexify_at_real
    {n : ℕ} (g : Poly ℝ n) (a : Fin n → ℝ) :
    MvPolynomial.eval (fun i => (a i : ℂ)) (complexify g) =
      (MvPolynomial.eval a g : ℂ) := by
  unfold complexify
  symm
  change
    Complex.ofRealHom (MvPolynomial.eval a g) =
      MvPolynomial.eval (fun i => Complex.ofRealHom (a i))
        (MvPolynomial.map Complex.ofRealHom g)
  simpa [Function.comp_apply] using
    (MvPolynomial.map_eval Complex.ofRealHom a g)

/-- If a descended real norm polynomial is nonzero at a real point, then the
original complex polynomial is nonzero at the same point. -/
lemma eval_complex_ne_zero_of_realNorm_ne_zero
    {n : ℕ} {f : Poly ℂ n} {N : Poly ℝ n}
    (hN : complexify N = f * conjugatePoly f)
    (a : Fin n → ℝ)
    (ha : MvPolynomial.eval a N ≠ 0) :
    MvPolynomial.eval (fun i => (a i : ℂ)) f ≠ 0 := by
  intro hfzero
  have hz : ((MvPolynomial.eval a N : ℝ) : ℂ) = 0 := by
    rw [← eval_complexify_at_real N a, hN]
    simp [hfzero]
  exact ha (RCLike.ofReal_injective hz)

/-- A nonzero complex multivariate polynomial is nonzero at some *real* point.

This is stronger than the Stage-7 `exists_eval_ne_zero` statement in the one
respect needed for descent: the chosen parameter can be taken in `ℝ^n`, even
though the polynomial has complex coefficients. -/
theorem exists_real_point_eval_ne_zero
    {n : ℕ} (f : Poly ℂ n) (hf : f ≠ 0) :
    ∃ a : Fin n → ℝ,
      MvPolynomial.eval (fun i => (a i : ℂ)) f ≠ 0 := by
  obtain ⟨N, hN0, hN⟩ := exists_nonzero_real_norm_poly hf
  obtain ⟨a, ha⟩ := exists_eval_ne_zero N hN0
  exact ⟨a, eval_complex_ne_zero_of_realNorm_ne_zero hN a ha⟩

/-- Every complex principal-open irreducibility certificate has a *real*
parameter point in its principal open. -/
theorem exists_real_parameter_of_complex_certificate
    {m : ℕ} {f : Poly ℂ (m + 1)}
    (hcert : HasGraphIrreducibilityCertificate ℂ f) :
    ∃ a : Fin m → ℝ,
      Irreducible
        (graphRestrict f (fun j => (a j : ℂ))) := by
  rcases hcert with ⟨Δ, hΔ, hgood⟩
  obtain ⟨a, ha⟩ := exists_real_point_eval_ne_zero Δ hΔ
  exact ⟨a, hgood (fun j => (a j : ℂ)) ha⟩

/-! ### Pulling irreducibility back from `ℂ` to `ℝ`

For the geometrically irreducible branch we also need the elementary reverse
implication: if the coefficientwise complexification of a real polynomial is
irreducible, then the original real polynomial was already irreducible.

The only nontrivial bookkeeping point is reflection of units.  Over a reduced
coefficient ring Mathlib characterizes multivariate-polynomial units as
constant unit polynomials; injectivity of `ℝ → ℂ` then reflects that property.
-/

/-- Complexification reflects units of real multivariate polynomials. -/
lemma isUnit_of_complexify_isUnit
    {n : ℕ} {f : Poly ℝ n}
    (hf : IsUnit (complexify f)) :
    IsUnit f := by
  have hvarsMap :
      (complexify f).vars = f.vars := by
    simpa [complexify] using
      (MvPolynomial.vars_map_of_injective f
        (f := Complex.ofRealHom) RCLike.ofReal_injective)
  obtain ⟨z, _, hz⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := complexify f)).mp hf
  have hfvars : f.vars = ∅ := by
    rw [← hvarsMap, hz]
    simp
  have hfC : f = MvPolynomial.C (f.coeff 0) :=
    MvPolynomial.vars_eq_empty_iff_eq_C.mp hfvars
  have hcoeff : f.coeff 0 ≠ 0 := by
    intro hzero
    have hfzero : f = 0 := by
      rw [hfC, hzero]
      simp
    have : IsUnit (0 : Poly ℂ n) := by
      simpa [hfzero, complexify] using hf
    exact not_isUnit_zero this
  exact
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := f)).mpr
      ⟨f.coeff 0, IsUnit.mk0 _ hcoeff, hfC⟩

/-- Irreducibility after complexification implies irreducibility over the
reals. -/
lemma irreducible_of_complexify_irreducible
    {n : ℕ} {f : Poly ℝ n}
    (hf : Irreducible (complexify f)) :
    Irreducible f := by
  refine ⟨?_, ?_⟩
  · intro hunit
    apply hf.not_isUnit
    simpa [complexify] using
      hunit.map (MvPolynomial.map Complex.ofRealHom)
  · intro a b hab
    have hfac :
        complexify f = complexify a * complexify b := by
      rw [hab, complexify_mul]
    rcases hf.isUnit_or_isUnit hfac with ha | hb
    · exact Or.inl (isUnit_of_complexify_isUnit ha)
    · exact Or.inr (isUnit_of_complexify_isUnit hb)

/-- Therefore a complex certificate for the complexification of a real
polynomial already produces a genuinely irreducible real graph section. -/
theorem exists_real_irreducible_graphRestrict_of_complex_certificate
    {m : ℕ} {f : Poly ℝ (m + 1)}
    (hcert :
      HasGraphIrreducibilityCertificate ℂ (complexify f)) :
    ∃ a : Fin m → ℝ,
      Irreducible (graphRestrict f a) := by
  obtain ⟨a, ha⟩ :=
    exists_real_parameter_of_complex_certificate hcert
  refine ⟨a, irreducible_of_complexify_irreducible ?_⟩
  rw [complexify_graphRestrict]
  exact ha

/-!
Stage-9 audit
-------------

New unconditional facts proved here:

1. conjugation-fixed complex multivariate polynomials descend to `ℝ`;
2. `f * conjugate(f)` has a nonzero real descendant whenever `f ≠ 0`;
3. every nonzero complex parameter polynomial is nonzero at some real point;
4. a complex principal-open Bertini certificate therefore contains a real
   parameter point;
5. complexification reflects units;
6. irreducibility over `ℂ` pulls back to irreducibility over `ℝ`;
7. consequently the entire geometrically-irreducible real branch is reduced
   to the same complex certificate used in the complex case.

The remaining upper-bound gaps are now sharply separated:

* **Complex core:** construct the certificate in `ComplexBertiniCore` without
  postulating Bertini/Noether forms as an axiom.
* **Real non-geometric branch:** if an irreducible real polynomial splits after
  complexification, formalize the quadratic Galois/UFD statement that the
  complex factors form one conjugate pair, and prove that a specialized
  nonassociate conjugate pair descends to a real irreducible product.

No `axiom`, `sorry`, `admit`, or custom theorem-interface assumption is added
in Stage 9.
-/



/-! ## Stage 10: strict Galois descent for a fixed complex factor

This stage resumes from the last *actual* strict source file, Stage 9.

There is no Bertini assumption here.  The purpose is to close the first
non-geometrically-irreducible descent layer needed over `ℝ`.

The key algebraic observation is elementary but important:

* coefficientwise conjugation is an involutive ring automorphism of
  `MvPolynomial (Fin n) ℂ`, hence preserves units, divisibility, and
  irreducibility;
* if
      `complexify f = g * q`
  with `g` fixed by conjugation, then cancellation shows that `q` is fixed by
  conjugation as well;
* both factors therefore descend to real polynomials;
* injectivity of coefficientwise complexification turns the complex
  factorization back into a genuine real factorization of `f`;
* if `f` is irreducible over `ℝ`, one of the two complex factors must therefore
  be a unit;
* consequently, in a genuine nontrivial complex splitting of an irreducible
  real polynomial, no irreducible proper factor can itself be fixed by
  conjugation.

This does not yet replace "fixed" by "associated to its conjugate"; that
normalization is the next strict target.
-/

/-- Coefficientwise complexification is injective. -/
lemma complexify_injective
    {n : ℕ} :
    Function.Injective (complexify : Poly ℝ n → Poly ℂ n) := by
  intro f g h
  exact
    MvPolynomial.map_injective
      Complex.ofRealHom RCLike.ofReal_injective h

/-- Coefficientwise conjugation preserves and reflects units. -/
lemma isUnit_conjugatePoly_iff
    {n : ℕ} (f : Poly ℂ n) :
    IsUnit (conjugatePoly f) ↔ IsUnit f := by
  constructor
  · intro h
    have hh : IsUnit (conjugatePoly (conjugatePoly f)) := by
      change
        IsUnit
          (MvPolynomial.map (starRingEnd ℂ)
            (conjugatePoly f))
      exact h.map (MvPolynomial.map (starRingEnd ℂ))
    rw [conjugatePoly_conjugatePoly] at hh
    exact hh
  · intro h
    change
      IsUnit
        (MvPolynomial.map (starRingEnd ℂ) f)
    exact h.map (MvPolynomial.map (starRingEnd ℂ))

/-- Conjugation transports divisibility in both directions. -/
lemma conjugatePoly_dvd_conjugatePoly_iff
    {n : ℕ} {f g : Poly ℂ n} :
    conjugatePoly f ∣ conjugatePoly g ↔ f ∣ g := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨conjugatePoly q, ?_⟩
    have h := congrArg conjugatePoly hq
    simpa only
      [conjugatePoly_conjugatePoly, conjugatePoly_mul] using h
  · rintro ⟨q, hq⟩
    refine ⟨conjugatePoly q, ?_⟩
    calc
      conjugatePoly g = conjugatePoly (f * q) := by rw [← hq]
      _ = conjugatePoly f * conjugatePoly q :=
        conjugatePoly_mul f q

/-- Conjugation preserves irreducibility. -/
lemma irreducible_conjugatePoly
    {n : ℕ} {f : Poly ℂ n}
    (hf : Irreducible f) :
    Irreducible (conjugatePoly f) := by
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hf.not_isUnit
      ((isUnit_conjugatePoly_iff f).mp hunit)
  · intro a b hab
    have hfac :
        f = conjugatePoly a * conjugatePoly b := by
      calc
        f = conjugatePoly (conjugatePoly f) := by
          symm
          exact conjugatePoly_conjugatePoly f
        _ = conjugatePoly (a * b) := by
          rw [← hab]
        _ = conjugatePoly a * conjugatePoly b :=
          conjugatePoly_mul a b
    rcases hf.isUnit_or_isUnit hfac with ha | hb
    · exact Or.inl ((isUnit_conjugatePoly_iff a).mp ha)
    · exact Or.inr ((isUnit_conjugatePoly_iff b).mp hb)

/-- Irreducibility is invariant under coefficientwise conjugation. -/
lemma irreducible_conjugatePoly_iff
    {n : ℕ} (f : Poly ℂ n) :
    Irreducible (conjugatePoly f) ↔ Irreducible f := by
  constructor
  · intro h
    have hh :=
      irreducible_conjugatePoly
        (f := conjugatePoly f) h
    rw [conjugatePoly_conjugatePoly] at hh
    exact hh
  · exact irreducible_conjugatePoly

/-- If the left factor of a factorization of a complexified real polynomial
is fixed by conjugation, then the quotient is fixed as well.

The only input beyond functoriality is cancellation by the nonzero left
factor. -/
lemma quotient_isConjugationFixed_of_fixed_left_factor
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hg0 : g ≠ 0)
    (hgfix : IsConjugationFixed g)
    (hfac : complexify f = g * q) :
    IsConjugationFixed q := by
  have hfacConj :
      complexify f =
        conjugatePoly g * conjugatePoly q :=
    conjugate_factorization_of_complexify hfac
  unfold IsConjugationFixed at hgfix ⊢
  rw [hgfix] at hfacConj
  have hcancel :
      g * q = g * conjugatePoly q := by
    calc
      g * q = complexify f := hfac.symm
      _ = g * conjugatePoly q := hfacConj
  exact (mul_left_cancel₀ hg0 hcancel).symm

/-- A conjugation-fixed complex factorization of a complexified real
polynomial descends term-by-term to a genuine real factorization. -/
lemma real_factorization_of_fixed_complex_factor
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hg0 : g ≠ 0)
    (hgfix : IsConjugationFixed g)
    (hfac : complexify f = g * q) :
    ∃ gr qr : Poly ℝ n,
      complexify gr = g ∧
      complexify qr = q ∧
      f = gr * qr := by
  have hqfix :
      IsConjugationFixed q :=
    quotient_isConjugationFixed_of_fixed_left_factor
      hg0 hgfix hfac
  obtain ⟨gr, hgr⟩ :=
    exists_real_poly_of_isConjugationFixed hgfix
  obtain ⟨qr, hqr⟩ :=
    exists_real_poly_of_isConjugationFixed hqfix
  refine ⟨gr, qr, hgr, hqr, ?_⟩
  apply complexify_injective
  calc
    complexify f = g * q := hfac
    _ = complexify gr * complexify qr := by
      rw [hgr, hqr]
    _ = complexify (gr * qr) := by
      symm
      exact complexify_mul gr qr

/-- For an irreducible real polynomial, any factorization of its
complexification whose left factor is conjugation-fixed has a unit factor. -/
lemma isUnit_or_isUnit_of_fixed_complex_factor
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hf : Irreducible f)
    (hg0 : g ≠ 0)
    (hgfix : IsConjugationFixed g)
    (hfac : complexify f = g * q) :
    IsUnit g ∨ IsUnit q := by
  obtain ⟨gr, qr, hgr, hqr, hreal⟩ :=
    real_factorization_of_fixed_complex_factor
      hg0 hgfix hfac
  rcases hf.isUnit_or_isUnit hreal with hgrU | hqrU
  · left
    rw [← hgr]
    change
      IsUnit
        (MvPolynomial.map Complex.ofRealHom gr)
    exact hgrU.map (MvPolynomial.map Complex.ofRealHom)
  · right
    rw [← hqr]
    change
      IsUnit
        (MvPolynomial.map Complex.ofRealHom qr)
    exact hqrU.map (MvPolynomial.map Complex.ofRealHom)

/-- If the fixed left factor is itself irreducible, then the quotient must be
a unit. -/
lemma quotient_isUnit_of_fixed_irreducible_factor
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hf : Irreducible f)
    (hg : Irreducible g)
    (hgfix : IsConjugationFixed g)
    (hfac : complexify f = g * q) :
    IsUnit q := by
  rcases
      isUnit_or_isUnit_of_fixed_complex_factor
        hf hg.ne_zero hgfix hfac with hgU | hqU
  · exact False.elim (hg.not_isUnit hgU)
  · exact hqU

/-- Hence an irreducible proper factor in a genuine nontrivial complex
splitting of an irreducible real polynomial cannot be literally fixed by
conjugation. -/
lemma irreducible_factor_not_conjugationFixed
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hf : Irreducible f)
    (hg : Irreducible g)
    (hq : ¬ IsUnit q)
    (hfac : complexify f = g * q) :
    ¬ IsConjugationFixed g := by
  intro hgfix
  exact hq
    (quotient_isUnit_of_fixed_irreducible_factor
      hf hg hgfix hfac)

/-!
Stage-10 audit
--------------

This stage adds no mathematical assumption.

The real non-geometric branch has advanced from mere functoriality to an
actual descent theorem:

* conjugation preserves units, divisibility, and irreducibility;
* a fixed complex factor forces its quotient to be fixed;
* the whole factorization then descends to `ℝ`;
* irreducibility over `ℝ` forces a unit factor;
* therefore a proper irreducible factor of a genuine complex splitting cannot
  be conjugation-fixed.

The remaining local Galois step is sharper: rule out not merely
`conjugatePoly g = g`, but
`Associated (conjugatePoly g) g`.
That requires normalizing an associate-to-conjugate factor by a scalar unit.
After that, the real non-geometric branch can be reduced to a conjugate pair.

The global hard input remains the complex fixed-point Bertini certificate.
-/



/-! ## Stage 11: normalize an associate-to-conjugate factor

Stage 10 ruled out a proper irreducible complex factor that is literally fixed
by conjugation.  For the Galois argument we need the stronger statement that a
proper irreducible factor cannot even be *associated* to its conjugate.

The normalization below avoids extracting a square root of a phase.

Suppose
    `g * u = conjugatePoly g`
for a polynomial unit `u`.  Since a unit in a multivariate polynomial ring
over a field is constant, write `u = C z`.  Choose one nonzero coefficient
`c = coeff d g`.  Comparing the `d`-th coefficient gives
    `c * z = star c`.
Hence
    `h := C (star c) * g`
satisfies `conjugatePoly h = h`.  Moreover `h` is associated to `g`.

This elementary coefficient normalization is exactly what is needed to reduce
the associated case to the fixed case proved in Stage 10.
-/

/-- If a nonzero complex polynomial is associated to its conjugate, then some
associate of it is literally fixed by conjugation. -/
lemma exists_conjugationFixed_associate_of_associated_conjugate
    {n : ℕ} {g : Poly ℂ n}
    (hg0 : g ≠ 0)
    (hassoc : Associated g (conjugatePoly g)) :
    ∃ h : Poly ℂ n,
      IsConjugationFixed h ∧ Associated h g := by
  rcases hassoc with ⟨u, hu⟩
  obtain ⟨z, hzU, huz⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := (u : Poly ℂ n))).mp u.isUnit
  rw [huz] at hu

  obtain ⟨d, hd⟩ :=
    MvPolynomial.exists_coeff_ne_zero hg0
  let c : ℂ := g.coeff d
  have hc : c ≠ 0 := by
    simpa [c] using hd

  have hcz : c * z = star c := by
    have hcoeff :=
      congrArg (fun p : Poly ℂ n => p.coeff d) hu
    rw [mul_comm g (MvPolynomial.C z)] at hcoeff
    simpa [c] using hcoeff

  let h : Poly ℂ n :=
    MvPolynomial.C (star c) * g

  have hcstar : star c ≠ 0 := by
    exact (star_ne_zero.mpr hc)

  have hCunit :
      IsUnit (MvPolynomial.C (star c) : Poly ℂ n) := by
    exact
      (IsUnit.mk0 (star c) hcstar).map
        (MvPolynomial.C : ℂ →+* Poly ℂ n)

  refine ⟨h, ?_, ?_⟩
  · unfold IsConjugationFixed
    dsimp [h]
    calc
      conjugatePoly
          (MvPolynomial.C (star c) * g) =
        conjugatePoly (MvPolynomial.C (star c)) *
          conjugatePoly g :=
        conjugatePoly_mul
          (MvPolynomial.C (star c)) g
      _ =
        MvPolynomial.C c *
          (g * MvPolynomial.C z) := by
        rw [conjugatePoly_C, star_star, ← hu]
      _ =
        MvPolynomial.C (c * z) * g := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ =
        MvPolynomial.C (star c) * g := by
        rw [hcz]
  · dsimp [h]
    exact
      associated_unit_mul_left
        g (MvPolynomial.C (star c)) hCunit

/-- If `g` is nonzero and is associated to `g * q`, then `q` is a unit.

This is just cancellation of the unit appearing in the definition of
`Associated`. -/
lemma isUnit_right_of_associated_self_mul
    {n : ℕ} {g q : Poly ℂ n}
    (hg0 : g ≠ 0)
    (hassoc : Associated g (g * q)) :
    IsUnit q := by
  rcases hassoc with ⟨u, hu⟩
  have hq :
      (u : Poly ℂ n) = q :=
    mul_left_cancel₀ hg0 hu
  rw [← hq]
  exact u.isUnit

/-- Main Stage-11 upgrade: in a genuine nontrivial complex splitting of an
irreducible real polynomial, a proper irreducible factor is not associated to
its conjugate. -/
lemma irreducible_factor_not_associated_conjugate
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hf : Irreducible f)
    (hg : Irreducible g)
    (hq : ¬ IsUnit q)
    (hfac : complexify f = g * q) :
    ¬ Associated g (conjugatePoly g) := by
  intro hassoc

  obtain ⟨h, hhfix, hhassoc⟩ :=
    exists_conjugationFixed_associate_of_associated_conjugate
      hg.ne_zero hassoc

  have hhirr : Irreducible h :=
    (hhassoc.irreducible_iff).mpr hg

  have hgDvd :
      g ∣ complexify f := by
    exact ⟨q, hfac⟩

  have hhDvd :
      h ∣ complexify f :=
    (hhassoc.dvd_iff_dvd_left).mpr hgDvd

  rcases hhDvd with ⟨qh, hfacH⟩

  have hqhU : IsUnit qh :=
    quotient_isUnit_of_fixed_irreducible_factor
      hf hhirr hhfix hfacH

  have hhAssocF :
      Associated h (complexify f) := by
    rw [hfacH]
    exact associated_mul_unit_right h qh hqhU

  have hgAssocF :
      Associated g (complexify f) :=
    hhassoc.symm.trans hhAssocF

  have hgAssocProd :
      Associated g (g * q) := by
    simpa [hfac] using hgAssocF

  exact hq
    (isUnit_right_of_associated_self_mul
      hg.ne_zero hgAssocProd)

/-!
Stage-11 audit
--------------

The local Galois obstruction is now strengthened from equality to association:

    if `f : ℝ[x]` is irreducible and
       `complexify f = g * q`
    is a nontrivial factorization with irreducible `g`, then

       `¬ Associated g (conjugatePoly g)`.

Thus any irreducible factor extracted from a genuine complex splitting lies in
a two-element conjugation orbit at the level of associates.

No square-root choice, Hilbert-90 theorem, factorization-list API, Bertini
statement, or additional assumption is used.

The next strict algebraic target is to exploit primality/UFD factorization to
show that the conjugate orbit already exhausts the complexification:
`complexify f` is associated to `g * conjugatePoly g`.
-/



/-! ## Stage 12: the conjugate pair exhausts the complexification

We now use only primality of irreducibles in the UFD
`MvPolynomial (Fin n) ℂ`.

Suppose
    `complexify f = g * q`
is a genuine factorization, where `f` is irreducible over `ℝ` and `g` is
irreducible over `ℂ`.

Stage 11 gives `g` not associated to `conjugatePoly g`.  Since
`conjugatePoly g` also divides `complexify f`, primality forces it to divide
`q`.  Thus
    `complexify f = (g * conjugatePoly g) * r`.
The first factor is conjugation-fixed.  Cancellation therefore makes `r`
conjugation-fixed as well, so Stage 10 descends the factorization to `ℝ`.
Real irreducibility then forces `r` to be a unit.

This proves the desired "one conjugate pair, up to a unit" statement without
formalizing a complete factor multiset.
-/

/-- A proper irreducible complex factor of an irreducible real polynomial
comes with its conjugate, and the remaining quotient is a unit. -/
lemma complexify_eq_conjugate_pair_mul_unit_of_irreducible_factor
    {n : ℕ}
    {f : Poly ℝ n} {g q : Poly ℂ n}
    (hf : Irreducible f)
    (hg : Irreducible g)
    (hq : ¬ IsUnit q)
    (hfac : complexify f = g * q) :
    ∃ r : Poly ℂ n,
      IsUnit r ∧
      complexify f =
        (g * conjugatePoly g) * r := by
  have hgNotAssoc :
      ¬ Associated g (conjugatePoly g) :=
    irreducible_factor_not_associated_conjugate
      hf hg hq hfac

  have hgDvd :
      g ∣ complexify f := by
    exact ⟨q, hfac⟩

  have hconjDvd0 :
      conjugatePoly g ∣
        conjugatePoly (complexify f) :=
    (conjugatePoly_dvd_conjugatePoly_iff).2 hgDvd

  have hconjDvd :
      conjugatePoly g ∣ complexify f := by
    simpa [conjugatePoly_complexify] using hconjDvd0

  have hconjDvdProd :
      conjugatePoly g ∣ g * q := by
    rw [← hfac]
    exact hconjDvd

  have hconjIrr :
      Irreducible (conjugatePoly g) :=
    irreducible_conjugatePoly hg

  have hconjPrime :
      Prime (conjugatePoly g) :=
    hconjIrr.prime

  rcases hconjPrime.dvd_or_dvd hconjDvdProd with hcg | hcq
  · have hAssocCG :
        Associated (conjugatePoly g) g :=
      hconjIrr.associated_of_dvd hg hcg
    exact False.elim (hgNotAssoc hAssocCG.symm)
  · rcases hcq with ⟨r, hr⟩

    have hpairFac :
        complexify f =
          (g * conjugatePoly g) * r := by
      calc
        complexify f = g * q := hfac
        _ = g * (conjugatePoly g * r) := by
          rw [hr]
        _ = (g * conjugatePoly g) * r := by
          rw [mul_assoc]

    have hpair0 :
        g * conjugatePoly g ≠ 0 := by
      exact mul_ne_zero hg.ne_zero hconjIrr.ne_zero

    have hpairFix :
        IsConjugationFixed
          (g * conjugatePoly g) :=
      mul_conjugate_isConjugationFixed g

    have hunitOr :
        IsUnit (g * conjugatePoly g) ∨
          IsUnit r :=
      isUnit_or_isUnit_of_fixed_complex_factor
        hf hpair0 hpairFix hpairFac

    have hrU : IsUnit r := by
      rcases hunitOr with hpairU | hrU
      · have hgU : IsUnit g :=
          (IsUnit.mul_iff.mp hpairU).1
        exact False.elim (hg.not_isUnit hgU)
      · exact hrU

    exact ⟨r, hrU, hpairFac⟩

/-- If the complexification of an irreducible real polynomial is reducible,
then it is, up to a unit, one nonassociate conjugate pair of irreducibles.

This theorem also performs the extraction of the first irreducible factor
using well-founded factorization; no factor-list theorem is assumed. -/
theorem exists_conjugate_pair_factorization_of_complexify
    {n : ℕ} {f : Poly ℝ n}
    (hf : Irreducible f)
    (hred : ¬ Irreducible (complexify f)) :
    ∃ g r : Poly ℂ n,
      Irreducible g ∧
      ¬ Associated g (conjugatePoly g) ∧
      IsUnit r ∧
      complexify f =
        (g * conjugatePoly g) * r := by
  have hcf0 : complexify f ≠ 0 := by
    intro hzero
    apply hf.ne_zero
    apply complexify_injective
    simpa [complexify] using hzero

  have hcfNonunit :
      ¬ IsUnit (complexify f) := by
    intro hunit
    exact hf.not_isUnit
      (isUnit_of_complexify_isUnit hunit)

  rcases irreducible_or_factor hcfNonunit with hI | hsplit
  · exact False.elim (hred hI)
  · rcases hsplit with
      ⟨a, b, haNonunit, hbNonunit, hab⟩

    have ha0 : a ≠ 0 := by
      intro ha
      apply hcf0
      rw [hab, ha, zero_mul]

    obtain ⟨g, hg, hgDvdA⟩ :=
      WfDvdMonoid.exists_irreducible_factor
        haNonunit ha0

    rcases hgDvdA with ⟨s, hs⟩

    let q : Poly ℂ n := s * b

    have hfac :
        complexify f = g * q := by
      dsimp [q]
      calc
        complexify f = a * b := hab
        _ = (g * s) * b := by rw [hs]
        _ = g * (s * b) := by
          rw [mul_assoc]

    have hqNonunit : ¬ IsUnit q := by
      intro hqU
      have hbU : IsUnit b := by
        dsimp [q] at hqU
        exact (IsUnit.mul_iff.mp hqU).2
      exact hbNonunit hbU

    have hgNotAssoc :
        ¬ Associated g (conjugatePoly g) :=
      irreducible_factor_not_associated_conjugate
        hf hg hqNonunit hfac

    obtain ⟨r, hrU, hpair⟩ :=
      complexify_eq_conjugate_pair_mul_unit_of_irreducible_factor
        hf hg hqNonunit hfac

    exact
      ⟨g, r, hg, hgNotAssoc, hrU, hpair⟩

/-!
Stage-12 audit
--------------

The real Galois/UFD structure is now reduced to a clean theorem with no
factor-list machinery:

if an irreducible real polynomial becomes reducible over `ℂ`, then

    `complexify f = (g * conjugatePoly g) * r`

for an irreducible `g`, with

    `¬ Associated g (conjugatePoly g)`

and a unit `r`.

Hence, up to a harmless scalar unit, the complexification has exactly one
conjugate pair.

The remaining real-side work for Bertini is therefore specialization:
choose a real graph parameter for which the two conjugate specialized factors
stay irreducible and nonassociate, then descend their product.

The only global existence input still missing is the strict proof of the
complex fixed-point Bertini certificate itself.
-/



/-! ## Stage 13: a specialized conjugate pair descends to a real irreducible

This is the converse descent statement needed after specialization.

Assume a real polynomial `p` has complexification
    `complexify p = (g * conjugatePoly g) * u`,
where `g` is irreducible, is not associated to its conjugate, and `u` is a
unit.  Then `p` is irreducible over `ℝ`.

Indeed, in any real factorization `p = a * b`, primality of `g` says that `g`
divides one complexified factor.  Because that factor is fixed by conjugation,
`conjugatePoly g` divides the same factor.  Nonassociation of the two
irreducibles makes them relatively prime, so their product divides that
factor.  Cancelling the pair from the total factorization leaves the other
factor dividing a unit, hence that real factor is a unit.

This lemma cleanly separates the remaining Bertini work from Galois descent.
-/

/-- Two nonassociated irreducibles are relatively prime. -/
lemma isRelPrime_of_irreducible_not_associated
    {n : ℕ} {g h : Poly ℂ n}
    (hg : Irreducible g)
    (hh : Irreducible h)
    (hna : ¬ Associated g h) :
    IsRelPrime g h := by
  apply hg.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact hna (hg.associated_of_dvd hh hdiv)

/-- If `g` divides the complexification of a real polynomial, then its
conjugate divides the same complexification. -/
lemma conjugate_dvd_complexify_of_dvd
    {n : ℕ} {a : Poly ℝ n} {g : Poly ℂ n}
    (hdiv : g ∣ complexify a) :
    conjugatePoly g ∣ complexify a := by
  have h :=
    (conjugatePoly_dvd_conjugatePoly_iff).2 hdiv
  simpa [conjugatePoly_complexify] using h

/-- A nonassociated conjugate pair dividing a complexified real polynomial
divides it as a product. -/
lemma mul_conjugate_dvd_complexify_of_dvd
    {n : ℕ} {a : Poly ℝ n} {g : Poly ℂ n}
    (hg : Irreducible g)
    (hna : ¬ Associated g (conjugatePoly g))
    (hdiv : g ∣ complexify a) :
    g * conjugatePoly g ∣ complexify a := by
  have hgcIrr :
      Irreducible (conjugatePoly g) :=
    irreducible_conjugatePoly hg
  have hrel :
      IsRelPrime g (conjugatePoly g) :=
    isRelPrime_of_irreducible_not_associated
      hg hgcIrr hna
  have hconj :
      conjugatePoly g ∣ complexify a :=
    conjugate_dvd_complexify_of_dvd hdiv
  exact hrel.mul_dvd hdiv hconj

/-- Main converse descent theorem for the real non-geometric branch. -/
theorem irreducible_real_of_complexify_conjugate_pair
    {n : ℕ}
    {p : Poly ℝ n} {g u : Poly ℂ n}
    (hg : Irreducible g)
    (hna : ¬ Associated g (conjugatePoly g))
    (hu : IsUnit u)
    (hpair :
      complexify p =
        (g * conjugatePoly g) * u) :
    Irreducible p := by
  have hpNonunit : ¬ IsUnit p := by
    intro hpU
    have hcpU : IsUnit (complexify p) := by
      change
        IsUnit
          (MvPolynomial.map Complex.ofRealHom p)
      exact hpU.map (MvPolynomial.map Complex.ofRealHom)
    have hpairU :
        IsUnit (g * conjugatePoly g) := by
      rw [hpair] at hcpU
      exact (IsUnit.mul_iff.mp hcpU).1
    have hgU : IsUnit g :=
      (IsUnit.mul_iff.mp hpairU).1
    exact hg.not_isUnit hgU

  refine ⟨hpNonunit, ?_⟩
  intro a b hab

  have hcomplexFac :
      complexify p =
        complexify a * complexify b := by
    calc
      complexify p = complexify (a * b) := by rw [hab]
      _ = complexify a * complexify b :=
        complexify_mul a b

  have hgDvdTotal :
      g ∣ complexify p := by
    rw [hpair]
    exact dvd_mul_of_dvd_left (dvd_mul_right g (conjugatePoly g)) u

  have hgPrime : Prime g := hg.prime

  have hgDvdAB :
      g ∣ complexify a * complexify b := by
    rw [← hcomplexFac]
    exact hgDvdTotal

  rcases hgPrime.dvd_or_dvd hgDvdAB with hga | hgb
  · have hpairDvdA :
        g * conjugatePoly g ∣ complexify a :=
      mul_conjugate_dvd_complexify_of_dvd
        hg hna hga
    rcases hpairDvdA with ⟨s, hs⟩

    have hpair0 :
        g * conjugatePoly g ≠ 0 := by
      exact mul_ne_zero hg.ne_zero
        (irreducible_conjugatePoly hg).ne_zero

    have hcancel :
        s * complexify b = u := by
      apply mul_left_cancel₀ hpair0
      calc
        (g * conjugatePoly g) *
            (s * complexify b) =
          ((g * conjugatePoly g) * s) *
            complexify b := by
              ac_rfl
        _ = complexify a * complexify b := by
              rw [← hs]
        _ = complexify p := hcomplexFac.symm
        _ = (g * conjugatePoly g) * u := hpair

    have hcbU : IsUnit (complexify b) := by
      have hprodU : IsUnit (s * complexify b) := by
        rw [hcancel]
        exact hu
      exact (IsUnit.mul_iff.mp hprodU).2

    exact Or.inr (isUnit_of_complexify_isUnit hcbU)

  · have hpairDvdB :
        g * conjugatePoly g ∣ complexify b :=
      mul_conjugate_dvd_complexify_of_dvd
        hg hna hgb
    rcases hpairDvdB with ⟨s, hs⟩

    have hpair0 :
        g * conjugatePoly g ≠ 0 := by
      exact mul_ne_zero hg.ne_zero
        (irreducible_conjugatePoly hg).ne_zero

    have hcancel :
        complexify a * s = u := by
      apply mul_right_cancel₀ hpair0
      calc
        (complexify a * s) *
            (g * conjugatePoly g) =
          complexify a *
            ((g * conjugatePoly g) * s) := by
              ac_rfl
        _ = complexify a * complexify b := by
              rw [← hs]
        _ = complexify p := hcomplexFac.symm
        _ = (g * conjugatePoly g) * u := hpair
        _ = u * (g * conjugatePoly g) := by
              ac_rfl

    have hcaU : IsUnit (complexify a) := by
      have hprodU : IsUnit (complexify a * s) := by
        rw [hcancel]
        exact hu
      exact (IsUnit.mul_iff.mp hprodU).1

    exact Or.inl (isUnit_of_complexify_isUnit hcaU)

/-!
Stage-13 audit
--------------

The real non-geometric descent is now algebraically closed *conditional only on
having a good specialization*:

    complexify p = (g * conjugatePoly g) * unit
    + Irreducible g
    + not Associated g (conjugatePoly g)
    -------------------------------------------------
    Irreducible p.

Thus no further Galois/UFD theorem is needed for the real branch.

What remains is parameter selection:
1. preserve irreducibility of a chosen complex factor under graph restriction;
2. simultaneously preserve nonassociation with its conjugate;
3. obtain both conditions at one real parameter.

Those are geometric/generic-specialization statements and should be reduced to
the single complex Bertini certificate core rather than introduced as new
axioms.
-/



/-! ## Stage 14: the conjugate pencil is irreducible

We now formalize the auxiliary pencil
\[
  H_g(Z,X)=g(X)+Z\,\overline{g}(X).
\]

This is the clean algebraic device for converting the condition
"`g` is not associated to its conjugate" into irreducibility of one more
polynomial.

The proof uses only:
* `MvPolynomial.finSuccEquiv`, identifying `n+1` variables with a univariate
  polynomial over `MvPolynomial (Fin n)`;
* the degree-one primitive criterion
  `Polynomial.irreducible_C_mul_X_add_C`;
* the Stage-13 fact that two nonassociated irreducibles are relatively prime.

No Bertini theorem or specialization theorem is used in this stage.
-/

/-- Irreducibility is invariant under a ring equivalence.

We record this explicitly so that the auxiliary pencil can be moved through
`MvPolynomial.finSuccEquiv` without relying on a hidden theorem interface. -/
lemma irreducible_ringEquiv_iff
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) :
    Irreducible (e a) ↔ Irreducible a := by
  constructor
  · intro ha
    refine ⟨?_, ?_⟩
    · intro hunit
      exact ha.not_isUnit (hunit.map e.toRingHom)
    · intro b c hbc
      have hfac : e a = e b * e c := by
        simpa using congrArg e hbc
      rcases ha.isUnit_or_isUnit hfac with hb | hc
      · left
        have hb' := hb.map e.symm.toRingHom
        simpa using hb'
      · right
        have hc' := hc.map e.symm.toRingHom
        simpa using hc'
  · intro ha
    refine ⟨?_, ?_⟩
    · intro hunit
      have hback := hunit.map e.symm.toRingHom
      exact ha.not_isUnit (by simpa using hback)
    · intro b c hbc
      have hback :
          a = e.symm b * e.symm c := by
        have h := congrArg e.symm hbc
        simpa using h
      rcases ha.isUnit_or_isUnit hback with hb | hc
      · left
        have hb' := hb.map e.toRingHom
        simpa using hb'
      · right
        have hc' := hc.map e.toRingHom
        simpa using hc'

/-- The auxiliary conjugate pencil, first expressed as an ordinary univariate
polynomial over the coefficient ring `Poly ℂ n`.

The order is chosen as
`C (conjugatePoly g) * X + C g`, so evaluation at `z` is
`g + z * conjugate(g)`. -/
def conjugatePencilPoly
    {n : ℕ} (g : Poly ℂ n) :
    Polynomial (Poly ℂ n) :=
  Polynomial.C (conjugatePoly g) * Polynomial.X +
    Polynomial.C g

/-- If `g` is irreducible and not associated to its conjugate, the auxiliary
degree-one pencil is irreducible over the polynomial coefficient ring. -/
lemma conjugatePencilPoly_irreducible
    {n : ℕ} {g : Poly ℂ n}
    (hg : Irreducible g)
    (hna : ¬ Associated g (conjugatePoly g)) :
    Irreducible (conjugatePencilPoly g) := by
  have hcg :
      Irreducible (conjugatePoly g) :=
    irreducible_conjugatePoly hg
  have hrel0 :
      IsRelPrime g (conjugatePoly g) :=
    isRelPrime_of_irreducible_not_associated
      hg hcg hna
  have hrel :
      IsRelPrime (conjugatePoly g) g :=
    hrel0.symm
  exact
    Polynomial.irreducible_C_mul_X_add_C
      hcg.ne_zero hrel

/-- The same pencil as an honest multivariate polynomial in `n+1` variables.

Under `finSuccEquiv`, variable `0` is the new pencil variable `Z`, while
variables `1,...,n` are the original variables. -/
def conjugatePencil
    {n : ℕ} (g : Poly ℂ n) :
    Poly ℂ (n + 1) :=
  (MvPolynomial.finSuccEquiv ℂ n).symm
    (conjugatePencilPoly g)

@[simp] lemma finSuccEquiv_conjugatePencil
    {n : ℕ} (g : Poly ℂ n) :
    MvPolynomial.finSuccEquiv ℂ n
        (conjugatePencil g) =
      conjugatePencilPoly g := by
  simp [conjugatePencil]

/-- The multivariate auxiliary pencil is irreducible. -/
lemma conjugatePencil_irreducible
    {n : ℕ} {g : Poly ℂ n}
    (hg : Irreducible g)
    (hna : ¬ Associated g (conjugatePoly g)) :
    Irreducible (conjugatePencil g) := by
  have hp :
      Irreducible (conjugatePencilPoly g) :=
    conjugatePencilPoly_irreducible hg hna
  have hiff :=
    irreducible_ringEquiv_iff
      (MvPolynomial.finSuccEquiv ℂ n).symm.toRingEquiv
      (conjugatePencilPoly g)
  exact hiff.mpr hp

/-- Exact pointwise semantics of the auxiliary pencil:
\[
H_g(z,x)=g(x)+z\,\overline g(x).
\]
-/
lemma eval_conjugatePencil
    {n : ℕ} (g : Poly ℂ n)
    (z : ℂ) (x : Fin n → ℂ) :
    MvPolynomial.eval (Fin.cons z x)
        (conjugatePencil g) =
      MvPolynomial.eval x g +
        z * MvPolynomial.eval x (conjugatePoly g) := by
  rw [MvPolynomial.eval_eq_eval_mv_eval']
  simp [conjugatePencil, conjugatePencilPoly]
  ring

/-- At `Z = 0`, the auxiliary pencil restricts exactly to `g`. -/
@[simp] lemma eval_conjugatePencil_zero
    {n : ℕ} (g : Poly ℂ n)
    (x : Fin n → ℂ) :
    MvPolynomial.eval (Fin.cons 0 x)
        (conjugatePencil g) =
      MvPolynomial.eval x g := by
  simp [eval_conjugatePencil]

/-- At `Z = 1`, the auxiliary pencil evaluates to `g + conjugate(g)`. -/
@[simp] lemma eval_conjugatePencil_one
    {n : ℕ} (g : Poly ℂ n)
    (x : Fin n → ℂ) :
    MvPolynomial.eval (Fin.cons 1 x)
        (conjugatePencil g) =
      MvPolynomial.eval x g +
        MvPolynomial.eval x (conjugatePoly g) := by
  simp [eval_conjugatePencil]

/-!
Stage-14 audit
--------------

The auxiliary pencil is now a genuine Lean object and its irreducibility is
proved from ordinary UFD algebra:

    Irreducible g
    + ¬ Associated g (conjugatePoly g)
    -----------------------------------
    Irreducible (conjugatePencil g).

This is a substantive reduction: preserving nonassociation after
specialization no longer needs an independent Galois theorem.  It can be
forced by arranging irreducibility of a suitable specialization of this
single irreducible auxiliary polynomial.

The remaining issue is geometric bookkeeping: a Bertini section of the pencil
must be related to the *same* graph parameter used to section `g`.
That compatibility is the next strict target.

No `axiom`, `sorry`, `admit`, or custom Bertini assumption is introduced.
-/



/-! ## Stage 15: same-parameter compatibility for the conjugate pencil

For a real graph parameter `a : Fin m → ℝ`, the auxiliary pencil in one extra
variable must be sectioned with parameter `(0,a)`.

The leading zero is essential: the new pencil variable `Z` is kept as a free
coordinate, while only the *last original spatial variable* is eliminated.

This stage proves the exact identity
\[
  \operatorname{graphRestrict}(H_g,(0,a))
  =
  H_{\operatorname{graphRestrict}(g,a)}.
\]

Thus, at one and the same real parameter `a`:
* irreducibility of the section of `g`, and
* irreducibility of the corresponding section of `H_g`

force the specialized factor to remain nonassociate to its conjugate.
-/

/-- View a real graph parameter as a complex graph parameter. -/
def complexGraphParamOfReal
    {m : ℕ} (a : Fin m → ℝ) :
    Fin m → ℂ :=
  fun j => (a j : ℂ)

/-- The graph parameter for the auxiliary pencil: keep the new variable `Z`
free by putting coefficient zero in front of it, and use the original real
graph parameter on the remaining coordinates. -/
def pencilGraphParamOfReal
    {m : ℕ} (a : Fin m → ℝ) :
    Fin (m + 1) → ℂ :=
  Fin.cons 0 (complexGraphParamOfReal a)

@[simp] lemma pencilGraphParamOfReal_zero
    {m : ℕ} (a : Fin m → ℝ) :
    pencilGraphParamOfReal a 0 = 0 := by
  simp [pencilGraphParamOfReal]

@[simp] lemma pencilGraphParamOfReal_succ
    {m : ℕ} (a : Fin m → ℝ)
    (j : Fin m) :
    pencilGraphParamOfReal a j.succ = (a j : ℂ) := by
  simp [pencilGraphParamOfReal, complexGraphParamOfReal]

/-- Point-level compatibility of the two graph constructions.

The left side first adjoins the pencil coordinate and then takes the graph
hyperplane with parameter `(0,a)`.  The right side keeps the pencil coordinate
and applies the original graph point construction to the spatial coordinates.
-/
lemma graphPoint_pencilGraphParamOfReal
    {m : ℕ} (a : Fin m → ℝ)
    (z : ℂ) (x : Fin m → ℂ) :
    graphPoint (pencilGraphParamOfReal a)
        (Fin.cons z x) =
      Fin.cons z
        (graphPoint (complexGraphParamOfReal a) x) := by
  funext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simp only [graphPoint_last]
    simp [pencilGraphParamOfReal, complexGraphParamOfReal,
      Fin.sum_univ_succ]
  · simp only [graphPoint_castSucc]
    refine Fin.cases ?_ (fun j => ?_) r
    · simp
    · simp

/-- **Same-parameter pencil restriction identity.**

For a real parameter `a`, restricting the global auxiliary pencil with
parameter `(0,a)` is exactly the auxiliary pencil of the restricted factor.
-/
lemma graphRestrict_conjugatePencil_realParam
    {m : ℕ}
    (g : Poly ℂ (m + 1))
    (a : Fin m → ℝ) :
    graphRestrict (conjugatePencil g)
        (pencilGraphParamOfReal a) =
      conjugatePencil
        (graphRestrict g
          (complexGraphParamOfReal a)) := by
  apply MvPolynomial.funext
  intro y
  rw [← Fin.cons_self_tail y]
  rw [eval_graphRestrict]
  rw [graphPoint_pencilGraphParamOfReal]
  rw [eval_conjugatePencil]
  rw [eval_conjugatePencil]
  rw [eval_graphRestrict]
  have hcomm :
      conjugatePoly
          (graphRestrict g (complexGraphParamOfReal a)) =
        graphRestrict (conjugatePoly g)
          (complexGraphParamOfReal a) := by
    change
      conjugatePoly
          (graphRestrict g (fun j => (a j : ℂ))) =
        graphRestrict (conjugatePoly g)
          (fun j => (a j : ℂ))
    exact conjugatePoly_graphRestrict_realParams g a
  rw [hcomm]
  rw [eval_graphRestrict]

/-- If an irreducible polynomial is associated to its conjugate, then its
univariate conjugate pencil is reducible. -/
lemma conjugatePencilPoly_not_irreducible_of_associated
    {n : ℕ} {g : Poly ℂ n}
    (hg : Irreducible g)
    (hassoc : Associated g (conjugatePoly g)) :
    ¬ Irreducible (conjugatePencilPoly g) := by
  intro hP
  rcases hassoc with ⟨u, hu⟩

  have hfac :
      conjugatePencilPoly g =
        Polynomial.C g *
          (Polynomial.C (u : Poly ℂ n) *
              Polynomial.X + 1) := by
    unfold conjugatePencilPoly
    rw [← hu]
    simp
    ring

  have hCgNonunit :
      ¬ IsUnit (Polynomial.C g :
        Polynomial (Poly ℂ n)) := by
    simpa [Polynomial.isUnit_C] using hg.not_isUnit

  have hu0 : (u : Poly ℂ n) ≠ 0 :=
    Units.ne_zero u

  have hlinNonunit :
      ¬ IsUnit
        (Polynomial.C (u : Poly ℂ n) *
            Polynomial.X + 1 :
          Polynomial (Poly ℂ n)) := by
    intro hunit
    rw [Polynomial.isUnit_iff] at hunit
    rcases hunit with ⟨c, _, hc⟩
    have hcoeff :=
      congrArg
        (fun p : Polynomial (Poly ℂ n) =>
          p.coeff 1) hc
    have : (u : Poly ℂ n) = 0 := by
      simpa [Polynomial.coeff_one] using hcoeff.symm
    exact hu0 this

  have hor :=
    hP.isUnit_or_isUnit hfac
  exact hor.elim hCgNonunit hlinNonunit

/-- Therefore irreducibility of both `g` and its auxiliary pencil forces
`g` not to be associated to its conjugate. -/
lemma not_associated_of_irreducible_conjugatePencil
    {n : ℕ} {g : Poly ℂ n}
    (hg : Irreducible g)
    (hP : Irreducible (conjugatePencil g)) :
    ¬ Associated g (conjugatePoly g) := by
  intro hassoc
  have hPpoly :
      Irreducible (conjugatePencilPoly g) := by
    have hiff :=
      irreducible_ringEquiv_iff
        (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv
        (conjugatePencil g)
    change
      Irreducible
        ((MvPolynomial.finSuccEquiv ℂ n).toRingEquiv
          (conjugatePencil g))
    exact hiff.mpr hP
  exact
    (conjugatePencilPoly_not_irreducible_of_associated
      hg hassoc) hPpoly

/-- **Same real parameter gives nonassociation.**

If the section of `g` at `a` is irreducible and the section of the global
auxiliary pencil at `(0,a)` is irreducible, then the specialized factor is not
associated to its conjugate. -/
theorem graphRestrict_not_associated_conjugate_of_pencil
    {m : ℕ}
    {g : Poly ℂ (m + 1)}
    {a : Fin m → ℝ}
    (hgA :
      Irreducible
        (graphRestrict g
          (complexGraphParamOfReal a)))
    (hP :
      Irreducible
        (graphRestrict (conjugatePencil g)
          (pencilGraphParamOfReal a))) :
    ¬ Associated
      (graphRestrict g
        (complexGraphParamOfReal a))
      (conjugatePoly
        (graphRestrict g
          (complexGraphParamOfReal a))) := by
  have hEq :=
    graphRestrict_conjugatePencil_realParam
      g a
  have hP' :
      Irreducible
        (conjugatePencil
          (graphRestrict g
            (complexGraphParamOfReal a))) := by
    rw [← hEq]
    exact hP
  exact
    not_associated_of_irreducible_conjugatePencil
      hgA hP'

/-!
Stage-15 audit
--------------

The "same parameter" bookkeeping is now explicit and algebraic.

At a real parameter `a`, the two desired conditions

1. `Irreducible (graphRestrict g a)`;
2. `Irreducible (graphRestrict (conjugatePencil g) (0,a))`

imply

3. the specialized factor is not associated to its conjugate.

Combining (1)+(3) with Stage 13 is enough to prove real irreducibility once
the specialized product is identified with the complexification of the real
section.

Therefore the real non-geometric branch no longer requires a separate
"nonassociation is open" theorem.  It requires only a way to choose a *single
real parameter* satisfying two irreducibility conditions.

The remaining global difficulty is consequently a simultaneous Bertini
selection problem, to be reduced next to principal-open certificates for the
complex core.

No `axiom`, `sorry`, `admit`, or external theorem interface is introduced.
-/



/-! ## Stage 16: simultaneous real parameter selection and closure of the
real non-geometric branch

Important audit correction:
a nonzero certificate polynomial in the full pencil-parameter space need not
remain nonzero on the constrained hyperplane whose first coordinate is zero.

Accordingly we do **not** silently use an arbitrary certificate for the pencil.
We isolate the exact restricted certificate needed on the same-parameter
family `(0,a)`.

Once such a restricted certificate and an ordinary certificate for `g` are
available, elementary polynomial algebra chooses one real parameter satisfying
both.  Stage 13 then proves the resulting real section irreducible.
-/

/-- Two nonzero complex parameter polynomials are simultaneously nonzero at
some real point. -/
theorem exists_real_point_two_eval_ne_zero
    {n : ℕ}
    (p q : Poly ℂ n)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a : Fin n → ℝ,
      MvPolynomial.eval
          (complexGraphParamOfReal a) p ≠ 0 ∧
      MvPolynomial.eval
          (complexGraphParamOfReal a) q ≠ 0 := by
  have hpq : p * q ≠ 0 :=
    mul_ne_zero hp hq
  obtain ⟨a, ha⟩ :=
    exists_real_point_eval_ne_zero
      (p * q) hpq
  have ha' :
      MvPolynomial.eval (complexGraphParamOfReal a) (p * q) ≠ 0 := by
    change
      MvPolynomial.eval (fun i => (a i : ℂ)) (p * q) ≠ 0
    exact ha
  refine ⟨a, ?_, ?_⟩
  · intro hp0
    apply ha'
    rw [MvPolynomial.eval_mul, hp0, zero_mul]
  · intro hq0
    apply ha'
    rw [MvPolynomial.eval_mul, hq0, mul_zero]

/-- A principal-open certificate for irreducibility of the **constrained**
pencil sections `(0,a)`.

This is stronger than an arbitrary certificate in the full `m+1` dimensional
pencil-parameter space, and it is exactly what the real descent needs.
-/
def HasRestrictedPencilIrreducibilityCertificate
    {m : ℕ}
    (g : Poly ℂ (m + 1)) : Prop :=
  ∃ Δ : Poly ℂ m,
    Δ ≠ 0 ∧
    ∀ a : Fin m → ℝ,
      MvPolynomial.eval
          (complexGraphParamOfReal a) Δ ≠ 0 →
        Irreducible
          (graphRestrict (conjugatePencil g)
            (pencilGraphParamOfReal a))

/-- An ordinary graph certificate for `g` together with a constrained pencil
certificate yields one real parameter at which both relevant sections are
irreducible. -/
theorem exists_same_real_parameter_of_graph_and_pencil_certificates
    {m : ℕ}
    {g : Poly ℂ (m + 1)}
    (hgcert :
      HasGraphIrreducibilityCertificate ℂ g)
    (hpcert :
      HasRestrictedPencilIrreducibilityCertificate g) :
    ∃ a : Fin m → ℝ,
      Irreducible
        (graphRestrict g
          (complexGraphParamOfReal a)) ∧
      Irreducible
        (graphRestrict (conjugatePencil g)
          (pencilGraphParamOfReal a)) := by
  rcases hgcert with
    ⟨Δg, hΔg0, hΔg⟩
  rcases hpcert with
    ⟨Δp, hΔp0, hΔp⟩
  obtain ⟨a, hga, hpa⟩ :=
    exists_real_point_two_eval_ne_zero
      Δg Δp hΔg0 hΔp0
  exact
    ⟨a, hΔg (complexGraphParamOfReal a) hga,
      hΔp a hpa⟩

/-- Graph restriction is multiplicative. -/
lemma graphRestrict_mul
    {K : Type*} [CommSemiring K]
    {m : ℕ}
    (f h : Poly K (m + 1))
    (a : Fin m → K) :
    graphRestrict (f * h) a =
      graphRestrict f a *
        graphRestrict h a := by
  unfold graphRestrict restrictLinear
  exact map_mul (restrictHom (graphFrame a)) f h

/-- Graph restriction sends units to units. -/
lemma isUnit_graphRestrict
    {K : Type*} [CommSemiring K]
    {m : ℕ}
    {u : Poly K (m + 1)}
    (hu : IsUnit u)
    (a : Fin m → K) :
    IsUnit (graphRestrict u a) := by
  unfold graphRestrict restrictLinear
  exact hu.map (restrictHom (graphFrame a)).toRingHom

/-- Specialize a conjugate-pair factorization of a complexified real polynomial
at a real graph parameter. -/
lemma specialized_conjugate_pair_factorization
    {m : ℕ}
    {f : Poly ℝ (m + 1)}
    {g u : Poly ℂ (m + 1)}
    (hpair :
      complexify f =
        (g * conjugatePoly g) * u)
    (a : Fin m → ℝ) :
    complexify (graphRestrict f a) =
      (graphRestrict g
          (complexGraphParamOfReal a) *
        conjugatePoly
          (graphRestrict g
            (complexGraphParamOfReal a))) *
      graphRestrict u
        (complexGraphParamOfReal a) := by
  calc
    complexify (graphRestrict f a) =
        graphRestrict (complexify f)
          (complexGraphParamOfReal a) := by
      exact complexify_graphRestrict f a
    _ =
        graphRestrict
          ((g * conjugatePoly g) * u)
          (complexGraphParamOfReal a) := by
      rw [hpair]
    _ =
        (graphRestrict g
            (complexGraphParamOfReal a) *
          graphRestrict (conjugatePoly g)
            (complexGraphParamOfReal a)) *
        graphRestrict u
          (complexGraphParamOfReal a) := by
      rw [graphRestrict_mul, graphRestrict_mul]
    _ =
        (graphRestrict g
            (complexGraphParamOfReal a) *
          conjugatePoly
            (graphRestrict g
              (complexGraphParamOfReal a))) *
        graphRestrict u
          (complexGraphParamOfReal a) := by
      congr 2
      change
        graphRestrict (conjugatePoly g) (fun j => (a j : ℂ)) =
          conjugatePoly (graphRestrict g (fun j => (a j : ℂ)))
      exact (conjugatePoly_graphRestrict_realParams g a).symm

/-- **Closure of the real non-geometric branch from the two exact
certificates.**

No further Galois, UFD, or descent theorem is needed after this point.
-/
theorem exists_real_irreducible_graphRestrict_of_conjugate_pair_certificates
    {m : ℕ}
    {f : Poly ℝ (m + 1)}
    {g u : Poly ℂ (m + 1)}
    (hg : Irreducible g)
    (hna : ¬ Associated g (conjugatePoly g))
    (hu : IsUnit u)
    (hpair :
      complexify f =
        (g * conjugatePoly g) * u)
    (hgcert :
      HasGraphIrreducibilityCertificate ℂ g)
    (hpcert :
      HasRestrictedPencilIrreducibilityCertificate g) :
    ∃ a : Fin m → ℝ,
      Irreducible (graphRestrict f a) := by
  obtain ⟨a, hgA, hPA⟩ :=
    exists_same_real_parameter_of_graph_and_pencil_certificates
      hgcert hpcert

  have hnaA :
      ¬ Associated
        (graphRestrict g
          (complexGraphParamOfReal a))
        (conjugatePoly
          (graphRestrict g
            (complexGraphParamOfReal a))) :=
    graphRestrict_not_associated_conjugate_of_pencil
      hgA hPA

  have huA :
      IsUnit
        (graphRestrict u
          (complexGraphParamOfReal a)) :=
    isUnit_graphRestrict hu
      (complexGraphParamOfReal a)

  have hpairA :=
    specialized_conjugate_pair_factorization
      hpair a

  refine ⟨a, ?_⟩
  exact
    irreducible_real_of_complexify_conjugate_pair
      hgA hnaA huA hpairA

/-!
Stage-16 audit
--------------

The real non-geometric branch is now completely algebraic once two explicit
principal-open inputs are supplied:

* an ordinary irreducibility certificate for `g`;
* a certificate for the constrained auxiliary-pencil family `(0,a)`.

The proof then:
1. intersects the two principal opens at a real point;
2. gets irreducibility of the specialized factor;
3. gets nonassociation from the auxiliary pencil;
4. specializes the conjugate-pair factorization;
5. descends to an irreducible real section.

Crucially, this stage corrects the earlier overstatement that an arbitrary
full-parameter pencil certificate would suffice.  It does not.

Therefore the unresolved geometric core has two precise pieces:
A. ordinary complex graph-section certificates;
B. the same theorem for the constrained pencil linear system.

Neither is assumed here.

No `axiom`, `sorry`, `admit`, or theorem-interface placeholder is added.
-/



/-! ## Stage 17: close all finite-dimensional iteration and exact-value plumbing

This section contains no new geometric input.

The purpose is to make the final theorem genuinely formal once the one-step
graph statement is available:
* compose successive linear restrictions;
* iterate a one-step graph section from `3+r` variables down to exactly `3`;
* package the exact least positive detection dimensions;
* connect the already-proved lower bounds to the upper bound.

Thus no finite-dimensional induction is left implicit in the final
formalization.
-/

/-- Two successive linear restrictions compose by matrix multiplication. -/
lemma restrictLinear_comp
    {K : Type*} [CommSemiring K]
    {n k l : ℕ}
    (f : Poly K n)
    (A : Frame K n k)
    (B : Frame K k l) :
    restrictLinear (restrictLinear f A) B =
      restrictLinear f (A * B) := by
  change
    (MvPolynomial.bind₁ B.toMvPolynomial)
        ((MvPolynomial.bind₁ A.toMvPolynomial) f) =
      (MvPolynomial.bind₁ (A * B).toMvPolynomial) f
  rw [MvPolynomial.bind₁_bind₁]
  have hfun :
      (fun i : Fin n =>
        (MvPolynomial.bind₁ B.toMvPolynomial)
          (A.toMvPolynomial i)) =
        (A * B).toMvPolynomial := by
    funext i
    exact (Matrix.toMvPolynomial_mul A B i).symm
  rw [hfun]

/-- Restriction along the identity frame is the identity. -/
lemma restrictLinear_id
    {K : Type*} [CommSemiring K]
    (n : ℕ) (f : Poly K n) :
    restrictLinear f (1 : Frame K n n) = f := by
  change
    (MvPolynomial.bind₁
      ((1 : Frame K n n).toMvPolynomial)) f = f
  rw [Matrix.toMvPolynomial_one]
  rw [MvPolynomial.bind₁_X_left]
  rfl

/-- Every irreducible polynomial is detected on its full ambient space. -/
lemma detectableIn_self
    {K : Type*} [CommSemiring K]
    {n : ℕ}
    (f : Poly K n)
    (hf : Irreducible f) :
    DetectableIn n f := by
  refine ⟨1, ?_⟩
  simpa [restrictLinear_id] using hf

/-- Tautological full-dimensional universal detection. -/
lemma universalDetects_self
    {K : Type*} [CommSemiring K]
    (n : ℕ) :
    UniversalDetects K n n := by
  intro f hf
  exact detectableIn_self f hf

/-- A proved graph-Bertini statement gives the corresponding one-step
arbitrary-matrix restriction. -/
lemma oneStep_of_graphBertini
    {K : Type*} [Field K]
    (hGB : GraphBertiniStatement K)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly K (m + 1))
    (hf : Irreducible f) :
    ∃ A : Frame K (m + 1) m,
      Irreducible (restrictLinear f A) := by
  obtain ⟨a, ha⟩ := hGB hm f hf
  exact ⟨graphFrame a, ha⟩

/-- Repeated one-step graph sections reduce `3+r` variables to exactly three
parameters.  This induction uses no additional geometry. -/
theorem detectableIn_three_add_of_graphBertini
    {K : Type*} [Field K]
    (hGB : GraphBertiniStatement K) :
    ∀ r : ℕ, ∀ f : Poly K (3 + r),
      Irreducible f → DetectableIn 3 f := by
  intro r
  induction r with
  | zero =>
      intro f hf
      simpa using detectableIn_self f hf
  | succ r ih =>
      intro f hf
      have hm : 3 ≤ 3 + r := by omega
      obtain ⟨A, hA⟩ :=
        oneStep_of_graphBertini
          hGB hm f hf
      obtain ⟨B, hB⟩ :=
        ih (restrictLinear f A) hA
      refine ⟨A * B, ?_⟩
      rw [← restrictLinear_comp]
      exact hB

/-- Any proved graph-Bertini statement yields the universal upper bound `3`
in every ambient dimension at least three. -/
theorem universalDetects_three_of_graphBertini
    {K : Type*} [Field K]
    (hGB : GraphBertiniStatement K)
    {n : ℕ} (hn : 3 ≤ n) :
    UniversalDetects K n 3 := by
  intro f hf
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_add_of_le hn
  exact
    detectableIn_three_add_of_graphBertini
      hGB r f hf

/-- `k` is the least positive universal detection dimension. -/
def LeastUniversalDetection
    (K : Type*) [CommSemiring K]
    (n k : ℕ) : Prop :=
  1 ≤ k ∧
  UniversalDetects K n k ∧
  ∀ j, 1 ≤ j →
    UniversalDetects K n j →
    k ≤ j

/-- Exact one-variable value, completely unconditional. -/
theorem leastUniversalDetection_one
    {K : Type*} [CommSemiring K] :
    LeastUniversalDetection K 1 1 := by
  refine ⟨by omega, universalDetects_self 1, ?_⟩
  intro j hj _
  omega

/-- Exact two-variable value over `ℝ`, using the already formalized plane
witness lower bound. -/
theorem leastUniversalDetection_two_real :
    LeastUniversalDetection ℝ 2 2 := by
  refine ⟨by omega, universalDetects_self 2, ?_⟩
  intro j hj hU
  by_contra hlt
  have hj1 : j = 1 := by omega
  subst j
  exact not_universalDetects_one_twoVars_real hU

/-- Exact two-variable value over `ℂ`. -/
theorem leastUniversalDetection_two_complex :
    LeastUniversalDetection ℂ 2 2 := by
  refine ⟨by omega, universalDetects_self 2, ?_⟩
  intro j hj hU
  by_contra hlt
  have hj1 : j = 1 := by omega
  subst j
  exact not_universalDetects_one_twoVars_complex hU

/-- Conditional exact high-dimensional real value: the only input is the
explicit one-step graph-Bertini proposition. -/
theorem leastUniversalDetection_high_real_of_graphBertini
    (hGB : GraphBertiniStatement ℝ)
    {n : ℕ} (hn : 3 ≤ n) :
    LeastUniversalDetection ℝ n 3 := by
  refine
    ⟨by omega,
      universalDetects_three_of_graphBertini hGB hn,
      ?_⟩
  intro j hj hU
  by_contra hlt
  have hjcases : j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl
  · exact not_universalDetects_one_high_real hn hU
  · exact not_universalDetects_two_real hn hU

/-- Conditional exact high-dimensional complex value. -/
theorem leastUniversalDetection_high_complex_of_graphBertini
    (hGB : GraphBertiniStatement ℂ)
    {n : ℕ} (hn : 3 ≤ n) :
    LeastUniversalDetection ℂ n 3 := by
  refine
    ⟨by omega,
      universalDetects_three_of_graphBertini hGB hn,
      ?_⟩
  intro j hj hU
  by_contra hlt
  have hjcases : j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl
  · exact not_universalDetects_one_high_complex hn hU
  · exact not_universalDetects_two_complex hn hU

/-!
Stage-17 audit
--------------

All non-geometric finite-dimensional plumbing is now explicit:

* restrictions compose;
* the identity restriction is formalized;
* one graph-Bertini step iterates to dimension three;
* `k₁ = 1` is unconditional;
* `k₂ = 2` over `ℝ` and `ℂ` is unconditional;
* for `n ≥ 3`, the already-formalized lower bounds combine with a proved
  `GraphBertiniStatement` to give the exact value `3`.

No axiom or placeholder is used.  The theorem arguments named `hGB` are
ordinary hypotheses in implication theorems; they are not instances, axioms,
or claims that Bertini has been proved.

The remaining task for a completely closed Problem 20.1 formalization is
therefore genuinely geometric/algebraic: prove `GraphBertiniStatement ℂ`,
and prove the real one-step statement using the strict descent machinery above.
-/



/-! ## Stage 18: an explicit polynomial certificate for nonassociation

Stage 16 used a second, constrained Bertini certificate for the auxiliary
conjugate pencil.  That is stronger than necessary.

Here we replace it by an explicit coefficient/evaluation determinant.

Fix two spatial points `x,y`.  For a graph parameter `a`, define
\[
  D_{g,x,y}(a)
   = g_a(x)\,\bar g_a(y)-g_a(y)\,\bar g_a(x).
\]
This is an honest polynomial in the graph parameters.  If it is nonzero at
`a`, then `g_a` cannot be associated to its conjugate.

Consequently, once we exhibit just one real parameter `a₀` with
`D(a₀) ≠ 0`, the polynomial `D` itself is a principal-open certificate for
nonassociation.  It can then be intersected with the ordinary Bertini
irreducibility certificate.

This removes the need for a second Bertini theorem, provided Stage 19 can
construct such an `a₀` from global nonassociation.
-/

/-- Substitute a *fixed spatial point* into a graph section, leaving the graph
coefficients as polynomial variables.

Thus `graphEvalParam f x` is a polynomial in `A₀,...,A_{m-1}` whose value at
`a` is `graphRestrict f a` evaluated at `x`. -/
def graphEvalParamSubst
    {m : ℕ} (x : Fin m → ℂ) :
    Fin (m + 1) → Poly ℂ m :=
  fun i =>
    Fin.lastCases
      (∑ j : Fin m,
        MvPolynomial.X j *
          MvPolynomial.C (x j))
      (fun r : Fin m =>
        MvPolynomial.C (x r)) i

def graphEvalParam
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (x : Fin m → ℂ) :
    Poly ℂ m :=
  MvPolynomial.bind₁
    (graphEvalParamSubst x) f

/-- Exact semantics of `graphEvalParam`. -/
lemma eval_graphEvalParam
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (x : Fin m → ℂ)
    (a : Fin m → ℂ) :
    MvPolynomial.eval a
        (graphEvalParam f x) =
      MvPolynomial.eval x
        (graphRestrict f a) := by
  rw [eval_graphRestrict]
  unfold graphEvalParam
  calc
    MvPolynomial.eval a
        (MvPolynomial.bind₁ (graphEvalParamSubst x) f) =
      MvPolynomial.eval
        (fun i => MvPolynomial.eval a (graphEvalParamSubst x i)) f := by
          simpa using
            (MvPolynomial.eval₂Hom_bind₁
              (RingHom.id ℂ) a (graphEvalParamSubst x) f)
    _ = MvPolynomial.eval (graphPoint a x) f := by
      apply congrArg (fun h : Fin (m + 1) → ℂ =>
        MvPolynomial.eval h f)
      funext i
      refine Fin.lastCases ?_ (fun r => ?_) i
      · simp [graphEvalParamSubst, graphPoint]
      · simp [graphEvalParamSubst, graphPoint]

/-- The explicit determinant polynomial detecting failure of proportionality
between a graph section and the graph section of its conjugate. -/
def graphNonAssocWitness
    {m : ℕ}
    (g : Poly ℂ (m + 1))
    (x y : Fin m → ℂ) :
    Poly ℂ m :=
  graphEvalParam g x *
      graphEvalParam (conjugatePoly g) y -
    graphEvalParam g y *
      graphEvalParam (conjugatePoly g) x

/-- Evaluation formula for the determinant witness. -/
lemma eval_graphNonAssocWitness
    {m : ℕ}
    (g : Poly ℂ (m + 1))
    (x y : Fin m → ℂ)
    (a : Fin m → ℂ) :
    MvPolynomial.eval a
        (graphNonAssocWitness g x y) =
      MvPolynomial.eval x
          (graphRestrict g a) *
        MvPolynomial.eval y
          (graphRestrict (conjugatePoly g) a) -
      MvPolynomial.eval y
          (graphRestrict g a) *
        MvPolynomial.eval x
          (graphRestrict (conjugatePoly g) a) := by
  simp [graphNonAssocWitness,
    eval_graphEvalParam]

/-- Associated multivariate polynomials over `ℂ` have zero two-point
proportionality determinant. -/
lemma eval_det_eq_zero_of_associated
    {n : ℕ}
    {p q : Poly ℂ n}
    (hassoc : Associated p q)
    (x y : Fin n → ℂ) :
    MvPolynomial.eval x p *
        MvPolynomial.eval y q -
      MvPolynomial.eval y p *
        MvPolynomial.eval x q = 0 := by
  rcases hassoc with ⟨u, hu⟩
  obtain ⟨c, hcU, huc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := (u : Poly ℂ n))).mp u.isUnit
  rw [huc] at hu
  have hx :=
    congrArg (MvPolynomial.eval x) hu
  have hy :=
    congrArg (MvPolynomial.eval y) hu
  simp at hx hy
  rw [← hx, ← hy]
  ring

/-- At a **real** graph parameter, nonvanishing of the explicit witness forces
the specialized factor to be nonassociated to its coefficientwise conjugate.
-/
theorem graphRestrict_not_associated_of_witness
    {m : ℕ}
    (g : Poly ℂ (m + 1))
    (x y : Fin m → ℂ)
    (a : Fin m → ℝ)
    (hD :
      MvPolynomial.eval
        (complexGraphParamOfReal a)
        (graphNonAssocWitness g x y) ≠ 0) :
    ¬ Associated
      (graphRestrict g
        (complexGraphParamOfReal a))
      (conjugatePoly
        (graphRestrict g
          (complexGraphParamOfReal a))) := by
  intro hassoc
  have hassoc' :
      Associated
        (graphRestrict g
          (complexGraphParamOfReal a))
        (graphRestrict (conjugatePoly g)
          (complexGraphParamOfReal a)) := by
    change
      Associated
        (graphRestrict g (fun j => (a j : ℂ)))
        (graphRestrict (conjugatePoly g) (fun j => (a j : ℂ)))
    rw [← conjugatePoly_graphRestrict_realParams g a]
    change
      Associated
        (graphRestrict g (fun j => (a j : ℂ)))
        (conjugatePoly (graphRestrict g (fun j => (a j : ℂ)))) at hassoc
    exact hassoc
  apply hD
  rw [eval_graphNonAssocWitness]
  exact
    eval_det_eq_zero_of_associated
      hassoc' x y

/-- If the witness is nonzero at one parameter, then it is a nonzero parameter
polynomial. -/
lemma graphNonAssocWitness_ne_zero_of_eval
    {m : ℕ}
    {g : Poly ℂ (m + 1)}
    {x y : Fin m → ℂ}
    {a : Fin m → ℂ}
    (hD :
      MvPolynomial.eval a
        (graphNonAssocWitness g x y) ≠ 0) :
    graphNonAssocWitness g x y ≠ 0 := by
  intro hzero
  apply hD
  rw [hzero]
  simp

/-- An ordinary Bertini certificate plus one nonzero nonassociation witness
polynomial yields a single real parameter where the graph section is both
irreducible and nonassociated to its conjugate. -/
theorem exists_real_parameter_irreducible_and_not_associated
    {m : ℕ}
    {g : Poly ℂ (m + 1)}
    (hgcert :
      HasGraphIrreducibilityCertificate ℂ g)
    (x y : Fin m → ℂ)
    (hD0 :
      graphNonAssocWitness g x y ≠ 0) :
    ∃ a : Fin m → ℝ,
      Irreducible
        (graphRestrict g
          (complexGraphParamOfReal a)) ∧
      ¬ Associated
        (graphRestrict g
          (complexGraphParamOfReal a))
        (conjugatePoly
          (graphRestrict g
            (complexGraphParamOfReal a))) := by
  rcases hgcert with
    ⟨Δ, hΔ0, hΔgood⟩
  obtain ⟨a, hΔa, hDa⟩ :=
    exists_real_point_two_eval_ne_zero
      Δ (graphNonAssocWitness g x y)
      hΔ0 hD0
  refine
    ⟨a,
      hΔgood
        (complexGraphParamOfReal a) hΔa,
      ?_⟩
  exact
    graphRestrict_not_associated_of_witness
      g x y a hDa

/-- The real non-geometric branch closes from an ordinary graph certificate as
soon as one explicit nonzero witness polynomial has been produced. -/
theorem exists_real_irreducible_graphRestrict_of_conjugate_pair_and_witness
    {m : ℕ}
    {f : Poly ℝ (m + 1)}
    {g u : Poly ℂ (m + 1)}
    (hg : Irreducible g)
    (hu : IsUnit u)
    (hpair :
      complexify f =
        (g * conjugatePoly g) * u)
    (hgcert :
      HasGraphIrreducibilityCertificate ℂ g)
    (x y : Fin m → ℂ)
    (hD0 :
      graphNonAssocWitness g x y ≠ 0) :
    ∃ a : Fin m → ℝ,
      Irreducible (graphRestrict f a) := by
  obtain ⟨a, hgA, hnaA⟩ :=
    exists_real_parameter_irreducible_and_not_associated
      hgcert x y hD0
  have huA :
      IsUnit
        (graphRestrict u
          (complexGraphParamOfReal a)) :=
    isUnit_graphRestrict hu
      (complexGraphParamOfReal a)
  have hpairA :=
    specialized_conjugate_pair_factorization
      hpair a
  refine ⟨a, ?_⟩
  exact
    irreducible_real_of_complexify_conjugate_pair
      hgA hnaA huA hpairA

/-!
Stage-18 audit
--------------

The auxiliary-pencil Bertini condition from Stage 16 is no longer logically
necessary.

To close the real non-geometric branch it now suffices to prove the following
purely algebraic existence statement:

    if `¬ Associated g (conjugatePoly g)`,
    then there exist fixed spatial points `x,y`
    such that `graphNonAssocWitness g x y ≠ 0`.

Once that is done, **one ordinary complex Bertini certificate for `g` is
enough**.  The nonassociation condition is handled by the explicit additional
principal-open polynomial `graphNonAssocWitness`.

Stage 19 will construct the required witness from two real ambient points and
an explicit graph hyperplane through them.

No second Bertini theorem, no openness theorem for association, and no new
axiom is introduced.
-/



/-! ## Stage 19: construct a nonassociation witness hyperplane explicitly

We now prove the purely algebraic existence statement left by Stage 18.

Let `g` be a nonzero complex polynomial not associated to its conjugate.

1. Choose a real point `u` where both `g(u) ≠ 0` and the first coordinate
   `u₀ ≠ 0`.  This is done by applying the Stage-9 real-point theorem to
   `g * X₀`.
2. The polynomial
      `g(u) * conjugate(g) - conjugate(g)(u) * g`
   is nonzero; otherwise `g` would be a constant-unit multiple of its
   conjugate.
3. Choose a second real point `v` where this phase-difference polynomial is
   nonzero and where
      `u₀ v₁ - u₁ v₀ ≠ 0`.
4. Solve the two equations saying that a graph hyperplane contains `u` and
   `v` using the first two graph coefficients (Cramer's rule).
5. At that graph parameter the Stage-18 determinant witness is nonzero.

Hence global nonassociation always yields a nonzero explicit parameter
polynomial.  No second Bertini statement is needed.
-/

/-- Complexify a real point coordinatewise. -/
def complexPoint
    {n : ℕ} (x : Fin n → ℝ) :
    Fin n → ℂ :=
  fun i => (x i : ℂ)

/-- Evaluation of coefficientwise conjugation at a real point is ordinary
complex conjugation of the value. -/
lemma eval_conjugatePoly_at_real
    {n : ℕ}
    (g : Poly ℂ n)
    (x : Fin n → ℝ) :
    MvPolynomial.eval (complexPoint x)
        (conjugatePoly g) =
      star
        (MvPolynomial.eval (complexPoint x) g) := by
  symm
  unfold conjugatePoly
  have h :=
    MvPolynomial.map_eval
      (starRingEnd ℂ)
      (complexPoint x) g
  convert h using 1 <;>
    simp [complexPoint, Function.comp_apply]

/-- The phase-difference polynomial based at a real point `u`. -/
def phaseDifferenceAt
    {n : ℕ}
    (g : Poly ℂ n)
    (u : Fin n → ℝ) :
    Poly ℂ n :=
  MvPolynomial.C
      (MvPolynomial.eval (complexPoint u) g) *
      conjugatePoly g -
    MvPolynomial.C
      (MvPolynomial.eval (complexPoint u)
        (conjugatePoly g)) *
      g

/-- If `g(u) ≠ 0` and `g` is not associated to its conjugate, the
phase-difference polynomial based at `u` is nonzero. -/
lemma phaseDifferenceAt_ne_zero
    {n : ℕ}
    {g : Poly ℂ n}
    {u : Fin n → ℝ}
    (hgu :
      MvPolynomial.eval (complexPoint u) g ≠ 0)
    (hna :
      ¬ Associated g (conjugatePoly g)) :
    phaseDifferenceAt g u ≠ 0 := by
  intro hzero

  let c : ℂ :=
    MvPolynomial.eval (complexPoint u) g
  let d : ℂ :=
    MvPolynomial.eval (complexPoint u)
      (conjugatePoly g)

  have hc : c ≠ 0 := by
    simpa [c] using hgu

  have hdstar : d = star c := by
    dsimp [c, d]
    exact eval_conjugatePoly_at_real g u

  have hd : d ≠ 0 := by
    rw [hdstar]
    exact star_ne_zero.mpr hc

  have hEq :
      MvPolynomial.C c * conjugatePoly g =
        MvPolynomial.C d * g := by
    have := sub_eq_zero.mp hzero
    simpa [phaseDifferenceAt, c, d] using this

  let z : ℂ := d / c

  have hz : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero hd hc

  have hbar :
      conjugatePoly g =
        g * MvPolynomial.C z := by
    calc
      conjugatePoly g =
          MvPolynomial.C (c⁻¹) *
            (MvPolynomial.C c *
              conjugatePoly g) := by
        rw [← mul_assoc, ← MvPolynomial.C_mul]
        simp [hc]
      _ =
          MvPolynomial.C (c⁻¹) *
            (MvPolynomial.C d * g) := by
        rw [hEq]
      _ =
          g * MvPolynomial.C z := by
        dsimp [z]
        rw [div_eq_mul_inv]
        rw [← mul_assoc, ← MvPolynomial.C_mul]
        rw [mul_comm (c⁻¹) d]
        ac_rfl

  have hCz :
      IsUnit
        (MvPolynomial.C z : Poly ℂ n) := by
    exact
      (IsUnit.mk0 z hz).map
        (MvPolynomial.C : ℂ →+* Poly ℂ n)

  apply hna
  rw [hbar]
  exact
    associated_mul_unit_right
      g (MvPolynomial.C z) hCz

/-- A fixed linear polynomial measuring whether the first two head coordinates
of a point are independent from those of `u`. -/
def transverseLinear
    {m : ℕ}
    (hm : 2 ≤ m)
    (u : Fin (m + 1) → ℝ) :
    Poly ℂ (m + 1) := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  exact
    MvPolynomial.C (u i0.castSucc : ℂ) *
        MvPolynomial.X i1.castSucc -
      MvPolynomial.C (u i1.castSucc : ℂ) *
        MvPolynomial.X i0.castSucc

/-- Evaluation formula for `transverseLinear`. -/
lemma eval_transverseLinear
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ) :
    MvPolynomial.eval (complexPoint v)
        (transverseLinear hm u) =
      (u ⟨0, by omega⟩ : ℂ) *
          (v ⟨1, by omega⟩ : ℂ) -
        (u ⟨1, by omega⟩ : ℂ) *
          (v ⟨0, by omega⟩ : ℂ) := by
  simp [transverseLinear, complexPoint]

/-- If the first coordinate of `u` is nonzero, then the transverse linear
polynomial is nonzero. -/
lemma transverseLinear_ne_zero
    {m : ℕ}
    (hm : 2 ≤ m)
    (u : Fin (m + 1) → ℝ)
    (hu0 :
      u ⟨0, by omega⟩ ≠ 0) :
    transverseLinear hm u ≠ 0 := by
  let v : Fin (m + 1) → ℝ :=
    fun i => if i.val = 1 then 1 else 0
  intro hzero
  have hEval :
      MvPolynomial.eval (complexPoint v)
          (transverseLinear hm u) = 0 := by
    rw [hzero]
    simp
  rw [eval_transverseLinear hm u v] at hEval
  have huz : (u ⟨0, by omega⟩ : ℂ) = 0 := by
    simpa [v] using hEval
  have huc : (u ⟨0, by omega⟩ : ℂ) ≠ 0 := by
    exact_mod_cast hu0
  exact huc huz

/-- The head of an ambient real point. -/
def realHead
    {m : ℕ}
    (u : Fin (m + 1) → ℝ) :
    Fin m → ℝ :=
  fun j => u j.castSucc

/-- The complexified head. -/
def complexHead
    {m : ℕ}
    (u : Fin (m + 1) → ℝ) :
    Fin m → ℂ :=
  complexPoint (realHead u)

/-- Cramer's-rule graph parameter through two ambient real points whose first
two head coordinates have nonzero determinant. -/
def twoPointGraphParam
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ) :
    Fin m → ℝ := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let det : ℝ :=
    u i0.castSucc * v i1.castSucc -
      u i1.castSucc * v i0.castSucc
  let a0 : ℝ :=
    (u (Fin.last m) * v i1.castSucc -
      v (Fin.last m) * u i1.castSucc) / det
  let a1 : ℝ :=
    (v (Fin.last m) * u i0.castSucc -
      u (Fin.last m) * v i0.castSucc) / det
  exact fun j =>
    if j = i0 then a0
    else if j = i1 then a1
    else 0

/-- The Cramer parameter sends the head of `u` to its last coordinate. -/
lemma twoPointGraphParam_dot_u
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ)
    (hdet :
      u ⟨0, by omega⟩ * v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ * v ⟨0, by omega⟩ ≠ 0) :
    ∑ j : Fin m,
        twoPointGraphParam hm u v j *
          realHead u j =
      u (Fin.last m) := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    simp [i0, i1]
  let det : ℝ :=
    u i0.castSucc * v i1.castSucc -
      u i1.castSucc * v i0.castSucc
  have hdet' : det ≠ 0 := by
    simpa [det, i0, i1] using hdet
  let a0 : ℝ :=
    (u (Fin.last m) * v i1.castSucc -
      v (Fin.last m) * u i1.castSucc) / det
  let a1 : ℝ :=
    (v (Fin.last m) * u i0.castSucc -
      u (Fin.last m) * v i0.castSucc) / det
  have hsum :
      (∑ j : Fin m,
        twoPointGraphParam hm u v j *
          realHead u j) =
        a0 * u i0.castSucc +
          a1 * u i1.castSucc := by
    apply Fintype.sum_eq_add i0 i1 hi
    intro j hj
    simp [twoPointGraphParam, realHead, hj.1, hj.2,
      i0, i1, a0, a1, det]
  rw [hsum]
  dsimp [a0, a1]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (div_eq_iff hdet').2
  dsimp [det]
  ring

/-- The same Cramer parameter sends the head of `v` to its last coordinate. -/
lemma twoPointGraphParam_dot_v
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ)
    (hdet :
      u ⟨0, by omega⟩ * v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ * v ⟨0, by omega⟩ ≠ 0) :
    ∑ j : Fin m,
        twoPointGraphParam hm u v j *
          realHead v j =
      v (Fin.last m) := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    simp [i0, i1]
  let det : ℝ :=
    u i0.castSucc * v i1.castSucc -
      u i1.castSucc * v i0.castSucc
  have hdet' : det ≠ 0 := by
    simpa [det, i0, i1] using hdet
  let a0 : ℝ :=
    (u (Fin.last m) * v i1.castSucc -
      v (Fin.last m) * u i1.castSucc) / det
  let a1 : ℝ :=
    (v (Fin.last m) * u i0.castSucc -
      u (Fin.last m) * v i0.castSucc) / det
  have hsum :
      (∑ j : Fin m,
        twoPointGraphParam hm u v j *
          realHead v j) =
        a0 * v i0.castSucc +
          a1 * v i1.castSucc := by
    apply Fintype.sum_eq_add i0 i1 hi
    intro j hj
    simp [twoPointGraphParam, realHead, hj.1, hj.2,
      i0, i1, a0, a1, det]
  rw [hsum]
  dsimp [a0, a1]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (div_eq_iff hdet').2
  dsimp [det]
  ring

/-- The graph point with the Cramer parameter recovers `u`. -/
lemma graphPoint_twoPointGraphParam_u
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ)
    (hdet :
      u ⟨0, by omega⟩ * v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ * v ⟨0, by omega⟩ ≠ 0) :
    graphPoint
        (complexGraphParamOfReal
          (twoPointGraphParam hm u v))
        (complexHead u) =
      complexPoint u := by
  funext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simp only [graphPoint_last, complexGraphParamOfReal,
      complexHead, complexPoint, realHead]
    exact_mod_cast twoPointGraphParam_dot_u hm u v hdet
  · simp only [graphPoint_castSucc, complexHead,
      complexPoint, realHead]

/-- The same graph point recovers `v`. -/
lemma graphPoint_twoPointGraphParam_v
    {m : ℕ}
    (hm : 2 ≤ m)
    (u v : Fin (m + 1) → ℝ)
    (hdet :
      u ⟨0, by omega⟩ * v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ * v ⟨0, by omega⟩ ≠ 0) :
    graphPoint
        (complexGraphParamOfReal
          (twoPointGraphParam hm u v))
        (complexHead v) =
      complexPoint v := by
  funext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · simp only [graphPoint_last, complexGraphParamOfReal,
      complexHead, complexPoint, realHead]
    exact_mod_cast twoPointGraphParam_dot_v hm u v hdet
  · simp only [graphPoint_castSucc, complexHead,
      complexPoint, realHead]

/-- **Global nonassociation produces a nonzero Stage-18 witness polynomial.**

This is the key result eliminating the second Bertini core.
-/
theorem exists_graphNonAssocWitness_of_not_associated
    {m : ℕ}
    (hm : 2 ≤ m)
    {g : Poly ℂ (m + 1)}
    (hg0 : g ≠ 0)
    (hna :
      ¬ Associated g (conjugatePoly g)) :
    ∃ x y : Fin m → ℂ,
      graphNonAssocWitness g x y ≠ 0 := by
  let i0 : Fin (m + 1) := ⟨0, by omega⟩

  have hprod0 :
      g * MvPolynomial.X i0 ≠ 0 := by
    exact mul_ne_zero hg0 (by simp)

  obtain ⟨u, huProd⟩ :=
    exists_real_point_eval_ne_zero
      (g * MvPolynomial.X i0) hprod0
  have huProd' :
      MvPolynomial.eval (complexPoint u)
          (g * MvPolynomial.X i0) ≠ 0 := by
    change
      MvPolynomial.eval (fun i => (u i : ℂ))
          (g * MvPolynomial.X i0) ≠ 0
    exact huProd

  have hgu :
      MvPolynomial.eval (complexPoint u) g ≠ 0 := by
    intro hzero
    apply huProd'
    rw [MvPolynomial.eval_mul, hzero, zero_mul]

  have hu0 :
      u i0 ≠ 0 := by
    intro hzero
    apply huProd'
    rw [MvPolynomial.eval_mul]
    have hXi :
        MvPolynomial.eval (complexPoint u) (MvPolynomial.X i0) = 0 := by
      simp [complexPoint, hzero]
    rw [hXi, mul_zero]

  have hphase0 :
      phaseDifferenceAt g u ≠ 0 :=
    phaseDifferenceAt_ne_zero hgu hna

  have htrans0 :
      transverseLinear hm u ≠ 0 :=
    transverseLinear_ne_zero hm u
      (by simpa [i0] using hu0)

  have hproduct0 :
      phaseDifferenceAt g u *
          transverseLinear hm u ≠ 0 :=
    mul_ne_zero hphase0 htrans0

  obtain ⟨v, hvProd⟩ :=
    exists_real_point_eval_ne_zero
      (phaseDifferenceAt g u *
        transverseLinear hm u)
      hproduct0
  have hvProd' :
      MvPolynomial.eval (complexPoint v)
        (phaseDifferenceAt g u * transverseLinear hm u) ≠ 0 := by
    change
      MvPolynomial.eval (fun i => (v i : ℂ))
        (phaseDifferenceAt g u * transverseLinear hm u) ≠ 0
    exact hvProd

  have hvPhase :
      MvPolynomial.eval (complexPoint v)
        (phaseDifferenceAt g u) ≠ 0 := by
    intro hzero
    apply hvProd'
    rw [MvPolynomial.eval_mul, hzero, zero_mul]

  have hvTrans :
      MvPolynomial.eval (complexPoint v)
        (transverseLinear hm u) ≠ 0 := by
    intro hzero
    apply hvProd'
    rw [MvPolynomial.eval_mul, hzero, mul_zero]

  have hdetC :
      ((u ⟨0, by omega⟩ *
          v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ *
          v ⟨0, by omega⟩ : ℝ) : ℂ) ≠ 0 := by
    simpa [eval_transverseLinear,
      complexPoint] using hvTrans

  have hdet :
      u ⟨0, by omega⟩ *
          v ⟨1, by omega⟩ -
        u ⟨1, by omega⟩ *
          v ⟨0, by omega⟩ ≠ 0 := by
    exact_mod_cast hdetC

  let a : Fin m → ℝ :=
    twoPointGraphParam hm u v

  have hguGraph :
      MvPolynomial.eval (complexHead u)
          (graphRestrict g
            (complexGraphParamOfReal a)) =
        MvPolynomial.eval (complexPoint u) g := by
    rw [eval_graphRestrict]
    rw [graphPoint_twoPointGraphParam_u
      hm u v hdet]

  have hgvGraph :
      MvPolynomial.eval (complexHead v)
          (graphRestrict g
            (complexGraphParamOfReal a)) =
        MvPolynomial.eval (complexPoint v) g := by
    rw [eval_graphRestrict]
    rw [graphPoint_twoPointGraphParam_v
      hm u v hdet]

  have hcuGraph :
      MvPolynomial.eval (complexHead u)
          (graphRestrict (conjugatePoly g)
            (complexGraphParamOfReal a)) =
        MvPolynomial.eval (complexPoint u)
          (conjugatePoly g) := by
    rw [eval_graphRestrict]
    rw [graphPoint_twoPointGraphParam_u
      hm u v hdet]

  have hcvGraph :
      MvPolynomial.eval (complexHead v)
          (graphRestrict (conjugatePoly g)
            (complexGraphParamOfReal a)) =
        MvPolynomial.eval (complexPoint v)
          (conjugatePoly g) := by
    rw [eval_graphRestrict]
    rw [graphPoint_twoPointGraphParam_v
      hm u v hdet]

  have hDAt :
      MvPolynomial.eval
          (complexGraphParamOfReal a)
          (graphNonAssocWitness g
            (complexHead u) (complexHead v)) ≠ 0 := by
    rw [eval_graphNonAssocWitness]
    rw [hguGraph, hgvGraph,
      hcuGraph, hcvGraph]
    simpa [phaseDifferenceAt, mul_comm] using hvPhase

  refine
    ⟨complexHead u, complexHead v, ?_⟩
  exact
    graphNonAssocWitness_ne_zero_of_eval
      hDAt

/-- The real non-geometric branch now needs only the **ordinary** complex
graph irreducibility certificate.  The second constrained-pencil certificate
from Stage 16 has been eliminated. -/
theorem exists_real_irreducible_graphRestrict_of_conjugate_pair_certificate
    {m : ℕ}
    (hm : 2 ≤ m)
    {f : Poly ℝ (m + 1)}
    {g u : Poly ℂ (m + 1)}
    (hg : Irreducible g)
    (hna :
      ¬ Associated g (conjugatePoly g))
    (hu : IsUnit u)
    (hpair :
      complexify f =
        (g * conjugatePoly g) * u)
    (hgcert :
      HasGraphIrreducibilityCertificate ℂ g) :
    ∃ a : Fin m → ℝ,
      Irreducible (graphRestrict f a) := by
  obtain ⟨x, y, hD0⟩ :=
    exists_graphNonAssocWitness_of_not_associated
      hm hg.ne_zero hna
  exact
    exists_real_irreducible_graphRestrict_of_conjugate_pair_and_witness
      hg hu hpair hgcert x y hD0

/-!
Stage-19 audit
--------------

The earlier Stage-16 correction has now been superseded constructively:

* no constrained-pencil Bertini certificate is needed;
* global nonassociation `g ≁ conjugate(g)` produces an explicit nonzero
  parameter polynomial `graphNonAssocWitness`;
* that polynomial can be intersected with the ordinary irreducibility
  certificate at a real point;
* Stage 13 then descends the specialized conjugate pair to an irreducible real
  section.

Therefore the entire real non-geometric branch reduces to the **same ordinary
complex graph-section certificate** used in the geometrically irreducible
branch.

At the level of mathematical dependencies, the only remaining genuine
Bertini core is now the ordinary complex certificate theorem
`ComplexBertiniCore`.

No second Bertini theorem survives.
-/



/-! ## Stage 20: reduce the entire exact theorem to one complex certificate core

Stage 19 removed the second Bertini input from the real non-geometric branch.
We can now combine all cases.

This section proves:

    ComplexBertiniCore
      → GraphBertiniStatement ℂ
      → exact complex values,

and independently

    ComplexBertiniCore
      → GraphBertiniStatement ℝ
      → exact real values.

The real proof splits according to whether `complexify f` is irreducible.
* Geometrically irreducible branch: Stage 9.
* Reducible complexification branch: Stages 10--13 + 18--19.

No further unproved interface is introduced.
-/

/-- The complex certificate core immediately gives the complex one-step graph
statement. -/
theorem complex_graphBertini_of_core
    (hcore : ComplexBertiniCore) :
    GraphBertiniStatement ℂ := by
  intro m hm f hf
  have hcert :
      HasGraphIrreducibilityCertificate ℂ f :=
    hcore hm f hf
  exact
    exists_irreducible_graphRestrict_of_certificate
      hcert

/-- The same single complex core also gives the real one-step graph statement.

This is the full strict real descent, including the non-geometrically-
irreducible branch. -/
theorem real_graphBertini_of_core
    (hcore : ComplexBertiniCore) :
    GraphBertiniStatement ℝ := by
  intro m hm f hf
  by_cases hgeom :
      Irreducible (complexify f)
  · have hcert :
        HasGraphIrreducibilityCertificate ℂ
          (complexify f) :=
      hcore hm (complexify f) hgeom
    exact
      exists_real_irreducible_graphRestrict_of_complex_certificate
        hcert
  · obtain
      ⟨g, u, hg, hna, hu, hpair⟩ :=
      exists_conjugate_pair_factorization_of_complexify
        hf hgeom
    have hgcert :
        HasGraphIrreducibilityCertificate ℂ g :=
      hcore hm g hg
    have hm2 : 2 ≤ m := by omega
    exact
      exists_real_irreducible_graphRestrict_of_conjugate_pair_certificate
        hm2 hg hna hu hpair hgcert

/-- Hence the single complex core gives the exact high-dimensional values over
`ℂ`. -/
theorem leastUniversalDetection_high_complex_of_core
    (hcore : ComplexBertiniCore)
    {n : ℕ} (hn : 3 ≤ n) :
    LeastUniversalDetection ℂ n 3 := by
  exact
    leastUniversalDetection_high_complex_of_graphBertini
      (complex_graphBertini_of_core hcore) hn

/-- And the same core gives the exact high-dimensional values over `ℝ`. -/
theorem leastUniversalDetection_high_real_of_core
    (hcore : ComplexBertiniCore)
    {n : ℕ} (hn : 3 ≤ n) :
    LeastUniversalDetection ℝ n 3 := by
  exact
    leastUniversalDetection_high_real_of_graphBertini
      (real_graphBertini_of_core hcore) hn

/-- Complete exact sequence over the complexes, expressed as one conjunction
whose only hypothesis is the single complex certificate core. -/
theorem exact_sequence_complex_of_core
    (hcore : ComplexBertiniCore) :
    LeastUniversalDetection ℂ 1 1 ∧
    LeastUniversalDetection ℂ 2 2 ∧
    ∀ n, 3 ≤ n →
      LeastUniversalDetection ℂ n 3 := by
  exact
    ⟨leastUniversalDetection_one,
      leastUniversalDetection_two_complex,
      fun n hn =>
        leastUniversalDetection_high_complex_of_core
          hcore hn⟩

/-- Complete exact sequence over the reals, again from the same single core. -/
theorem exact_sequence_real_of_core
    (hcore : ComplexBertiniCore) :
    LeastUniversalDetection ℝ 1 1 ∧
    LeastUniversalDetection ℝ 2 2 ∧
    ∀ n, 3 ≤ n →
      LeastUniversalDetection ℝ n 3 := by
  exact
    ⟨leastUniversalDetection_one,
      leastUniversalDetection_two_real,
      fun n hn =>
        leastUniversalDetection_high_real_of_core
          hcore hn⟩

/-!
Stage-20 audit
--------------

All lower bounds, real descent, conjugate-factor algebra, same-parameter
selection, and finite-dimensional iteration are now internal.

The exact theorem over both `ℝ` and `ℂ` has exactly one remaining mathematical
dependency:

    ComplexBertiniCore

namely

    for `m ≥ 3`, every irreducible
    `f : ℂ[x₀,...,x_m]`
    admits a nonzero polynomial `Δ` in the graph-hyperplane parameters such
    that every parameter with `Δ ≠ 0` gives an irreducible graph section.

Nothing else is hidden behind an axiom, instance, theorem class, or second
genericity statement.

The rest of the formalization must now prove this core itself.
-/



/-! ## Stage 21: finite Nullstellensatz certificates

The remaining complex Bertini core will be attacked by encoding a forbidden
factorization as a finite polynomial system in the unknown factor
coefficients.

This stage formalizes the generic algebraic engine:

* over an algebraically closed field and finitely many variables,
  an ideal with empty zero locus is the unit ideal;
* for a finitely indexed family of equations this gives an explicit finite
  identity
      `∑ H_i * E_i = 1`;
* such an identity immediately rules out a common zero.

This is exactly the kind of certificate that can later be cleared of
denominators and specialized in the graph parameters.
-/

/-- Weak Nullstellensatz in the exact form needed here:
an ideal in a finite-variable polynomial ring over an algebraically closed
field whose zero locus is empty is the whole ring. -/
theorem ideal_eq_top_of_zeroLocus_empty
    {K : Type*} [Field K] [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hzero :
      MvPolynomial.zeroLocus K I = ∅) :
    I = ⊤ := by
  have hvan :
      MvPolynomial.vanishingIdeal K
          (MvPolynomial.zeroLocus K I) =
        ⊤ := by
    rw [hzero]
    ext p
    simp [MvPolynomial.vanishingIdeal]
  have hrad : I.radical = ⊤ := by
    rw [←
      MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
        (K := K) I]
    exact hvan
  exact Ideal.radical_eq_top.mp hrad

/-- Finite-family version: if a finite collection of polynomial equations has
no common zero, then `1` is an explicit polynomial linear combination of the
equations. -/
theorem exists_nullstellensatz_linearCombination
    {K : Type*} [Field K] [IsAlgClosed K]
    {σ τ : Type*}
    [Finite σ] [Fintype τ]
    (E : τ → MvPolynomial σ K)
    (hzero :
      MvPolynomial.zeroLocus K
          (Ideal.span (Set.range E)) =
        ∅) :
    ∃ H : τ → MvPolynomial σ K,
      ∑ i : τ, H i * E i = 1 := by
  have htop :
      Ideal.span (Set.range E) = ⊤ :=
    ideal_eq_top_of_zeroLocus_empty
      (Ideal.span (Set.range E)) hzero
  have hone :
      (1 : MvPolynomial σ K) ∈
        Ideal.span (Set.range E) := by
    rw [htop]
    simp
  exact
    (Ideal.mem_span_range_iff_exists_fun.mp hone)

/-- Conversely, a finite identity `∑ H_i E_i = 1` rules out a common zero.

This direction does not require algebraic closedness. -/
theorem zeroLocus_span_range_eq_empty_of_linearCombination_one
    {K : Type*} [Field K]
    {σ τ : Type*}
    [Fintype τ]
    (E H : τ → MvPolynomial σ K)
    (hcert :
      ∑ i : τ, H i * E i = 1) :
    MvPolynomial.zeroLocus K
        (Ideal.span (Set.range E)) =
      ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hEach :
      ∀ i : τ,
        MvPolynomial.eval x (E i) = 0 := by
    intro i
    have hmem :
        E i ∈ Ideal.span (Set.range E) :=
      Ideal.subset_span (Set.mem_range_self i)
    exact
      (MvPolynomial.mem_zeroLocus_iff.mp hx)
        (E i) hmem
  have hEval :=
    congrArg (MvPolynomial.eval x) hcert
  have hzero : (0 : K) = 1 := by
    simpa [hEach] using hEval
  exact zero_ne_one hzero

/-- The two finite formulations are equivalent over an algebraically closed
field. -/
theorem zeroLocus_empty_iff_exists_linearCombination_one
    {K : Type*} [Field K] [IsAlgClosed K]
    {σ τ : Type*}
    [Finite σ] [Fintype τ]
    (E : τ → MvPolynomial σ K) :
    MvPolynomial.zeroLocus K
        (Ideal.span (Set.range E)) =
      ∅
    ↔
    ∃ H : τ → MvPolynomial σ K,
      ∑ i : τ, H i * E i = 1 := by
  constructor
  · exact
      exists_nullstellensatz_linearCombination E
  · rintro ⟨H, hH⟩
    exact
      zeroLocus_span_range_eq_empty_of_linearCombination_one
        E H hH

/-- Pointwise evaluation of a Nullstellensatz identity.

If every equation vanished at a point, the identity would evaluate to
`0 = 1`; hence at least one equation is nonzero there. -/
theorem exists_equation_eval_ne_zero_of_linearCombination_one
    {K : Type*} [Field K]
    {σ τ : Type*}
    [Fintype τ]
    (E H : τ → MvPolynomial σ K)
    (hcert :
      ∑ i : τ, H i * E i = 1)
    (x : σ → K) :
    ∃ i : τ,
      MvPolynomial.eval x (E i) ≠ 0 := by
  by_contra h
  push_neg at h
  have hEval :=
    congrArg (MvPolynomial.eval x) hcert
  have : (0 : K) = 1 := by
    simpa [h] using hEval
  exact zero_ne_one this

/-!
Stage-21 audit
--------------

The formalization now has an internal replacement for the phrase
"the inconsistent factorization equations have a Nullstellensatz
certificate":

    empty common-zero locus
       ↔
    finite identity `∑ H_i E_i = 1`.

No elimination theorem, projective-space compactness, or scheme-theoretic
openness is assumed.

The next step is finite combinatorics:
for a fixed degree bound and a fixed candidate factor-degree split, introduce
finitely many coefficient variables for the two factors and finitely many
coefficient equations saying their product equals the target graph section.
After a normalization coefficient is fixed to `1`, solutions of that finite
system are exactly normalized factorizations.

Those systems can then be fed directly into the lemmas above.
-/



/-!
## Stages 22--24 retired

The earlier arbitrary-basis bounded-degree factorization encoding has been
removed from the executable development. Stage 25 below gives the canonical
monomial-coordinate encoding used by every subsequent argument, including all
base-change-sensitive steps. No theorem below this point references the
retired encoding.
-/

/-! ## Stage 25: canonical monomial coordinates, stable under field extension

Stages 22--24 used an arbitrary chosen basis of the bounded-degree polynomial
space.  That is sufficient over one fixed field, but the chosen bases over
`F` and over an extension `L/F` are unrelated definitionally.

For the final Bertini descent we therefore switch to canonical monomial
coordinates.  The index
\[
  \{\alpha : \mathbf N^n : |\alpha|\le d\}
\]
depends only on `n,d`, not on the coefficient field.

This makes every factorization equation commute literally with coefficient
extension.  The arbitrary-basis system remains useful but is no longer used
for the base-change-sensitive core.
-/

/-- Canonical finite type of monomials in `n` variables of total degree at
most `d`. -/
abbrev DegreeMonomial (n d : ℕ) :=
  { a : Fin n →₀ ℕ // Finsupp.degree a ≤ d }

noncomputable instance degreeMonomialFintype
    (n d : ℕ) :
    Fintype (DegreeMonomial n d) :=
  (Finsupp.finite_of_degree_le d).fintype

/-- Canonical bounded polynomial represented by its monomial coefficients. -/
noncomputable def canonicalBoundedPolynomial
    {K : Type*} [CommSemiring K]
    {n d : ℕ}
    (c : DegreeMonomial n d → K) :
    Poly K n :=
  ∑ a : DegreeMonomial n d,
    MvPolynomial.monomial a.1 (c a)

/-- A canonical bounded polynomial really has total degree at most `d`. -/
lemma canonicalBoundedPolynomial_totalDegree_le
    {K : Type*} [CommSemiring K]
    {n d : ℕ}
    (c : DegreeMonomial n d → K) :
    (canonicalBoundedPolynomial c).totalDegree ≤ d := by
  classical
  unfold canonicalBoundedPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  have ha :
      a.1.sum (fun _ e => e) ≤ d := by
    change Finsupp.degree a.1 ≤ d
    exact a.2
  exact
    (MvPolynomial.totalDegree_monomial_le a.1 (c a)).trans ha

/-- The coefficient of the monomial indexed by `a` is exactly its canonical
coordinate. -/
@[simp] lemma coeff_canonicalBoundedPolynomial
    {K : Type*} [CommSemiring K]
    {n d : ℕ}
    (c : DegreeMonomial n d → K)
    (a : DegreeMonomial n d) :
    (canonicalBoundedPolynomial c).coeff a.1 =
      c a := by
  classical
  unfold canonicalBoundedPolynomial
  rw [MvPolynomial.coeff_sum]
  calc
    (∑ b : DegreeMonomial n d,
        (MvPolynomial.monomial b.1 (c b)).coeff a.1) =
        (MvPolynomial.monomial a.1 (c a)).coeff a.1 := by
      apply Fintype.sum_eq_single a
      intro b hba
      have hsupport : b.1 ≠ a.1 := by
        intro h
        apply hba
        exact Subtype.ext h
      simp [MvPolynomial.coeff_monomial, hsupport]
    _ = c a := by
      simp [MvPolynomial.coeff_monomial]

/-- A polynomial of total degree at most `d` is recovered from its canonical
bounded coefficient vector. -/
lemma canonicalBoundedPolynomial_coeff_eq
    {K : Type*} [CommSemiring K]
    {n d : ℕ}
    (p : Poly K n)
    (hp : p.totalDegree ≤ d) :
    canonicalBoundedPolynomial
        (fun a : DegreeMonomial n d =>
          p.coeff a.1) =
      p := by
  classical
  ext t
  by_cases ht : Finsupp.degree t ≤ d
  · let a : DegreeMonomial n d := ⟨t, ht⟩
    simpa [a] using
      (coeff_canonicalBoundedPolynomial
        (fun a : DegreeMonomial n d =>
          p.coeff a.1) a)
  · have hdt : d < Finsupp.degree t := by omega
    have hpt :
        p.coeff t = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      exact lt_of_le_of_lt hp hdt
    have hleft :
        (canonicalBoundedPolynomial
          (fun a : DegreeMonomial n d =>
            p.coeff a.1)).coeff t = 0 := by
      unfold canonicalBoundedPolynomial
      simp only [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro a ha
      have hat : a.1 ≠ t := by
        intro heq
        apply ht
        simpa [heq] using a.2
      simp [hat]
    rw [hleft, hpt]

/-- Canonical factor coefficient variables; importantly, this type is
independent of the coefficient field. -/
abbrev CanonicalFactorCoeffVar
    (n r s : ℕ) :=
  Sum (DegreeMonomial n r)
      (DegreeMonomial n s)

/-- Decode the left canonical factor from a coefficient-space point. -/
noncomputable def canonicalDecodedLeft
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → K) :
    Poly K n :=
  canonicalBoundedPolynomial
    (fun a : DegreeMonomial n r =>
      x (Sum.inl a))

/-- Decode the right canonical factor. -/
noncomputable def canonicalDecodedRight
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → K) :
    Poly K n :=
  canonicalBoundedPolynomial
    (fun b : DegreeMonomial n s =>
      x (Sum.inr b))

lemma canonicalDecodedLeft_totalDegree_le
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → K) :
    (canonicalDecodedLeft x).totalDegree ≤ r :=
  canonicalBoundedPolynomial_totalDegree_le _

lemma canonicalDecodedRight_totalDegree_le
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → K) :
    (canonicalDecodedRight x).totalDegree ≤ s :=
  canonicalBoundedPolynomial_totalDegree_le _

/-- Canonical factorization equation for output monomial `t`.

The quadratic part is the convolution of the two factor coefficient vectors.
No field-dependent structure constants occur. -/
noncomputable def canonicalFactorEquation
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (t : DegreeMonomial n d) :
    MvPolynomial
      (CanonicalFactorCoeffVar n r s) K :=
  (∑ a : DegreeMonomial n r,
      ∑ b : DegreeMonomial n s,
        if a.1 + b.1 = t.1 then
          MvPolynomial.X (Sum.inl a) *
            MvPolynomial.X (Sum.inr b)
        else 0) -
    MvPolynomial.C (P.coeff t.1)

/-- Coefficient formula for a product of canonically decoded factors. -/
lemma coeff_canonicalDecoded_mul
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → K)
    (t : Fin n →₀ ℕ) :
    (canonicalDecodedLeft x *
        canonicalDecodedRight x).coeff t =
      ∑ a : DegreeMonomial n r,
        ∑ b : DegreeMonomial n s,
          if a.1 + b.1 = t then
            x (Sum.inl a) * x (Sum.inr b)
          else 0 := by
  classical
  unfold canonicalDecodedLeft canonicalDecodedRight
  unfold canonicalBoundedPolynomial
  simp only [Finset.sum_mul, Finset.mul_sum,
    MvPolynomial.monomial_mul,
    MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_comm]
  simp [add_comm, mul_comm]

/-- Evaluation of the canonical factor equation is exactly product coefficient
minus target coefficient. -/
lemma eval_canonicalFactorEquation
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (t : DegreeMonomial n d)
    (x : CanonicalFactorCoeffVar n r s → K) :
    MvPolynomial.eval x
        (canonicalFactorEquation
          K n r s d P t) =
      (canonicalDecodedLeft x *
          canonicalDecodedRight x).coeff t.1 -
        P.coeff t.1 := by
  rw [coeff_canonicalDecoded_mul]
  simp [canonicalFactorEquation]
  rw [Finset.sum_comm]
  simp [add_comm, mul_comm]

/-- If both target and decoded product have total degree at most `d`, equality
of all canonical degree-`≤d` coefficients is equivalent to polynomial
equality. -/
lemma eq_of_canonical_coeff_eq
    {K : Type*} [CommSemiring K]
    {n d : ℕ}
    {p q : Poly K n}
    (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d)
    (hcoeff :
      ∀ t : DegreeMonomial n d,
        p.coeff t.1 = q.coeff t.1) :
    p = q := by
  ext t
  by_cases ht : Finsupp.degree t ≤ d
  · exact hcoeff ⟨t, ht⟩
  · have hdt : d < Finsupp.degree t := by omega
    have hp0 :
        p.coeff t = 0 :=
      MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        (lt_of_le_of_lt hp hdt)
    have hq0 :
        q.coeff t = 0 :=
      MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        (lt_of_le_of_lt hq hdt)
    rw [hp0, hq0]

/-- Vanishing of every canonical factor equation is exactly factorization,
provided the target has ambient total-degree bound `d` and `r+s≤d`. -/
theorem all_canonicalFactorEquation_zero_iff
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (x : CanonicalFactorCoeffVar n r s → K) :
    (∀ t : DegreeMonomial n d,
      MvPolynomial.eval x
        (canonicalFactorEquation
          K n r s d P t) = 0)
    ↔
    canonicalDecodedLeft x *
        canonicalDecodedRight x =
      P := by
  constructor
  · intro hz
    apply eq_of_canonical_coeff_eq
    · exact
        (MvPolynomial.totalDegree_mul
          (canonicalDecodedLeft x)
          (canonicalDecodedRight x)).trans
          (Nat.add_le_add
            (canonicalDecodedLeft_totalDegree_le x)
            (canonicalDecodedRight_totalDegree_le x) |>.trans hrs)
    · exact hP
    · intro t
      have ht := hz t
      rw [eval_canonicalFactorEquation] at ht
      exact sub_eq_zero.mp ht
  · intro hprod t
    rw [eval_canonicalFactorEquation]
    rw [hprod]
    exact sub_self _

/-- Ideal of the canonical factorization equations. -/
noncomputable def canonicalFactorEquationIdeal
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (P : Poly K n) :
    Ideal
      (MvPolynomial
        (CanonicalFactorCoeffVar n r s) K) :=
  Ideal.span
    (Set.range
      (canonicalFactorEquation
        K n r s d P))

/-- Exact zero-locus semantics of the canonical factorization ideal. -/
theorem mem_zeroLocus_canonicalFactorEquationIdeal_iff
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (x : CanonicalFactorCoeffVar n r s → K) :
    x ∈
      MvPolynomial.zeroLocus K
        (canonicalFactorEquationIdeal
          K n r s d P)
    ↔
    canonicalDecodedLeft x *
        canonicalDecodedRight x =
      P := by
  constructor
  · intro hx
    apply
      (all_canonicalFactorEquation_zero_iff
        K n r s d hrs P hP x).mp
    intro t
    have hmem :
        canonicalFactorEquation
            K n r s d P t ∈
          canonicalFactorEquationIdeal
            K n r s d P := by
      exact
        Ideal.subset_span
          (Set.mem_range_self t)
    exact
      (MvPolynomial.mem_zeroLocus_iff.mp hx)
        (canonicalFactorEquation
          K n r s d P t)
        hmem
  · intro hprod
    have hz :
        ∀ t : DegreeMonomial n d,
          MvPolynomial.eval x
            (canonicalFactorEquation
              K n r s d P t) = 0 :=
      (all_canonicalFactorEquation_zero_iff
        K n r s d hrs P hP x).mpr hprod
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro q hq
    let φ :
        MvPolynomial
            (CanonicalFactorCoeffVar n r s) K →+* K :=
      (MvPolynomial.aeval x).toRingHom
    have hgen :
        Set.range
            (canonicalFactorEquation
              K n r s d P) ⊆
          RingHom.ker φ := by
      rintro q ⟨t, rfl⟩
      change
        MvPolynomial.eval x
          (canonicalFactorEquation
            K n r s d P t) = 0
      exact hz t
    exact
      (Ideal.span_le.mpr hgen) hq

/-- Canonical coefficient equations commute exactly with coefficient-field
extension.  This is the main reason for replacing the arbitrary chosen basis. -/
lemma map_canonicalFactorEquation
    {F L : Type*}
    [CommRing F] [CommRing L]
    (φ : F →+* L)
    (n r s d : ℕ)
    (P : Poly F n)
    (t : DegreeMonomial n d) :
    MvPolynomial.map φ
        (canonicalFactorEquation
          F n r s d P t) =
      canonicalFactorEquation
        L n r s d
        (MvPolynomial.map φ P) t := by
  classical
  unfold canonicalFactorEquation
  simp only [map_sub, map_sum, MvPolynomial.map_C]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a.1 + b.1 = t.1
    · simp [hab]
    · simp [hab]
  · simp [MvPolynomial.coeff_map]

/-- Canonical decoded factors also commute with coefficient extension. -/
lemma map_canonicalDecodedLeft
    {F L : Type*}
    [CommRing F] [CommRing L]
    (φ : F →+* L)
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → F) :
    MvPolynomial.map φ
        (canonicalDecodedLeft x) =
      canonicalDecodedLeft
        (fun v => φ (x v)) := by
  classical
  simp [canonicalDecodedLeft,
    canonicalBoundedPolynomial]

lemma map_canonicalDecodedRight
    {F L : Type*}
    [CommRing F] [CommRing L]
    (φ : F →+* L)
    {n r s : ℕ}
    (x : CanonicalFactorCoeffVar n r s → F) :
    MvPolynomial.map φ
        (canonicalDecodedRight x) =
      canonicalDecodedRight
        (fun v => φ (x v)) := by
  classical
  simp [canonicalDecodedRight,
    canonicalBoundedPolynomial]

/-- A nonzero product over a field has exact total degree equal to the sum of
the factor total degrees. -/
lemma totalDegree_product_exact
    {K : Type*} [Field K]
    {n : ℕ}
    {p q : Poly K n}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).totalDegree =
      p.totalDegree + q.totalDegree := by
  exact
    MvPolynomial.totalDegree_mul_of_isDomain
      hp hq

/-!
Stage-25 audit
--------------

This stage fixes the base-change incompatibility in the arbitrary-basis model.

The final factorization system now uses:
* a field-independent finite monomial index `DegreeMonomial n d`;
* field-independent factor variable type `CanonicalFactorCoeffVar n r s`;
* equations with coefficients consisting only of target coefficients and
  `0,1`;
* exact coefficientwise base-change identity
  `map_canonicalFactorEquation`.

Therefore the system over a parameter function field `F` maps literally to
the same system over `AlgebraicClosure F`.

This is the correct coordinate model for the faithfully-flat descent of the
Nullstellensatz certificate.
-/



/-! ## Stage 26: exact affine systems for **proper** factorizations

The canonical equations of Stage 25 still allow trivial factorizations such as
`1 * P`.  That is not the reducibility condition.

We now make properness algebraic without projectivizing the factor spaces.

For each factor choose one coefficient belonging to a monomial of *positive*
total degree.  Add a new inverse-witness variable and the equation

    `z * c - 1 = 0`.

A solution therefore certifies that this positive-degree coefficient is
nonzero.  Over a field this forces the factor to be nonconstant, hence
nonunit.

There are only finitely many choices of positive-degree monomials inside a
fixed degree bound.  Taking the finite union over those choices will therefore
capture every genuine nonunit factorization.
-/

/-- Monomials of positive total degree within a fixed bound. -/
abbrev PositiveDegreeMonomial (n d : ℕ) :=
  { a : DegreeMonomial n d //
      1 ≤ Finsupp.degree (a.1 : Fin n →₀ ℕ) }

noncomputable instance positiveDegreeMonomialFintype
    (n d : ℕ) :
    Fintype (PositiveDegreeMonomial n d) := by
  classical
  exact Fintype.ofFinite (PositiveDegreeMonomial n d)

/-- Variables for a proper-factorization chart:
all ordinary left/right factor coefficients, plus two inverse witnesses. -/
abbrev ProperFactorCoeffVar
    (n r s : ℕ) :=
  Sum (CanonicalFactorCoeffVar n r s) (Fin 2)

/-- Forget the two inverse variables. -/
def properFactorBasePoint
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K) :
    CanonicalFactorCoeffVar n r s → K :=
  fun v => x (Sum.inl v)

/-- The left decoded factor of a proper-factor chart point. -/
noncomputable def properDecodedLeft
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K) :
    Poly K n :=
  canonicalDecodedLeft
    (properFactorBasePoint x)

/-- The right decoded factor. -/
noncomputable def properDecodedRight
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K) :
    Poly K n :=
  canonicalDecodedRight
    (properFactorBasePoint x)

@[simp] lemma coeff_properDecodedLeft
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K)
    (a : DegreeMonomial n r) :
    (properDecodedLeft x).coeff a.1 =
      x (Sum.inl (Sum.inl a)) := by
  simp [properDecodedLeft, properFactorBasePoint,
    canonicalDecodedLeft,
    coeff_canonicalBoundedPolynomial]

@[simp] lemma coeff_properDecodedRight
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K)
    (b : DegreeMonomial n s) :
    (properDecodedRight x).coeff b.1 =
      x (Sum.inl (Sum.inr b)) := by
  simp [properDecodedRight, properFactorBasePoint,
    canonicalDecodedRight,
    coeff_canonicalBoundedPolynomial]

lemma properDecodedLeft_totalDegree_le
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K) :
    (properDecodedLeft x).totalDegree ≤ r :=
  canonicalDecodedLeft_totalDegree_le _

lemma properDecodedRight_totalDegree_le
    {K : Type*} [CommSemiring K]
    {n r s : ℕ}
    (x : ProperFactorCoeffVar n r s → K) :
    (properDecodedRight x).totalDegree ≤ s :=
  canonicalDecodedRight_totalDegree_le _

/-- Equation index:
the product-coefficient equations, followed by the two inverse equations. -/
abbrev ProperFactorEquationIndex (n d : ℕ) :=
  Sum (DegreeMonomial n d) (Fin 2)

/-- The proper-factorization equation in the chart where the selected
positive-degree left and right coefficients are `α` and `β`. -/
noncomputable def properFactorEquation
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) :
    ProperFactorEquationIndex n d →
      MvPolynomial (ProperFactorCoeffVar n r s) K
  | Sum.inl t =>
      (∑ a : DegreeMonomial n r,
          ∑ b : DegreeMonomial n s,
            if a.1 + b.1 = t.1 then
              MvPolynomial.X
                  (Sum.inl (Sum.inl a)) *
                MvPolynomial.X
                  (Sum.inl (Sum.inr b))
            else 0) -
        MvPolynomial.C (P.coeff t.1)
  | Sum.inr k =>
      Fin.cases
        (MvPolynomial.X (Sum.inr (0 : Fin 2)) *
            MvPolynomial.X
              (Sum.inl (Sum.inl α.1)) -
          1)
        (fun _ =>
          MvPolynomial.X (Sum.inr (1 : Fin 2)) *
              MvPolynomial.X
                (Sum.inl (Sum.inr β.1)) -
            1)
        k

/-- Product-coordinate equations have the expected semantics. -/
lemma eval_properFactorEquation_product
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (t : DegreeMonomial n d)
    (x : ProperFactorCoeffVar n r s → K) :
    MvPolynomial.eval x
        (properFactorEquation
          K n r s d P α β (Sum.inl t)) =
      (properDecodedLeft x *
          properDecodedRight x).coeff t.1 -
        P.coeff t.1 := by
  unfold properDecodedLeft properDecodedRight
  rw [coeff_canonicalDecoded_mul]
  simp [properFactorEquation, properFactorBasePoint]
  rw [Finset.sum_comm]
  simp [add_comm, mul_comm]

/-- The left inverse equation says exactly that the inverse witness multiplied
by the selected positive-degree coefficient is `1`. -/
lemma eval_properFactorEquation_leftInv
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (x : ProperFactorCoeffVar n r s → K) :
    MvPolynomial.eval x
        (properFactorEquation
          K n r s d P α β
          (Sum.inr (0 : Fin 2))) =
      x (Sum.inr (0 : Fin 2)) *
          (properDecodedLeft x).coeff α.1.1 -
        1 := by
  simp [properFactorEquation, properDecodedLeft,
    properFactorBasePoint, canonicalDecodedLeft,
    coeff_canonicalBoundedPolynomial]

/-- The right inverse equation. -/
lemma eval_properFactorEquation_rightInv
    (K : Type*) [CommRing K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (x : ProperFactorCoeffVar n r s → K) :
    MvPolynomial.eval x
        (properFactorEquation
          K n r s d P α β
          (Sum.inr (1 : Fin 2))) =
      x (Sum.inr (1 : Fin 2)) *
          (properDecodedRight x).coeff β.1.1 -
        1 := by
  rw [coeff_properDecodedRight]
  simp [properFactorEquation]

/-- Vanishing of all equations in one proper-factor chart has exact semantics:
the product is the target and both selected coefficients have explicit
multiplicative inverses. -/
theorem all_properFactorEquation_zero_iff
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (x : ProperFactorCoeffVar n r s → K) :
    (∀ e : ProperFactorEquationIndex n d,
      MvPolynomial.eval x
        (properFactorEquation
          K n r s d P α β e) = 0)
    ↔
    properDecodedLeft x *
        properDecodedRight x = P ∧
      x (Sum.inr (0 : Fin 2)) *
          (properDecodedLeft x).coeff α.1.1 = 1 ∧
      x (Sum.inr (1 : Fin 2)) *
          (properDecodedRight x).coeff β.1.1 = 1 := by
  constructor
  · intro hz
    have hprodCoeff :
        ∀ t : DegreeMonomial n d,
          (properDecodedLeft x *
              properDecodedRight x).coeff t.1 =
            P.coeff t.1 := by
      intro t
      have ht := hz (Sum.inl t)
      rw [eval_properFactorEquation_product] at ht
      exact sub_eq_zero.mp ht
    have hprod :
        properDecodedLeft x *
            properDecodedRight x = P := by
      apply eq_of_canonical_coeff_eq
      · exact
          (MvPolynomial.totalDegree_mul
            (properDecodedLeft x)
            (properDecodedRight x)).trans
            ((Nat.add_le_add
              (properDecodedLeft_totalDegree_le x)
              (properDecodedRight_totalDegree_le x)).trans hrs)
      · exact hP
      · exact hprodCoeff
    have hL := hz (Sum.inr (0 : Fin 2))
    have hR := hz (Sum.inr (1 : Fin 2))
    rw [eval_properFactorEquation_leftInv] at hL
    rw [eval_properFactorEquation_rightInv] at hR
    exact
      ⟨hprod, sub_eq_zero.mp hL,
        sub_eq_zero.mp hR⟩
  · rintro ⟨hprod, hL, hR⟩ e
    rcases e with t | k
    · rw [eval_properFactorEquation_product]
      rw [hprod]
      exact sub_self _
    · fin_cases k
      · change
          MvPolynomial.eval x
            (properFactorEquation
              K n r s d P α β (Sum.inr (0 : Fin 2))) = 0
        rw [eval_properFactorEquation_leftInv]
        exact sub_eq_zero.mpr hL
      · change
          MvPolynomial.eval x
            (properFactorEquation
              K n r s d P α β (Sum.inr (1 : Fin 2))) = 0
        rw [eval_properFactorEquation_rightInv]
        exact sub_eq_zero.mpr hR

/-- The ideal generated by one proper-factorization chart. -/
noncomputable def properFactorEquationIdeal
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) :
    Ideal
      (MvPolynomial
        (ProperFactorCoeffVar n r s) K) :=
  Ideal.span
    (Set.range
      (properFactorEquation
        K n r s d P α β))

/-- Exact zero-locus semantics of one proper-factor chart. -/
theorem mem_zeroLocus_properFactorEquationIdeal_iff
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (x : ProperFactorCoeffVar n r s → K) :
    x ∈
      MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)
    ↔
    properDecodedLeft x *
          properDecodedRight x = P ∧
      x (Sum.inr (0 : Fin 2)) *
          (properDecodedLeft x).coeff α.1.1 = 1 ∧
      x (Sum.inr (1 : Fin 2)) *
          (properDecodedRight x).coeff β.1.1 = 1 := by
  constructor
  · intro hx
    apply
      (all_properFactorEquation_zero_iff
        K n r s d hrs P hP α β x).mp
    intro e
    have hmem :
        properFactorEquation
            K n r s d P α β e ∈
          properFactorEquationIdeal
            K n r s d P α β := by
      exact
        Ideal.subset_span
          (Set.mem_range_self e)
    exact
      (MvPolynomial.mem_zeroLocus_iff.mp hx)
        (properFactorEquation
          K n r s d P α β e)
        hmem
  · intro hsem
    have hz :
        ∀ e : ProperFactorEquationIndex n d,
          MvPolynomial.eval x
            (properFactorEquation
              K n r s d P α β e) = 0 :=
      (all_properFactorEquation_zero_iff
        K n r s d hrs P hP α β x).mpr hsem
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro q hq
    let φ :
        MvPolynomial
            (ProperFactorCoeffVar n r s) K →+* K :=
      (MvPolynomial.aeval x).toRingHom
    have hgen :
        Set.range
            (properFactorEquation
              K n r s d P α β) ⊆
          RingHom.ker φ := by
      rintro q ⟨e, rfl⟩
      change
        MvPolynomial.eval x
          (properFactorEquation
            K n r s d P α β e) = 0
      exact hz e
    exact
      (Ideal.span_le.mpr hgen) hq

/-- The selected left coefficient in any common zero is nonzero. -/
lemma selectedLeftCoeff_ne_zero_of_mem_zeroLocus
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    {x : ProperFactorCoeffVar n r s → K}
    (hx :
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)) :
    (properDecodedLeft x).coeff α.1.1 ≠ 0 := by
  have hsem :=
    (mem_zeroLocus_properFactorEquationIdeal_iff
      K n r s d hrs P hP α β x).mp hx
  intro hzero
  have hL := hsem.2.1
  rw [hzero, mul_zero] at hL
  exact zero_ne_one hL

/-- Likewise for the selected right coefficient. -/
lemma selectedRightCoeff_ne_zero_of_mem_zeroLocus
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    {x : ProperFactorCoeffVar n r s → K}
    (hx :
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)) :
    (properDecodedRight x).coeff β.1.1 ≠ 0 := by
  have hsem :=
    (mem_zeroLocus_properFactorEquationIdeal_iff
      K n r s d hrs P hP α β x).mp hx
  intro hzero
  have hR := hsem.2.2
  rw [hzero, mul_zero] at hR
  exact zero_ne_one hR

/-- A polynomial over a field with a nonzero positive-degree coefficient is
not a unit. -/
lemma not_isUnit_of_positiveDegree_coeff_ne_zero
    {K : Type*} [Field K]
    {n : ℕ}
    {p : Poly K n}
    {a : Fin n →₀ ℕ}
    (ha : 1 ≤ Finsupp.degree a)
    (hcoeff : p.coeff a ≠ 0) :
    ¬ IsUnit p := by
  intro hpU
  obtain ⟨c, hcU, hpc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := p)).mp hpU
  have hcoeffC :=
    congrArg (fun q : Poly K n => q.coeff a) hpc
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  have hCa :
      (MvPolynomial.C c : Poly K n).coeff a = 0 := by
    rw [MvPolynomial.coeff_C]
    simp [ha0]
  have : p.coeff a = 0 := by
    rw [hpc]
    exact hCa
  exact hcoeff this

/-- Therefore every common zero of a proper-factor chart decodes to two
nonunit factors. -/
lemma properDecodedLeft_not_isUnit_of_mem_zeroLocus
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    {x : ProperFactorCoeffVar n r s → K}
    (hx :
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)) :
    ¬ IsUnit (properDecodedLeft x) := by
  exact
    not_isUnit_of_positiveDegree_coeff_ne_zero
      α.2
      (selectedLeftCoeff_ne_zero_of_mem_zeroLocus
        K n r s d hrs P hP α β hx)

lemma properDecodedRight_not_isUnit_of_mem_zeroLocus
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    {x : ProperFactorCoeffVar n r s → K}
    (hx :
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)) :
    ¬ IsUnit (properDecodedRight x) := by
  exact
    not_isUnit_of_positiveDegree_coeff_ne_zero
      β.2
      (selectedRightCoeff_ne_zero_of_mem_zeroLocus
        K n r s d hrs P hP α β hx)

/-- Given an actual bounded factorization with the selected positive-degree
coefficients nonzero, construct a common zero by using their inverses as the
two witness variables. -/
theorem exists_mem_zeroLocus_properFactorEquationIdeal_of_factorization
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hP : P.totalDegree ≤ d)
    (p q : Poly K n)
    (hpdeg : p.totalDegree ≤ r)
    (hqdeg : q.totalDegree ≤ s)
    (hpq : p * q = P)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (hα : p.coeff α.1.1 ≠ 0)
    (hβ : q.coeff β.1.1 ≠ 0) :
    ∃ x : ProperFactorCoeffVar n r s → K,
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β) := by
  let pCoords : DegreeMonomial n r → K :=
    fun a => p.coeff a.1
  let qCoords : DegreeMonomial n s → K :=
    fun b => q.coeff b.1
  let x : ProperFactorCoeffVar n r s → K
    | Sum.inl (Sum.inl a) => pCoords a
    | Sum.inl (Sum.inr b) => qCoords b
    | Sum.inr k =>
        Fin.cases
          (p.coeff α.1.1)⁻¹
          (fun _ => (q.coeff β.1.1)⁻¹)
          k
  have hpDecode :
      properDecodedLeft x = p := by
    unfold properDecodedLeft canonicalDecodedLeft
    change
      canonicalBoundedPolynomial pCoords = p
    exact
      canonicalBoundedPolynomial_coeff_eq
        p hpdeg
  have hqDecode :
      properDecodedRight x = q := by
    unfold properDecodedRight canonicalDecodedRight
    change
      canonicalBoundedPolynomial qCoords = q
    exact
      canonicalBoundedPolynomial_coeff_eq
        q hqdeg
  refine ⟨x, ?_⟩
  rw [mem_zeroLocus_properFactorEquationIdeal_iff
    K n r s d hrs P hP α β x]
  constructor
  · simpa [hpDecode, hqDecode] using hpq
  constructor
  · rw [hpDecode]
    change (p.coeff α.1.1)⁻¹ * p.coeff α.1.1 = 1
    exact inv_mul_cancel₀ hα
  · rw [hqDecode]
    change (q.coeff β.1.1)⁻¹ * q.coeff β.1.1 = 1
    exact inv_mul_cancel₀ hβ

/-!
Stage-26 audit
--------------

The trivial-factor loophole is now closed.

A common zero of a `properFactorEquationIdeal` gives:
* a genuine product factorization of the target;
* a nonzero positive-degree coefficient in each factor;
* hence both factors are nonunits.

Conversely, any bounded factorization together with chosen nonzero
positive-degree coefficients produces a common zero by adjoining inverse
witnesses.

What remains for the finite-cover argument is to prove that every nonzero
nonunit polynomial of total degree at most `r` has at least one nonzero
positive-degree coefficient among `PositiveDegreeMonomial n r`.  That is an
elementary finite-support lemma and will make the union over
`(r,s,α,β)` exactly equal to the reducible locus.
-/



/-! ## Stage 27: finite proper-factor charts exactly cover reducibility -/

lemma totalDegree_pos_of_ne_zero_not_isUnit
    {K : Type*} [Field K]
    {n : ℕ}
    {p : Poly K n}
    (hp0 : p ≠ 0)
    (hpU : ¬ IsUnit p) :
    1 ≤ p.totalDegree := by
  by_contra h
  have hdeg0 : p.totalDegree = 0 := by omega
  have hpC :
      p = MvPolynomial.C (p.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp0
    rw [hpC, hc]
    simp
  have hCU :
      IsUnit (MvPolynomial.C (p.coeff 0) : Poly K n) := by
    exact
      (IsUnit.mk0 (p.coeff 0) hc0).map
        (MvPolynomial.C : K →+* Poly K n)
  apply hpU
  rw [hpC]
  exact hCU

lemma exists_positive_degree_coeff_of_totalDegree_pos
    {K : Type*} [Field K]
    {n : ℕ}
    {p : Poly K n}
    (hdeg : 1 ≤ p.totalDegree) :
    ∃ a : Fin n →₀ ℕ,
      1 ≤ Finsupp.degree a ∧
      p.coeff a ≠ 0 := by
  by_contra h
  push_neg at h
  have hconst :
      p = MvPolynomial.C (p.coeff 0) := by
    ext a
    by_cases ha0 : a = 0
    · subst a
      simp
    · have hapos : 1 ≤ Finsupp.degree a := by
        have hdegne : Finsupp.degree a ≠ 0 := by
          intro hz
          apply ha0
          exact (Finsupp.degree_eq_zero_iff a).mp hz
        omega
      have hcoeff0 : p.coeff a = 0 :=
        h a hapos
      rw [hcoeff0]
      have ha0' : (0 : Fin n →₀ ℕ) ≠ a := Ne.symm ha0
      simp [ha0, ha0']
  have hdeg0 : p.totalDegree = 0 := by
    rw [hconst]
    exact MvPolynomial.totalDegree_C (p.coeff 0)
  omega

theorem exists_positiveDegreeMonomial_coeff_ne_zero
    {K : Type*} [Field K]
    {n r : ℕ}
    {p : Poly K n}
    (hp0 : p ≠ 0)
    (hpU : ¬ IsUnit p)
    (hpdeg : p.totalDegree ≤ r) :
    ∃ α : PositiveDegreeMonomial n r,
      p.coeff α.1.1 ≠ 0 := by
  obtain ⟨a, haPos, haCoeff⟩ :=
    exists_positive_degree_coeff_of_totalDegree_pos
      (totalDegree_pos_of_ne_zero_not_isUnit hp0 hpU)
  have hadeg : Finsupp.degree a ≤ r := by
    have hmem : a ∈ p.support := by
      simpa [MvPolynomial.mem_support_iff] using haCoeff
    have hle :
        Finsupp.degree a ≤ p.totalDegree :=
      MvPolynomial.le_totalDegree hmem
    exact le_trans hle hpdeg
  let A : DegreeMonomial n r := ⟨a, hadeg⟩
  let α : PositiveDegreeMonomial n r := ⟨A, haPos⟩
  exact ⟨α, by simpa [α, A] using haCoeff⟩

lemma factors_ne_zero_of_mul_ne_zero
    {K : Type*} [Field K]
    {n : ℕ}
    {p q : Poly K n}
    (hpq : p * q ≠ 0) :
    p ≠ 0 ∧ q ≠ 0 := by
  exact
    ⟨fun hp => hpq (by rw [hp, zero_mul]),
      fun hq => hpq (by rw [hq, mul_zero])⟩

theorem reducible_gives_properFactor_chart
    {K : Type*} [Field K]
    {n d : ℕ}
    {P : Poly K n}
    (hP0 : P ≠ 0)
    (hPU : ¬ IsUnit P)
    (hPred : ¬ Irreducible P)
    (hPdeg : P.totalDegree ≤ d) :
    ∃ r s : ℕ,
      ∃ hrs : r + s ≤ d,
      ∃ α : PositiveDegreeMonomial n r,
      ∃ β : PositiveDegreeMonomial n s,
      ∃ x : ProperFactorCoeffVar n r s → K,
        x ∈ MvPolynomial.zeroLocus K
          (properFactorEquationIdeal
            K n r s d P α β) := by
  rcases irreducible_or_factor hPU with hI | hsplit
  · exact False.elim (hPred hI)
  · rcases hsplit with ⟨p, q, hpU, hqU, hpq⟩
    have hpq0 : p * q ≠ 0 := by
      rw [← hpq]
      exact hP0
    have hnonzero := factors_ne_zero_of_mul_ne_zero hpq0
    have hp0 : p ≠ 0 := hnonzero.1
    have hq0 : q ≠ 0 := hnonzero.2
    let r : ℕ := p.totalDegree
    let s : ℕ := q.totalDegree
    have hrsEq : r + s = P.totalDegree := by
      dsimp [r, s]
      rw [hpq]
      exact (totalDegree_product_exact hp0 hq0).symm
    have hrs : r + s ≤ d := by
      rw [hrsEq]
      exact hPdeg
    have hpdeg : p.totalDegree ≤ r := le_rfl
    have hqdeg : q.totalDegree ≤ s := le_rfl
    obtain ⟨α, hα⟩ :=
      exists_positiveDegreeMonomial_coeff_ne_zero
        hp0 hpU hpdeg
    obtain ⟨β, hβ⟩ :=
      exists_positiveDegreeMonomial_coeff_ne_zero
        hq0 hqU hqdeg
    obtain ⟨x, hx⟩ :=
      exists_mem_zeroLocus_properFactorEquationIdeal_of_factorization
        K n r s d hrs P hPdeg
        p q hpdeg hqdeg hpq.symm α β hα hβ
    exact ⟨r, s, hrs, α, β, x, hx⟩

theorem not_irreducible_of_mem_properFactor_chart
    {K : Type*} [Field K]
    {n r s d : ℕ}
    {P : Poly K n}
    (hrs : r + s ≤ d)
    (hPdeg : P.totalDegree ≤ d)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    {x : ProperFactorCoeffVar n r s → K}
    (hx :
      x ∈ MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β)) :
    ¬ Irreducible P := by
  intro hI
  have hsem :=
    (mem_zeroLocus_properFactorEquationIdeal_iff
      K n r s d hrs P hPdeg α β x).mp hx
  have hpU :
      ¬ IsUnit (properDecodedLeft x) :=
    properDecodedLeft_not_isUnit_of_mem_zeroLocus
      K n r s d hrs P hPdeg α β hx
  have hqU :
      ¬ IsUnit (properDecodedRight x) :=
    properDecodedRight_not_isUnit_of_mem_zeroLocus
      K n r s d hrs P hPdeg α β hx
  have hor :=
    hI.isUnit_or_isUnit hsem.1.symm
  exact hor.elim hpU hqU

theorem not_irreducible_iff_exists_properFactor_chart
    {K : Type*} [Field K]
    {n d : ℕ}
    {P : Poly K n}
    (hP0 : P ≠ 0)
    (hPU : ¬ IsUnit P)
    (hPdeg : P.totalDegree ≤ d) :
    ¬ Irreducible P
    ↔
    ∃ r s : ℕ,
      ∃ hrs : r + s ≤ d,
      ∃ α : PositiveDegreeMonomial n r,
      ∃ β : PositiveDegreeMonomial n s,
      ∃ x : ProperFactorCoeffVar n r s → K,
        x ∈ MvPolynomial.zeroLocus K
          (properFactorEquationIdeal
            K n r s d P α β) := by
  constructor
  · intro hred
    exact
      reducible_gives_properFactor_chart
        hP0 hPU hred hPdeg
  · rintro ⟨r, s, hrs, α, β, x, hx⟩
    exact
      not_irreducible_of_mem_properFactor_chart
        hrs hPdeg α β hx

/-! ### Finite type of all positive degree splits up to an ambient bound -/

/-- Positive factor-degree bounds `r,s` with `r+s ≤ d`. -/
abbrev PositiveDegreeSplit (d : ℕ) :=
  { rs : Fin (d + 1) × Fin (d + 1) //
      1 ≤ rs.1.1 ∧
      1 ≤ rs.2.1 ∧
      rs.1.1 + rs.2.1 ≤ d }

instance positiveDegreeSplitFintype
    (d : ℕ) :
    Fintype (PositiveDegreeSplit d) :=
  inferInstance

def PositiveDegreeSplit.left
    {d : ℕ}
    (s : PositiveDegreeSplit d) : ℕ :=
  s.1.1.1

def PositiveDegreeSplit.right
    {d : ℕ}
    (s : PositiveDegreeSplit d) : ℕ :=
  s.1.2.1

lemma PositiveDegreeSplit.left_pos
    {d : ℕ}
    (s : PositiveDegreeSplit d) :
    1 ≤ s.left :=
  s.2.1

lemma PositiveDegreeSplit.right_pos
    {d : ℕ}
    (s : PositiveDegreeSplit d) :
    1 ≤ s.right :=
  s.2.2.1

lemma PositiveDegreeSplit.sum_le
    {d : ℕ}
    (s : PositiveDegreeSplit d) :
    s.left + s.right ≤ d :=
  s.2.2.2

def mkPositiveDegreeSplit
    {d r s : ℕ}
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hrs : r + s ≤ d) :
    PositiveDegreeSplit d := by
  have hrle : r < d + 1 := by omega
  have hsle : s < d + 1 := by omega
  exact
    ⟨(⟨r, hrle⟩, ⟨s, hsle⟩),
      hr, hs, hrs⟩

@[simp] lemma mkPositiveDegreeSplit_left
    {d r s : ℕ}
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hrs : r + s ≤ d) :
    (mkPositiveDegreeSplit hr hs hrs).left = r := rfl

@[simp] lemma mkPositiveDegreeSplit_right
    {d r s : ℕ}
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hrs : r + s ≤ d) :
    (mkPositiveDegreeSplit hr hs hrs).right = s := rfl

abbrev ProperFactorChartIndex (n d : ℕ) : Type :=
  Σ rs : PositiveDegreeSplit d,
    PositiveDegreeMonomial n rs.left ×
      PositiveDegreeMonomial n rs.right

noncomputable instance properFactorChartIndexFintype
    (n d : ℕ) :
    Fintype (ProperFactorChartIndex n d) :=
  inferInstance

def ProperFactorChartIndex.left
    {n d : ℕ}
    (c : ProperFactorChartIndex n d) : ℕ :=
  c.1.left

def ProperFactorChartIndex.right
    {n d : ℕ}
    (c : ProperFactorChartIndex n d) : ℕ :=
  c.1.right

def ProperFactorChartIndex.leftMonomial
    {n d : ℕ}
    (c : ProperFactorChartIndex n d) :
    PositiveDegreeMonomial n c.left :=
  c.2.1

def ProperFactorChartIndex.rightMonomial
    {n d : ℕ}
    (c : ProperFactorChartIndex n d) :
    PositiveDegreeMonomial n c.right :=
  c.2.2

lemma ProperFactorChartIndex.sum_le
    {n d : ℕ}
    (c : ProperFactorChartIndex n d) :
    c.left + c.right ≤ d :=
  c.1.sum_le

/-!
Stage-27 audit

For every nonzero nonunit polynomial `P` of total degree at most `d`:

    `¬ Irreducible P`
      iff
    one of finitely many proper-factor charts has a common zero.

Thus degree drops, unit factors, and normalization are all handled internally.
-/



/-! ## Stage 28: Nullstellensatz certificate for every proper-factor chart

We now connect the exact finite-cover semantics to the Stage-21
Nullstellensatz engine.

For one proper-factor chart:
* irreducibility of the target implies the chart has empty zero locus;
* over an algebraically closed coefficient field this yields an explicit
  finite identity `∑ H_e E_e = 1`;
* the proper-factor equations commute coefficientwise with every field
  extension.

This is precisely the local certificate needed later over the algebraic
closure of the graph-parameter function field.
-/

/-- Proper-factor equations commute with coefficient extension. -/
lemma map_properFactorEquation
    {F L : Type*}
    [CommRing F] [CommRing L]
    (φ : F →+* L)
    (n r s d : ℕ)
    (P : Poly F n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (e : ProperFactorEquationIndex n d) :
    MvPolynomial.map φ
        (properFactorEquation
          F n r s d P α β e) =
      properFactorEquation
        L n r s d
        (MvPolynomial.map φ P)
        α β e := by
  classical
  rcases e with t | k
  · unfold properFactorEquation
    simp only [map_sub, map_sum, MvPolynomial.map_C]
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : a.1 + b.1 = t.1
      · simp [hab]
      · simp [hab]
    · simp [MvPolynomial.coeff_map]
  · fin_cases k <;>
      simp [properFactorEquation]

/-- If the target is irreducible, a proper-factor chart has no common zero. -/
theorem zeroLocus_properFactorEquationIdeal_eq_empty_of_irreducible
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hPdeg : P.totalDegree ≤ d)
    (hPI : Irreducible P)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) :
    MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β) =
      ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact
    (not_irreducible_of_mem_properFactor_chart
      hrs hPdeg α β hx) hPI

/-- Over an algebraically closed field, irreducibility of the target produces
an explicit Nullstellensatz identity for one proper-factor chart. -/
theorem exists_properFactor_nullstellensatz_certificate
    (K : Type*) [Field K] [IsAlgClosed K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hPdeg : P.totalDegree ≤ d)
    (hPI : Irreducible P)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) :
    ∃ H :
        ProperFactorEquationIndex n d →
          MvPolynomial
            (ProperFactorCoeffVar n r s) K,
      ∑ e : ProperFactorEquationIndex n d,
        H e *
          properFactorEquation
            K n r s d P α β e =
      1 := by
  apply
    exists_nullstellensatz_linearCombination
      (properFactorEquation
        K n r s d P α β)
  exact
    zeroLocus_properFactorEquationIdeal_eq_empty_of_irreducible
      K n r s d hrs P hPdeg hPI α β

/-- A chart-level certificate immediately excludes every common zero. -/
theorem no_common_zero_of_properFactor_certificate
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (H :
      ProperFactorEquationIndex n d →
        MvPolynomial
          (ProperFactorCoeffVar n r s) K)
    (hH :
      ∑ e : ProperFactorEquationIndex n d,
        H e *
          properFactorEquation
            K n r s d P α β e =
        1) :
    MvPolynomial.zeroLocus K
        (properFactorEquationIdeal
          K n r s d P α β) =
      ∅ := by
  exact
    zeroLocus_span_range_eq_empty_of_linearCombination_one
      (properFactorEquation
        K n r s d P α β)
      H hH

/-- A convenient proposition packaging the finite Nullstellensatz certificate
for one chart. -/
def HasProperFactorCertificate
    (K : Type*) [Field K]
    (n r s d : ℕ)
    (P : Poly K n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) : Prop :=
  ∃ H :
      ProperFactorEquationIndex n d →
        MvPolynomial
          (ProperFactorCoeffVar n r s) K,
    ∑ e : ProperFactorEquationIndex n d,
      H e *
        properFactorEquation
          K n r s d P α β e =
      1

/-- Irreducibility over an algebraically closed field gives a certificate for
every proper-factor chart. -/
theorem hasProperFactorCertificate_of_irreducible
    (K : Type*) [Field K] [IsAlgClosed K]
    (n r s d : ℕ)
    (hrs : r + s ≤ d)
    (P : Poly K n)
    (hPdeg : P.totalDegree ≤ d)
    (hPI : Irreducible P)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s) :
    HasProperFactorCertificate
      K n r s d P α β := by
  exact
    exists_properFactor_nullstellensatz_certificate
      K n r s d hrs P hPdeg hPI α β

/-- Package "every finite chart has a certificate" at one ambient degree
bound.  The chart types are dependent because the factor-variable space
depends on the split. -/
def AllProperFactorCertificates
    (K : Type*) [Field K]
    (n d : ℕ)
    (P : Poly K n) : Prop :=
  ∀ c : ProperFactorChartIndex n d,
    HasProperFactorCertificate
      K n c.left c.right d P
      c.leftMonomial c.rightMonomial

/-- An irreducible bounded polynomial over an algebraically closed field has
certificates in all finite charts. -/
theorem allProperFactorCertificates_of_irreducible
    (K : Type*) [Field K] [IsAlgClosed K]
    (n d : ℕ)
    (P : Poly K n)
    (hPdeg : P.totalDegree ≤ d)
    (hPI : Irreducible P) :
    AllProperFactorCertificates K n d P := by
  intro c
  exact
    hasProperFactorCertificate_of_irreducible
      K n c.left c.right d
      c.sum_le P hPdeg hPI
      c.leftMonomial c.rightMonomial

/-! ### Evaluation of a mapped chart equation

This lemma is useful when a certificate is transported to an extension field:
evaluation of the mapped equation agrees with applying the field map to the
original coefficients and evaluating there.
-/
lemma eval_map_properFactorEquation
    {F L : Type*}
    [Field F] [Field L]
    (φ : F →+* L)
    (n r s d : ℕ)
    (P : Poly F n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (e : ProperFactorEquationIndex n d)
    (x : ProperFactorCoeffVar n r s → L) :
    MvPolynomial.eval x
      (MvPolynomial.map φ
        (properFactorEquation
          F n r s d P α β e)) =
    MvPolynomial.eval x
      (properFactorEquation
        L n r s d
        (MvPolynomial.map φ P)
        α β e) := by
  rw [map_properFactorEquation]

/-!
Stage-28 audit
--------------

For every finite proper-factor chart we now have the exact chain

    irreducible target over algebraically closed field
      → empty chart zero locus
      → finite Nullstellensatz identity.

Moreover every equation commutes exactly with coefficient-field extension.

Thus the remaining complex Bertini core has been narrowed further:

1. construct the generic graph section over the rational function field in
   the graph parameters;
2. prove that this generic section remains irreducible over an algebraic
   closure (absolute irreducibility);
3. instantiate Stage 28 there;
4. descend/clear denominators in the finitely many certificate identities.

No reducibility-locus geometry remains implicit.
-/



/-! ## Stage 29: the generic graph section over the parameter function field

All finite reducibility charts are now in place.  We turn to the actual
generic member of the graph-hyperplane family.

Let
    `R_m = ℂ[A₀,...,A_{m-1}]`
and
    `F_m = Frac(R_m)`.
The generic graph parameter is the tuple of coordinate functions
`A_j ∈ F_m`.

For `f ∈ ℂ[X₀,...,X_m]`, the generic graph section is the polynomial over
`F_m`
\[
 f(X_0,\ldots,X_{m-1},\sum_j A_j X_j).
\]

This stage constructs that object directly from the existing `graphRestrict`
and records its elementary algebraic properties.  No irreducibility claim is
assumed.
-/

/-- Polynomial ring in the graph parameters. -/
abbrev GraphParamRing (m : ℕ) :=
  Poly ℂ m

/-- Rational function field in the graph parameters. -/
abbrev GraphParamField (m : ℕ) :=
  FractionRing (GraphParamRing m)

/-- The generic parameter coordinate `A_j` inside the parameter function
field. -/
noncomputable def genericGraphParam
    {m : ℕ} (j : Fin m) :
    GraphParamField m :=
  algebraMap (GraphParamRing m)
      (GraphParamField m)
      (MvPolynomial.X j)

/-- Coefficient embedding `ℂ → GraphParamField m`. -/
noncomputable def complexToGraphParamField
    (m : ℕ) :
    ℂ →+* GraphParamField m :=
  algebraMap ℂ (GraphParamField m)

/-- Extend a complex polynomial coefficientwise to the parameter function
field. -/
noncomputable def toGraphParamField
    {m n : ℕ}
    (f : Poly ℂ n) :
    Poly (GraphParamField m) n :=
  MvPolynomial.map
    (complexToGraphParamField m) f

@[simp] lemma toGraphParamField_C
    {m n : ℕ} (z : ℂ) :
    toGraphParamField
        (m := m) (n := n)
        (MvPolynomial.C z) =
      MvPolynomial.C
        ((complexToGraphParamField m) z) := by
  simp [toGraphParamField]

@[simp] lemma toGraphParamField_X
    {m n : ℕ} (i : Fin n) :
    toGraphParamField
        (m := m)
        (MvPolynomial.X i : Poly ℂ n) =
      MvPolynomial.X i := by
  simp [toGraphParamField]

/-- The generic graph section. -/
noncomputable def genericGraphSection
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    Poly (GraphParamField m) m :=
  graphRestrict
    (toGraphParamField (m := m) f)
    genericGraphParam

/-- Syntactic unfolding of the generic graph section. -/
lemma genericGraphSection_eq
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    genericGraphSection f =
      graphRestrict
        (toGraphParamField (m := m) f)
        genericGraphParam := rfl

/-- Pointwise evaluation formula for the generic graph section. -/
lemma eval_genericGraphSection
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (x : Fin m → GraphParamField m) :
    MvPolynomial.eval x
        (genericGraphSection f) =
      MvPolynomial.eval
        (graphPoint genericGraphParam x)
        (toGraphParamField (m := m) f) := by
  exact
    eval_graphRestrict
      (toGraphParamField (m := m) f)
      genericGraphParam x

/-- Explicit value of the last ambient coordinate at a generic graph point. -/
lemma graphPoint_generic_last
    {m : ℕ}
    (x : Fin m → GraphParamField m) :
    graphPoint genericGraphParam x
        (Fin.last m) =
      ∑ j : Fin m,
        genericGraphParam j * x j := by
  simp [graphPoint]

/-- The first `m` coordinates of a generic graph point are unchanged. -/
lemma graphPoint_generic_castSucc
    {m : ℕ}
    (x : Fin m → GraphParamField m)
    (i : Fin m) :
    graphPoint genericGraphParam x
        i.castSucc = x i := by
  simp [graphPoint]

/-- Coefficient extension preserves nonzeroness. -/
lemma toGraphParamField_ne_zero
    {m n : ℕ}
    {f : Poly ℂ n}
    (hf : f ≠ 0) :
    toGraphParamField (m := m) f ≠ 0 := by
  intro hzero
  apply hf
  apply
    (MvPolynomial.map_injective
      (algebraMap ℂ (GraphParamField m))
      (algebraMap ℂ (GraphParamField m)).injective)
  simpa using hzero

/-- Total degree does not increase under coefficient extension. -/
lemma totalDegree_toGraphParamField_le
    {m n : ℕ}
    (f : Poly ℂ n) :
    (toGraphParamField (m := m) f).totalDegree ≤
      f.totalDegree := by
  exact totalDegree_map_le' _ _

/-- Linear graph restriction does not increase total degree. -/
lemma totalDegree_genericGraphSection_le
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    (genericGraphSection f).totalDegree ≤
      f.totalDegree := by
  unfold genericGraphSection
  have hmap :
      (toGraphParamField (m := m) f).totalDegree ≤
        f.totalDegree :=
    totalDegree_toGraphParamField_le f
  have hrest :
      (graphRestrict
        (toGraphParamField (m := m) f)
        genericGraphParam).totalDegree ≤
      (toGraphParamField (m := m) f).totalDegree := by
    exact
      restrictLinear_totalDegree_le
        (toGraphParamField (m := m) f)
        (graphFrame genericGraphParam)
  exact le_trans hrest hmap

/-- The exact remaining geometric statement at the generic point.

This is a proposition, not an axiom or an assumed theorem:
for every irreducible complex polynomial in at least four ambient variables,
its generic graph-hyperplane section remains irreducible after extending the
parameter function field to an algebraic closure.

This is the fixed-point Bertini content in its sharpest algebraic form.
-/
def GenericGraphAbsoluteIrreducibility : Prop :=
  ∀ {m : ℕ}, 3 ≤ m →
    ∀ f : Poly ℂ (m + 1),
      Irreducible f →
      Irreducible
        (MvPolynomial.map
          (algebraMap
            (GraphParamField m)
            (AlgebraicClosure
              (GraphParamField m)))
          (genericGraphSection f))

/-! We do not descend irreducibility from the algebraic closure here.
For the later finite-chart argument we only need one nonzero positive-degree
coefficient, which can be extracted directly after scalar extension. -/

/-!
Stage-29 audit
--------------

The generic member of the graph family is now an explicit Lean polynomial
over the rational function field in the hyperplane parameters.

The remaining Bertini theorem has been sharpened to one concrete statement:

    `GenericGraphAbsoluteIrreducibility`.

It says exactly that the generic graph section of an irreducible complex
hypersurface is geometrically irreducible.

Everything after this statement should be elimination/denominator algebra:
Stage 28 supplies finite Nullstellensatz identities for all proper-factor
charts once this generic absolute irreducibility is proved.

No geometric irreducibility theorem has been assumed in Stage 29.
-/



/-! ## Stage 30: descend Nullstellensatz identities through a field extension

Let `F ⊆ L` be a field extension.  A Nullstellensatz certificate for equations
whose coefficients come from `F` may initially be produced over `L`
(e.g. `L = AlgebraicClosure F`).

Instead of invoking faithfully-flat descent for polynomial ideals, we use a
more elementary linear-algebra argument.

The canonical inclusion `F → L` is an injective `F`-linear map.  Mathlib's
`LinearMap.leftInverse` therefore supplies an `F`-linear retraction
`λ : L → F` satisfying `λ(algebraMap x) = x`.  Apply `λ` coefficientwise to
polynomials in the auxiliary factor variables.  Because the equations
themselves have coefficients in `F`, coefficientwise retraction commutes with
multiplication by those equations.

Consequently
    `∑ Hᵢ * map(Eᵢ) = 1` over `L`
descends to
    `∑ retract(Hᵢ) * Eᵢ = 1` over `F`.

This is enough to descend every Stage-28 proper-factor certificate from the
algebraic closure of the generic parameter field back to that field.
-/

/-- The canonical `F`-linear inclusion of a field into an extension has an
`F`-linear left inverse. -/
noncomputable def fieldCoeffRetraction
    (F L : Type*) [Field F] [Field L] [Algebra F L] :
    L →ₗ[F] F :=
  (Algebra.linearMap F L).leftInverse

/-- The coefficient retraction is genuinely a left inverse to `algebraMap`. -/
@[simp] lemma fieldCoeffRetraction_algebraMap
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    (a : F) :
    fieldCoeffRetraction F L
        ((algebraMap F L) a) = a := by
  unfold fieldCoeffRetraction
  apply LinearMap.leftInverse_apply_of_inj
  exact
    LinearMap.ker_eq_bot_of_injective
      (FaithfulSMul.algebraMap_injective F L)

/-- Apply the field-coefficient retraction coefficientwise to a multivariate
polynomial. -/
noncomputable def mvPolynomialCoeffRetraction
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ : Type*}
    (p : MvPolynomial σ L) :
    MvPolynomial σ F :=
  (Finsupp.mapRange.linearMap (fieldCoeffRetraction F L) :
    ((σ →₀ ℕ) →₀ L) →ₗ[F] ((σ →₀ ℕ) →₀ F)) p

@[simp] lemma coeff_mvPolynomialCoeffRetraction
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ : Type*}
    (p : MvPolynomial σ L)
    (d : σ →₀ ℕ) :
    (mvPolynomialCoeffRetraction F L p).coeff d =
      fieldCoeffRetraction F L (p.coeff d) := by
  rfl

lemma mvPolynomialCoeffRetraction_sum
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ τ : Type*} [Fintype τ]
    (p : τ → MvPolynomial σ L) :
    mvPolynomialCoeffRetraction F L (∑ i, p i) =
      ∑ i, mvPolynomialCoeffRetraction F L (p i) := by
  ext d
  simp [coeff_mvPolynomialCoeffRetraction]

/-- Coefficientwise retraction undoes coefficient extension. -/
@[simp] lemma mvPolynomialCoeffRetraction_map
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ : Type*}
    (p : MvPolynomial σ F) :
    mvPolynomialCoeffRetraction F L
        (MvPolynomial.map (algebraMap F L) p) =
      p := by
  ext d
  simp [MvPolynomial.coeff_map]

/-- The coefficientwise retraction sends `1` to `1`. -/
@[simp] lemma mvPolynomialCoeffRetraction_one
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ : Type*} :
    mvPolynomialCoeffRetraction F L
        (1 : MvPolynomial σ L) =
      1 := by
  have h :=
    mvPolynomialCoeffRetraction_map
      F L (1 : MvPolynomial σ F)
  simpa using h

/-- **Module compatibility over the base polynomial ring.**

Although `mvPolynomialCoeffRetraction` is not a ring homomorphism, it commutes
with multiplication by a polynomial whose coefficients lie in the base field.
This is the exact property needed to descend a linear-combination
Nullstellensatz identity. -/
lemma mvPolynomialCoeffRetraction_mul_map
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ L)
    (p : MvPolynomial σ F) :
    mvPolynomialCoeffRetraction F L
        (q * MvPolynomial.map (algebraMap F L) p) =
      mvPolynomialCoeffRetraction F L q * p := by
  ext d
  simp only [coeff_mvPolynomialCoeffRetraction]
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  simp_rw [MvPolynomial.coeff_map]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  have hscalar :
      q.coeff xy.1 *
          (algebraMap F L) (p.coeff xy.2) =
        p.coeff xy.2 • q.coeff xy.1 := by
    rw [Algebra.smul_def]
    exact mul_comm _ _
  rw [hscalar]
  rw [(fieldCoeffRetraction F L).map_smul]
  exact mul_comm _ _

/-- A finite linear-combination identity over a field extension descends to
the base field whenever all equations themselves come from the base field. -/
theorem exists_linearCombination_one_of_map_linearCombination_one
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {σ τ : Type*}
    [DecidableEq σ] [Fintype τ]
    (E : τ → MvPolynomial σ F)
    (hcert :
      ∃ H : τ → MvPolynomial σ L,
        ∑ i : τ,
          H i *
            MvPolynomial.map (algebraMap F L) (E i) =
        1) :
    ∃ H0 : τ → MvPolynomial σ F,
      ∑ i : τ, H0 i * E i = 1 := by
  rcases hcert with ⟨H, hH⟩
  let H0 : τ → MvPolynomial σ F :=
    fun i => mvPolynomialCoeffRetraction F L (H i)
  refine ⟨H0, ?_⟩
  have hret :=
    congrArg
      (fun p : MvPolynomial σ L =>
        mvPolynomialCoeffRetraction F L p)
      hH
  change
    mvPolynomialCoeffRetraction F L
        (∑ i : τ,
          H i *
            MvPolynomial.map (algebraMap F L) (E i)) =
      mvPolynomialCoeffRetraction F L 1
      at hret
  rw [mvPolynomialCoeffRetraction_sum] at hret
  simpa [H0, mvPolynomialCoeffRetraction_mul_map]
    using hret

/-- The previous theorem packaged as descent of `HasProperFactorCertificate`
along an arbitrary field extension.

The extension field need not be algebraically closed here; algebraic
closedness is only used upstream to *produce* the certificate. -/
theorem hasProperFactorCertificate_of_map_certificate
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    (n r s d : ℕ)
    (P : Poly F n)
    (α : PositiveDegreeMonomial n r)
    (β : PositiveDegreeMonomial n s)
    (hcertL :
      HasProperFactorCertificate
        L n r s d
        (MvPolynomial.map (algebraMap F L) P)
        α β) :
    HasProperFactorCertificate
      F n r s d P α β := by
  rcases hcertL with ⟨H, hH⟩
  have hmapped :
      ∃ HL :
          ProperFactorEquationIndex n d →
            MvPolynomial
              (ProperFactorCoeffVar n r s) L,
        ∑ e : ProperFactorEquationIndex n d,
          HL e *
            MvPolynomial.map (algebraMap F L)
              (properFactorEquation
                F n r s d P α β e) =
          1 := by
    refine ⟨H, ?_⟩
    simpa only
      [map_properFactorEquation]
      using hH
  exact
    exists_linearCombination_one_of_map_linearCombination_one
      F L
      (properFactorEquation
        F n r s d P α β)
      hmapped

/-- If a polynomial becomes irreducible over an algebraically closed field
extension, then every proper-factor chart already has a Nullstellensatz
certificate over the base field.

This is the exact descent needed for the generic graph section:
`F = GraphParamField m`,
`L = AlgebraicClosure F`. -/
theorem allProperFactorCertificates_of_map_irreducible
    (F L : Type*) [Field F] [Field L]
    [Algebra F L] [IsAlgClosed L]
    (n d : ℕ)
    (P : Poly F n)
    (hPdeg : P.totalDegree ≤ d)
    (hPI :
      Irreducible
        (MvPolynomial.map (algebraMap F L) P)) :
    AllProperFactorCertificates F n d P := by
  intro c
  have hmapDeg :
      (MvPolynomial.map (algebraMap F L) P).totalDegree ≤ d := by
    exact
      (totalDegree_map_le'
        (algebraMap F L) P).trans hPdeg
  have hcertL :
      HasProperFactorCertificate
        L n c.left c.right d
        (MvPolynomial.map (algebraMap F L) P)
        c.leftMonomial c.rightMonomial :=
    hasProperFactorCertificate_of_irreducible
      L n c.left c.right d
      c.sum_le
      (MvPolynomial.map (algebraMap F L) P)
      hmapDeg hPI
      c.leftMonomial c.rightMonomial
  exact
    hasProperFactorCertificate_of_map_certificate
      F L n c.left c.right d P
      c.leftMonomial c.rightMonomial
      hcertL

/-- Specialization to the generic graph situation.

Thus `GenericGraphAbsoluteIrreducibility` already implies that *all finite
proper-factor Nullstellensatz identities exist over the rational parameter
field itself*, not merely over its algebraic closure. -/
theorem genericGraph_allProperFactorCertificates
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f) :
    AllProperFactorCertificates
      (GraphParamField m)
      m
      f.totalDegree
      (genericGraphSection f) := by
  have hAbs :
      Irreducible
        (MvPolynomial.map
          (algebraMap
            (GraphParamField m)
            (AlgebraicClosure
              (GraphParamField m)))
          (genericGraphSection f)) :=
    habs hm f hf
  exact
    allProperFactorCertificates_of_map_irreducible
      (GraphParamField m)
      (AlgebraicClosure (GraphParamField m))
      m f.totalDegree
      (genericGraphSection f)
      (totalDegree_genericGraphSection_le f)
      hAbs

/-!
Stage-30 audit
--------------

A previously hidden descent issue is now isolated and algebraically solved.

From `GenericGraphAbsoluteIrreducibility`, Stage 28 first gives chart-level
Nullstellensatz identities over
`AlgebraicClosure (GraphParamField m)`.
Stage 30 then descends every such identity to `GraphParamField m` by an
explicit coefficientwise `F`-linear retraction.

No faithfully-flat theorem, ideal contraction theorem, or new hypothesis is
used.

What remains between `GenericGraphAbsoluteIrreducibility` and
`ComplexBertiniCore` is now only **denominator clearing plus specialization**:
the certificate coefficients live in the fraction field
`Frac(ℂ[A])`; clear the finitely many denominators, multiply the resulting
nonzero parameter polynomials over the finite chart index, and specialize.

That is formal commutative algebra, not another Bertini theorem.
-/



/-! ## Stage 31: an integral model of the generic graph section

The generic graph section from Stage 29 has coefficients in the fraction
field `GraphParamField m`.  In fact no denominator occurs in the section
itself: its coefficients are polynomials in the graph parameters.

We now construct the canonical integral model
\[
  P_R(A;X)
  =
  f(X_0,\ldots,X_{m-1},\sum_j A_jX_j)
  \in \mathbb C[A_0,\ldots,A_{m-1}][X_0,\ldots,X_{m-1}]
\]
and prove that extending its coefficient ring from
`GraphParamRing m` to `GraphParamField m` gives exactly
`genericGraphSection f`.

This is the bridge required for denominator clearing.
-/

/-- Embed complex coefficients into the polynomial ring in graph parameters. -/
noncomputable def complexToGraphParamRing
    (m : ℕ) :
    ℂ →+* GraphParamRing m :=
  MvPolynomial.C

/-- Regard the original polynomial as a polynomial whose coefficient ring is
the graph-parameter ring. -/
noncomputable def toGraphParamRing
    {m n : ℕ}
    (f : Poly ℂ n) :
    Poly (GraphParamRing m) n :=
  MvPolynomial.map
    (complexToGraphParamRing m) f

/-- The parameter-polynomial coordinates `A_j` in the integral coefficient
ring. -/
noncomputable def integralGraphParam
    {m : ℕ} (j : Fin m) :
    GraphParamRing m :=
  MvPolynomial.X j

/-- Integral model of the generic graph section. -/
noncomputable def integralGenericGraphSection
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    Poly (GraphParamRing m) m :=
  graphRestrict
    (toGraphParamRing (m := m) f)
    integralGraphParam

@[simp] lemma algebraMap_integralGraphParam
    {m : ℕ} (j : Fin m) :
    (algebraMap
        (GraphParamRing m)
        (GraphParamField m))
      (integralGraphParam j) =
    genericGraphParam j := by
  rfl

/-- The two coefficient embeddings `ℂ → GraphParamField m` agree: either map
directly, or first regard a scalar as a constant parameter polynomial. -/
lemma algebraMap_complex_via_graphParamRing
    {m : ℕ} (z : ℂ) :
    (algebraMap
        (GraphParamRing m)
        (GraphParamField m))
      ((complexToGraphParamRing m) z) =
    (complexToGraphParamField m) z := by
  simpa [complexToGraphParamRing,
    complexToGraphParamField,
    GraphParamRing, GraphParamField] using
    (IsScalarTower.algebraMap_apply
      ℂ (GraphParamRing m)
      (GraphParamField m) z).symm

/-- Coefficient extension of the ambient polynomial through the parameter
ring equals direct extension to the parameter function field. -/
lemma map_toGraphParamRing_eq_toGraphParamField
    {m n : ℕ}
    (f : Poly ℂ n) :
    MvPolynomial.map
        (algebraMap
          (GraphParamRing m)
          (GraphParamField m))
        (toGraphParamRing (m := m) f) =
      toGraphParamField (m := m) f := by
  unfold toGraphParamRing toGraphParamField
  rw [MvPolynomial.map_map]
  congr 1

/-- **Base-change identity for the generic graph section.**

The rational-function-field generic member is literally the scalar extension
of the integral universal graph member. -/
theorem map_integralGenericGraphSection
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    MvPolynomial.map
        (algebraMap
          (GraphParamRing m)
          (GraphParamField m))
        (integralGenericGraphSection f) =
      genericGraphSection f := by
  unfold integralGenericGraphSection genericGraphSection
  rw [map_graphRestrict]
  rw [map_toGraphParamRing_eq_toGraphParamField]
  congr 1

/-- The integral model has the same elementary total-degree bound. -/
lemma totalDegree_integralGenericGraphSection_le
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    (integralGenericGraphSection f).totalDegree ≤
      f.totalDegree := by
  unfold integralGenericGraphSection
  have hmap :
      (toGraphParamRing (m := m) f).totalDegree ≤
        f.totalDegree :=
    totalDegree_map_le' _ _
  have hrest :
      (graphRestrict
        (toGraphParamRing (m := m) f)
        integralGraphParam).totalDegree ≤
      (toGraphParamRing (m := m) f).totalDegree := by
    exact
      restrictLinear_totalDegree_le
        (toGraphParamRing (m := m) f)
        (graphFrame integralGraphParam)
  exact hrest.trans hmap

/-- A coefficient of the integral model maps to the corresponding coefficient
of the generic function-field section. -/
lemma algebraMap_coeff_integralGenericGraphSection
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (d : Fin m →₀ ℕ) :
    (algebraMap
        (GraphParamRing m)
        (GraphParamField m))
      ((integralGenericGraphSection f).coeff d) =
    (genericGraphSection f).coeff d := by
  have h :=
    congrArg
      (fun p : Poly (GraphParamField m) m =>
        p.coeff d)
      (map_integralGenericGraphSection f)
  simpa [MvPolynomial.coeff_map] using h

/-!
Stage-31 audit
--------------

The generic graph section now has a denominator-free integral model

    `integralGenericGraphSection f`
      : `ℂ[A][X]`.

Its scalar extension to `Frac(ℂ[A])` is exactly
`genericGraphSection f`.

This removes another possible hidden gap: the target coefficients in all
proper-factor equations really originate in the parameter polynomial ring.

The next stage can therefore formulate every proper-factor equation over
`GraphParamRing m`, map it to the function field, use the Stage-30
certificate there, and clear one common denominator from the finite family
of coefficient-polynomial multipliers.
-/



/-! ## Stage 32: clear one common denominator from a finite certificate

Mathlib proves that polynomial rings commute with localization:
if `S` is a localization of `R` at `M`, then
`MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the image of
`M` under the constant-polynomial embedding.

We exploit this directly.  A finite family of certificate multipliers
`H_i ∈ S[Y]` therefore admits one common denominator which is itself a
constant polynomial in the auxiliary factor variables.  Multiplying the
Nullstellensatz identity by this denominator produces an identity over
`R[Y]` whose right-hand side is a nonzero constant polynomial `C Δ`.

This is the precise algebraic object required for specialization.
-/

/-- Clear a common denominator from a finite polynomial linear-combination
certificate over a localization.

The returned `Δ : R` lies in the localization submonoid `M`, hence is the
nonzero denominator parameter. -/
theorem clear_denominators_linearCombination_one
    (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S]
    (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R)
    [IsLocalization M S]
    {σ τ : Type*}
    [DecidableEq σ] [Fintype τ]
    (E : τ → MvPolynomial σ R)
    (hcert :
      ∃ H : τ → MvPolynomial σ S,
        ∑ i : τ,
          H i *
            MvPolynomial.map (algebraMap R S) (E i) =
        1) :
    ∃ Δ : R,
      Δ ∈ M ∧
      Δ ≠ 0 ∧
      ∃ K : τ → MvPolynomial σ R,
        ∑ i : τ, K i * E i =
          MvPolynomial.C Δ := by
  classical
  rcases hcert with ⟨H, hH⟩

  letI :
      Algebra (MvPolynomial σ R)
        (MvPolynomial σ S) :=
    MvPolynomial.algebraMvPolynomial

  let N : Submonoid (MvPolynomial σ R) :=
    Submonoid.map MvPolynomial.C M

  letI :
      IsLocalization N (MvPolynomial σ S) :=
    MvPolynomial.isLocalization M S

  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      N H

  have hbmem :
      (b : MvPolynomial σ R) ∈
        Submonoid.map MvPolynomial.C M :=
    b.property

  rcases hbmem with
    ⟨Δ, hΔM, hCΔ⟩

  have hΔ0 : Δ ≠ 0 :=
    nonZeroDivisors.ne_zero (hM hΔM)

  have hN :
      N ≤ nonZeroDivisors (MvPolynomial σ R) := by
    rintro p ⟨r, hrM, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro hCr
    apply nonZeroDivisors.ne_zero (hM hrM)
    exact (MvPolynomial.C_injective σ R) hCr

  have hKi :
      ∀ i : τ,
        ∃ Ki : MvPolynomial σ R,
          algebraMap
              (MvPolynomial σ R)
              (MvPolynomial σ S) Ki =
            (b : MvPolynomial σ R) • H i := by
    intro i
    have hi := hb i
    unfold IsLocalization.IsInteger at hi
    rw [RingHom.mem_rangeS] at hi
    exact hi

  choose K hK using hKi

  refine ⟨Δ, hΔM, hΔ0, K, ?_⟩

  apply
    (IsLocalization.injective
      (MvPolynomial σ S) hN)

  rw [map_sum]
  simp_rw [map_mul]
  simp_rw [MvPolynomial.algebraMap_def]
  simp_rw [hK]

  have hscaled :
      ∑ i : τ,
          ((b : MvPolynomial σ R) • H i) *
            MvPolynomial.map (algebraMap R S) (E i)
        =
      (b : MvPolynomial σ R) •
        (∑ i : τ,
          H i *
            MvPolynomial.map (algebraMap R S) (E i)) := by
    simp [smul_mul_assoc, Finset.smul_sum]

  rw [hscaled, hH, smul_one]

  change
    (algebraMap
      (MvPolynomial σ R)
      (MvPolynomial σ S))
      (MvPolynomial.C Δ) =
    algebraMap
      (MvPolynomial σ R)
      (MvPolynomial σ S)
      (MvPolynomial.C Δ)

  rfl

/-- Fraction-ring specialization of the preceding theorem.

Here the denominator submonoid is exactly the nonzero divisors of the base
domain, so the returned denominator is automatically nonzero. -/
theorem clear_denominators_fractionRing_certificate
    (R : Type*) [CommRing R] [IsDomain R]
    {σ τ : Type*}
    [DecidableEq σ] [Fintype τ]
    (E : τ → MvPolynomial σ (FractionRing R))
    (E0 : τ → MvPolynomial σ R)
    (hE :
      ∀ i : τ,
        E i =
          MvPolynomial.map
            (algebraMap R (FractionRing R))
            (E0 i))
    (hcert :
      ∃ H : τ → MvPolynomial σ (FractionRing R),
        ∑ i : τ, H i * E i = 1) :
    ∃ Δ : R,
      Δ ≠ 0 ∧
      ∃ K : τ → MvPolynomial σ R,
        ∑ i : τ, K i * E0 i =
          MvPolynomial.C Δ := by
  have hcert' :
      ∃ H : τ → MvPolynomial σ (FractionRing R),
        ∑ i : τ,
          H i *
            MvPolynomial.map
              (algebraMap R (FractionRing R))
              (E0 i) =
        1 := by
    rcases hcert with ⟨H, hH⟩
    refine ⟨H, ?_⟩
    simpa only [← hE] using hH

  obtain ⟨Δ, hΔM, hΔ0, K, hK⟩ :=
    clear_denominators_linearCombination_one
      R (FractionRing R)
      (nonZeroDivisors R)
      le_rfl E0 hcert'

  exact ⟨Δ, hΔ0, K, hK⟩

/-!
Stage-32 audit
--------------

A finite Nullstellensatz identity over a fraction field can now be converted
into a polynomial identity over the base domain

    `∑ K_i E_i = C Δ`

with `Δ ≠ 0`.

Because the localization of a multivariate polynomial ring is handled
directly by Mathlib, no hand-written coefficient denominator bookkeeping is
required.

For the Problem 20.1 application:
* `R = GraphParamRing m = ℂ[A]`;
* `S = GraphParamField m = Frac(R)`;
* auxiliary variables are the proper-factor coefficient variables;
* the equations `E_i` are formed from the integral generic graph section.

The only remaining algebra before `ComplexBertiniCore` is:
1. instantiate this theorem chart-by-chart;
2. evaluate the parameter coefficients at `a : ℂ^m`;
3. show `Δ(a) ≠ 0` excludes a common zero in that chart;
4. take the finite product over all charts and include one positive-degree
   target coefficient to prevent specialization to a unit.

No further field-extension descent remains.
-/



/-! ## Stage 33: specialize an integral chart certificate

Stage 32 produces, for each proper-factor chart, an identity over the parameter
ring
\[
  \sum_e K_e(A,Y) E_e(A,Y)=C(\Delta(A)).
\]
At a parameter `a` where `Δ(a) ≠ 0`, apply the coefficient ring homomorphism
`MvPolynomial.eval a : ℂ[A] →+* ℂ` and divide by the nonzero scalar `Δ(a)`.
The resulting identity has right-hand side `1`, so the specialized chart has
empty zero locus.

We first prove that specialization of the integral generic graph section is
exactly the original graph restriction.
-/

/-- Evaluating parameter coefficients of the integral ambient polynomial
recovers the original complex polynomial. -/
lemma map_toGraphParamRing_eval
    {m n : ℕ}
    (f : Poly ℂ n)
    (a : Fin m → ℂ) :
    MvPolynomial.map
        (MvPolynomial.eval a)
        (toGraphParamRing (m := m) f) =
      f := by
  unfold toGraphParamRing
  rw [MvPolynomial.map_map]
  have hcomp :
      (MvPolynomial.eval a).comp
          (complexToGraphParamRing m) =
        RingHom.id ℂ := by
    ext z
    simp [complexToGraphParamRing]
  rw [hcomp]
  simp

/-- Parameter specialization of the integral generic graph section is exactly
the concrete graph section. -/
theorem map_integralGenericGraphSection_eval
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (a : Fin m → ℂ) :
    MvPolynomial.map
        (MvPolynomial.eval a)
        (integralGenericGraphSection f) =
      graphRestrict f a := by
  unfold integralGenericGraphSection
  rw [map_graphRestrict]
  rw [map_toGraphParamRing_eval]
  congr 1
  funext j
  simp [integralGraphParam]

/-- One finite chart of the generic family has a denominator-cleared
certificate over the graph-parameter polynomial ring, assuming generic
absolute irreducibility. -/
theorem genericGraph_integral_chart_certificate
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f)
    (c : ProperFactorChartIndex m f.totalDegree) :
    ∃ Δ : GraphParamRing m,
      Δ ≠ 0 ∧
      ∃ K :
          ProperFactorEquationIndex m f.totalDegree →
            MvPolynomial
              (ProperFactorCoeffVar
                m c.left c.right)
              (GraphParamRing m),
        ∑ e : ProperFactorEquationIndex
              m f.totalDegree,
          K e *
            properFactorEquation
              (GraphParamRing m)
              m c.left c.right f.totalDegree
              (integralGenericGraphSection f)
              c.leftMonomial c.rightMonomial e
          =
        MvPolynomial.C Δ := by
  have hAll :=
    genericGraph_allProperFactorCertificates
      habs hm f hf
  have hcertF :
      HasProperFactorCertificate
        (GraphParamField m)
        m c.left c.right f.totalDegree
        (genericGraphSection f)
        c.leftMonomial c.rightMonomial :=
    hAll c
  rcases hcertF with ⟨H, hH⟩

  let E0 :
      ProperFactorEquationIndex m f.totalDegree →
        MvPolynomial
          (ProperFactorCoeffVar
            m c.left c.right)
          (GraphParamRing m) :=
    properFactorEquation
      (GraphParamRing m)
      m c.left c.right f.totalDegree
      (integralGenericGraphSection f)
      c.leftMonomial c.rightMonomial

  have hcertMapped :
      ∃ H0 :
          ProperFactorEquationIndex m f.totalDegree →
            MvPolynomial
              (ProperFactorCoeffVar
                m c.left c.right)
              (GraphParamField m),
        ∑ e : ProperFactorEquationIndex
              m f.totalDegree,
          H0 e *
            MvPolynomial.map
              (algebraMap
                (GraphParamRing m)
                (GraphParamField m))
              (E0 e)
          =
        1 := by
    refine ⟨H, ?_⟩
    dsimp [E0]
    simpa only
      [map_properFactorEquation,
       map_integralGenericGraphSection]
      using hH

  obtain ⟨Δ, hΔM, hΔ0, K, hK⟩ :=
    clear_denominators_linearCombination_one
      (GraphParamRing m)
      (GraphParamField m)
      (nonZeroDivisors (GraphParamRing m))
      le_rfl E0 hcertMapped

  exact ⟨Δ, hΔ0, K, by simpa [E0] using hK⟩

/-- Mapping a proper-factor equation through parameter evaluation gives the
proper-factor equation of the specialized graph section. -/
lemma map_integral_properFactorEquation_eval
    {m r s d : ℕ}
    (f : Poly ℂ (m + 1))
    (a : Fin m → ℂ)
    (α : PositiveDegreeMonomial m r)
    (β : PositiveDegreeMonomial m s)
    (e : ProperFactorEquationIndex m d) :
    MvPolynomial.map
        (MvPolynomial.eval a)
        (properFactorEquation
          (GraphParamRing m)
          m r s d
          (integralGenericGraphSection f)
          α β e)
      =
    properFactorEquation
      ℂ m r s d
      (graphRestrict f a)
      α β e := by
  rw [map_properFactorEquation]
  rw [map_integralGenericGraphSection_eval]

/-- **Specialization exclusion lemma.**

A denominator-cleared integral chart certificate excludes a specialized
proper factorization at every parameter where its denominator polynomial does
not vanish. -/
theorem zeroLocus_specialized_properFactorChart_eq_empty
    {m r s d : ℕ}
    (f : Poly ℂ (m + 1))
    (a : Fin m → ℂ)
    (α : PositiveDegreeMonomial m r)
    (β : PositiveDegreeMonomial m s)
    (Δ : GraphParamRing m)
    (K :
      ProperFactorEquationIndex m d →
        MvPolynomial
          (ProperFactorCoeffVar m r s)
          (GraphParamRing m))
    (hK :
      ∑ e : ProperFactorEquationIndex m d,
        K e *
          properFactorEquation
            (GraphParamRing m)
            m r s d
            (integralGenericGraphSection f)
            α β e
        =
      MvPolynomial.C Δ)
    (hΔa :
      MvPolynomial.eval a Δ ≠ 0) :
    MvPolynomial.zeroLocus ℂ
        (properFactorEquationIdeal
          ℂ m r s d
          (graphRestrict f a)
          α β)
      =
    ∅ := by
  let δ : ℂ := MvPolynomial.eval a Δ
  have hδ : δ ≠ 0 := by
    simpa [δ] using hΔa

  let H :
      ProperFactorEquationIndex m d →
        MvPolynomial
          (ProperFactorCoeffVar m r s) ℂ :=
    fun e =>
      MvPolynomial.C δ⁻¹ *
        MvPolynomial.map
          (MvPolynomial.eval a)
          (K e)

  have hMapped :=
    congrArg
      (MvPolynomial.map
        (MvPolynomial.eval a))
      hK

  have hMapped' :
      ∑ e : ProperFactorEquationIndex m d,
        MvPolynomial.map
            (MvPolynomial.eval a) (K e) *
          properFactorEquation
            ℂ m r s d
            (graphRestrict f a)
            α β e
        =
      MvPolynomial.C δ := by
    simpa only
      [map_sum, map_mul,
       map_integral_properFactorEquation_eval,
       MvPolynomial.map_C, δ]
      using hMapped

  have hOne :
      ∑ e : ProperFactorEquationIndex m d,
        H e *
          properFactorEquation
            ℂ m r s d
            (graphRestrict f a)
            α β e
        =
      1 := by
    unfold H
    calc
      ∑ e : ProperFactorEquationIndex m d,
          (MvPolynomial.C δ⁻¹ *
              MvPolynomial.map
                (MvPolynomial.eval a) (K e)) *
            properFactorEquation
              ℂ m r s d
              (graphRestrict f a)
              α β e
          =
        MvPolynomial.C δ⁻¹ *
          (∑ e : ProperFactorEquationIndex m d,
            MvPolynomial.map
                (MvPolynomial.eval a) (K e) *
              properFactorEquation
                ℂ m r s d
                (graphRestrict f a)
                α β e) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          simp only [mul_assoc]
      _ =
        MvPolynomial.C δ⁻¹ *
          MvPolynomial.C δ := by
          rw [hMapped']
      _ = 1 := by
          rw [← MvPolynomial.C_mul]
          simp [hδ]

  exact
    zeroLocus_span_range_eq_empty_of_linearCombination_one
      (properFactorEquation
        ℂ m r s d
        (graphRestrict f a)
        α β)
      H hOne

/-- Convenient chart-specialization form of
`genericGraph_integral_chart_certificate`. -/
theorem genericGraph_chart_excluded_off_denominator
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f)
    (c : ProperFactorChartIndex m f.totalDegree) :
    ∃ Δ : GraphParamRing m,
      Δ ≠ 0 ∧
      ∀ a : Fin m → ℂ,
        MvPolynomial.eval a Δ ≠ 0 →
        MvPolynomial.zeroLocus ℂ
          (properFactorEquationIdeal
            ℂ m c.left c.right f.totalDegree
            (graphRestrict f a)
            c.leftMonomial c.rightMonomial)
        =
        ∅ := by
  obtain ⟨Δ, hΔ0, K, hK⟩ :=
    genericGraph_integral_chart_certificate
      habs hm f hf c
  refine ⟨Δ, hΔ0, ?_⟩
  intro a hΔa
  exact
    zeroLocus_specialized_properFactorChart_eq_empty
      f a c.leftMonomial c.rightMonomial
      Δ K hK hΔa

/-!
Stage-33 audit
--------------

The function-field certificates are now connected to actual numerical graph
parameters.

For every finite proper-factor chart, generic absolute irreducibility yields a
nonzero parameter polynomial `Δ_c(A)` such that

    `Δ_c(a) ≠ 0`

forces the specialized chart to have empty zero locus.

Thus each individual reducibility chart is excluded on an explicit principal
open subset of parameter space.

The remaining finite algebra is:
* choose these `Δ_c` simultaneously over the finite chart type;
* choose one nonzero positive-degree coefficient of the generic section to
  prevent specialization to a unit;
* multiply all these finitely many nonzero parameter polynomials.

That product will be the certificate required by `ComplexBertiniCore`.
-/



/-! ## Stage 34: finite product certificate and
`GenericGraphAbsoluteIrreducibility → ComplexBertiniCore`

We now combine all chart denominators.

There is one additional condition which must be included: a specialization
could in principle become a constant unit.  Proper-factor charts do not detect
units.  Since the generic section is irreducible, it is nonzero and nonunit;
therefore it has a nonzero coefficient at a positive-degree monomial.
The corresponding coefficient of the integral model is a nonzero parameter
polynomial `Δ₀`.  Requiring `Δ₀(a) ≠ 0` guarantees that the specialized graph
section is still nonzero and nonunit.

Multiply `Δ₀` by the finitely many chart denominator polynomials.  Off the
zero locus of this single product:
* the section is nonzero and nonunit;
* every possible proper-factor chart has empty zero locus;
hence the section is irreducible.

This proves the entire certificate core from the single generic absolute
irreducibility statement.
-/

/-- Generic absolute irreducibility supplies a nonzero positive-degree
coefficient of the generic graph section.  We extract it after passing to the
algebraic closure and then reflect coefficient nonvanishing through the
injective scalar map. -/
theorem exists_genericGraph_positive_coeff
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f) :
    ∃ α : PositiveDegreeMonomial m f.totalDegree,
      (genericGraphSection f).coeff α.1.1 ≠ 0 := by
  let F := GraphParamField m
  let L := AlgebraicClosure F
  let g : Poly F m := genericGraphSection f
  let gL : Poly L m :=
    MvPolynomial.map (algebraMap F L) g
  have hI : Irreducible gL := by
    simpa [F, L, g, gL] using habs hm f hf
  have hdeg :
      gL.totalDegree ≤ f.totalDegree := by
    exact
      le_trans
        (totalDegree_map_le' (algebraMap F L) g)
        (totalDegree_genericGraphSection_le f)
  obtain ⟨α, hα⟩ :=
    exists_positiveDegreeMonomial_coeff_ne_zero
      hI.ne_zero hI.not_isUnit hdeg
  refine ⟨α, ?_⟩
  intro hzero
  apply hα
  simp [gL, g, MvPolynomial.coeff_map, hzero]

/-- The matching coefficient of the integral model is a nonzero polynomial in
the graph parameters. -/
theorem exists_integralGenericGraph_positive_coeff
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f) :
    ∃ α : PositiveDegreeMonomial m f.totalDegree,
      (integralGenericGraphSection f).coeff α.1.1 ≠ 0 := by
  obtain ⟨α, hα⟩ :=
    exists_genericGraph_positive_coeff
      habs hm f hf
  refine ⟨α, ?_⟩
  intro hzero
  apply hα
  rw [← algebraMap_coeff_integralGenericGraphSection
        f α.1.1]
  rw [hzero]
  simp

/-- **Main certificate theorem from generic absolute irreducibility.** -/
theorem hasGraphIrreducibilityCertificate_of_genericAbsolute
    (habs : GenericGraphAbsoluteIrreducibility)
    {m : ℕ} (hm : 3 ≤ m)
    (f : Poly ℂ (m + 1))
    (hf : Irreducible f) :
    HasGraphIrreducibilityCertificate ℂ f := by
  classical

  obtain ⟨α0, hα0⟩ :=
    exists_integralGenericGraph_positive_coeff
      habs hm f hf

  let Δ0 : GraphParamRing m :=
    (integralGenericGraphSection f).coeff α0.1.1

  have hΔ0 : Δ0 ≠ 0 := by
    simpa [Δ0] using hα0

  let chartData :
      ∀ c : ProperFactorChartIndex m f.totalDegree,
        { Δ : GraphParamRing m //
          Δ ≠ 0 ∧
          ∀ a : Fin m → ℂ,
            MvPolynomial.eval a Δ ≠ 0 →
            MvPolynomial.zeroLocus ℂ
              (properFactorEquationIdeal
                ℂ m c.left c.right f.totalDegree
                (graphRestrict f a)
                c.leftMonomial c.rightMonomial)
              = ∅ } :=
    fun c =>
      ⟨Classical.choose
          (genericGraph_chart_excluded_off_denominator
            habs hm f hf c),
       (Classical.choose_spec
          (genericGraph_chart_excluded_off_denominator
            habs hm f hf c)).1,
       (Classical.choose_spec
          (genericGraph_chart_excluded_off_denominator
            habs hm f hf c)).2⟩

  let chartDenom :
      ProperFactorChartIndex m f.totalDegree →
        GraphParamRing m :=
    fun c => (chartData c).1

  have hchartDenom0 :
      ∀ c : ProperFactorChartIndex m f.totalDegree,
        chartDenom c ≠ 0 := by
    intro c
    exact (chartData c).2.1

  let Δ : GraphParamRing m :=
    Δ0 *
      ∏ c : ProperFactorChartIndex m f.totalDegree,
        chartDenom c

  have hprod0 :
      (∏ c : ProperFactorChartIndex m f.totalDegree,
        chartDenom c) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro c hc
      exact hchartDenom0 c)

  have hΔ : Δ ≠ 0 := by
    exact mul_ne_zero hΔ0 hprod0

  refine ⟨Δ, hΔ, ?_⟩
  intro a hΔa

  have hΔ0a :
      MvPolynomial.eval a Δ0 ≠ 0 := by
    intro hzero
    apply hΔa
    simp [Δ, hzero]

  have hchartA :
      ∀ c : ProperFactorChartIndex m f.totalDegree,
        MvPolynomial.eval a (chartDenom c) ≠ 0 := by
    intro c hzero
    apply hΔa
    dsimp [Δ]
    rw [map_mul, map_prod]
    have hprodEval :
        (∏ x : ProperFactorChartIndex m f.totalDegree,
          MvPolynomial.eval a (chartDenom x)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ c) hzero
    rw [hprodEval, mul_zero]

  let P : Poly ℂ m := graphRestrict f a

  have hPdeg :
      P.totalDegree ≤ f.totalDegree := by
    have hmapdeg :=
      totalDegree_map_le'
        (MvPolynomial.eval a)
        (integralGenericGraphSection f)
    rw [map_integralGenericGraphSection_eval] at hmapdeg
    exact
      hmapdeg.trans
        (totalDegree_integralGenericGraphSection_le f)

  have hcoeffP :
      P.coeff α0.1.1 =
        MvPolynomial.eval a Δ0 := by
    have h :=
      congrArg
        (fun q : Poly ℂ m =>
          q.coeff α0.1.1)
        (map_integralGenericGraphSection_eval f a)
    simpa [P, Δ0, MvPolynomial.coeff_map] using h.symm

  have hcoeffP0 :
      P.coeff α0.1.1 ≠ 0 := by
    rw [hcoeffP]
    exact hΔ0a

  have hP0 : P ≠ 0 := by
    intro hzero
    apply hcoeffP0
    rw [hzero]
    simp

  have hPU : ¬ IsUnit P :=
    not_isUnit_of_positiveDegree_coeff_ne_zero
      α0.2 hcoeffP0

  by_contra hPI

  obtain
      ⟨r, s, hrs, α, β, x, hx⟩ :=
    reducible_gives_properFactor_chart
      hP0 hPU hPI hPdeg

  have hr : 1 ≤ r := by
    exact le_trans α.2 α.1.2

  have hs : 1 ≤ s := by
    exact le_trans β.2 β.1.2

  let rs : PositiveDegreeSplit f.totalDegree :=
    mkPositiveDegreeSplit hr hs hrs

  let c : ProperFactorChartIndex
      m f.totalDegree :=
    ⟨rs,
      (by simpa [rs] using α),
      (by simpa [rs] using β)⟩

  have hcEmpty :
      MvPolynomial.zeroLocus ℂ
        (properFactorEquationIdeal
          ℂ m c.left c.right f.totalDegree
          (graphRestrict f a)
          c.leftMonomial c.rightMonomial)
        =
      ∅ := by
    exact
      (chartData c).2.2 a
        (hchartA c)

  have hx' :
      x ∈
        MvPolynomial.zeroLocus ℂ
          (properFactorEquationIdeal
            ℂ m c.left c.right f.totalDegree
            (graphRestrict f a)
            c.leftMonomial c.rightMonomial) := by
    simpa only [P, c, rs,
      ProperFactorChartIndex.left,
      ProperFactorChartIndex.right,
      ProperFactorChartIndex.leftMonomial,
      ProperFactorChartIndex.rightMonomial]
      using hx

  rw [hcEmpty] at hx'
  exact hx'

/-- The complete complex certificate core follows from the single generic
absolute irreducibility theorem. -/
theorem complexBertiniCore_of_genericGraphAbsoluteIrreducibility
    (habs : GenericGraphAbsoluteIrreducibility) :
    ComplexBertiniCore := by
  intro m hm f hf
  exact
    hasGraphIrreducibilityCertificate_of_genericAbsolute
      habs hm f hf

/-- Consequently the complete exact real result follows from the same single
generic theorem. -/
theorem exact_sequence_real_of_genericGraphAbsoluteIrreducibility
    (habs : GenericGraphAbsoluteIrreducibility) :
    LeastUniversalDetection ℝ 1 1 ∧
    LeastUniversalDetection ℝ 2 2 ∧
    ∀ n, 3 ≤ n →
      LeastUniversalDetection ℝ n 3 := by
  exact
    exact_sequence_real_of_core
      (complexBertiniCore_of_genericGraphAbsoluteIrreducibility
        habs)

/-- And likewise over the complexes. -/
theorem exact_sequence_complex_of_genericGraphAbsoluteIrreducibility
    (habs : GenericGraphAbsoluteIrreducibility) :
    LeastUniversalDetection ℂ 1 1 ∧
    LeastUniversalDetection ℂ 2 2 ∧
    ∀ n, 3 ≤ n →
      LeastUniversalDetection ℂ n 3 := by
  exact
    exact_sequence_complex_of_core
      (complexBertiniCore_of_genericGraphAbsoluteIrreducibility
        habs)

/-!
Stage-34 audit
--------------

This stage closes the entire elimination/specialization side.

We now have a formal implication

    GenericGraphAbsoluteIrreducibility
      → ComplexBertiniCore
      → exact Problem 20.1 over both `ℂ` and `ℝ`.

The finite product certificate explicitly handles:
* every positive factor-degree split, including degree drops;
* every normalization chart;
* all chart denominator polynomials;
* the separate possibility that the specialized target becomes a unit.

Therefore **there is now exactly one remaining mathematical theorem**:

    `GenericGraphAbsoluteIrreducibility`.

No Nullstellensatz descent, denominator clearing, specialization openness,
real descent, or finite-cover claim remains as an independent hypothesis.
-/



/-! ## Stage 35: algebraically independent coordinates on the hypersurface

We now enter the remaining Bertini theorem itself.

Let
    `f : ℂ[X₀,...,X_m]`
be irreducible, and choose a variable `X_i` which actually occurs in `f`.
The coordinate ring of the hypersurface is

    `A_f = ℂ[X₀,...,X_m] / (f)`.

The other `m` coordinate functions are algebraically independent in `A_f`.

This is proved purely algebraically.  If a nonzero polynomial `p` in the
other coordinates vanished in `A_f`, then `f` would divide the renamed
polynomial.  But the renamed polynomial has `X_i`-degree zero, whereas every
nonzero multiple of `f` has strictly positive `X_i`-degree because
`X_i ∈ f.vars`.  This contradicts `MvPolynomial.degreeOf_mul_eq`.

This is the first internal piece of the generic-hyperplane Bertini argument;
no Bertini theorem is assumed.
-/

/-- Principal ideal defining the affine hypersurface. -/
def hypersurfaceIdeal
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :
    Ideal (Poly ℂ (m + 1)) :=
  Ideal.span {f}

/-- Affine coordinate ring of the hypersurface `f = 0`. -/
abbrev HypersurfaceCoordRing
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :=
  Poly ℂ (m + 1) ⧸ hypersurfaceIdeal f

/-- An irreducible multivariate polynomial over `ℂ` has at least one variable.

A polynomial with empty variable set is constant, and a nonzero constant over
a field is a unit. -/
lemma exists_mem_vars_of_irreducible
    {n : ℕ}
    {f : Poly ℂ n}
    (hf : Irreducible f) :
    ∃ i : Fin n, i ∈ f.vars := by
  have hvars : f.vars ≠ ∅ := by
    intro hempty
    have hfC :
        f = MvPolynomial.C (f.coeff 0) :=
      (MvPolynomial.vars_eq_empty_iff_eq_C).mp hempty
    have hc0 : f.coeff 0 ≠ 0 := by
      intro hc0
      apply hf.ne_zero
      rw [hfC, hc0]
      simp
    have hunitC :
        IsUnit
          (MvPolynomial.C (f.coeff 0) : Poly ℂ n) := by
      exact
        (IsUnit.mk0 (f.coeff 0) hc0).map
          (MvPolynomial.C : ℂ →+* Poly ℂ n)
    apply hf.not_isUnit
    rw [hfC]
    exact hunitC
  exact Finset.nonempty_iff_ne_empty.mpr hvars

/-- Renaming the `m` variables through `i.succAbove` produces a polynomial
which does not involve the omitted pivot variable `i`; hence its
`i`-degree is zero. -/
lemma degreeOf_rename_succAbove_eq_zero
    {m : ℕ}
    (i : Fin (m + 1))
    (p : Poly ℂ m) :
    MvPolynomial.degreeOf i
        ((MvPolynomial.rename i.succAbove) p) =
      0 := by
  by_contra hdeg
  have hivar :
      i ∈
        ((MvPolynomial.rename i.succAbove) p).vars :=
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).2 hdeg
  rcases
      MvPolynomial.mem_vars_rename
        i.succAbove p hivar with
    ⟨j, hj, hji⟩
  exact (Fin.succAbove_ne i j) hji

/-- The canonical algebra map from the polynomial ring in the `m` non-pivot
coordinates to the hypersurface coordinate ring. -/
noncomputable def hypersurfaceOtherCoordAlgHom
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (i : Fin (m + 1)) :
    Poly ℂ m →ₐ[ℂ] HypersurfaceCoordRing f :=
  (Ideal.Quotient.mkₐ ℂ (hypersurfaceIdeal f)).comp
    (MvPolynomial.rename i.succAbove)

/-- On variables, `hypersurfaceOtherCoordAlgHom` is exactly the quotient class
of the corresponding ambient coordinate. -/
@[simp] lemma hypersurfaceOtherCoordAlgHom_X
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (i : Fin (m + 1))
    (j : Fin m) :
    hypersurfaceOtherCoordAlgHom f i
        (MvPolynomial.X j) =
      Ideal.Quotient.mk (hypersurfaceIdeal f)
        (MvPolynomial.X (i.succAbove j)) := by
  simp [hypersurfaceOtherCoordAlgHom]

/-- If the pivot variable occurs in irreducible `f`, the polynomial ring in
all other coordinates injects into the hypersurface coordinate ring. -/
theorem hypersurfaceOtherCoordAlgHom_injective
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    {i : Fin (m + 1)}
    (hi : i ∈ f.vars) :
    Function.Injective
      (hypersurfaceOtherCoordAlgHom f i) := by
  intro p q hpq

  have hmk :
      Ideal.Quotient.mk (hypersurfaceIdeal f)
          ((MvPolynomial.rename i.succAbove) p) =
        Ideal.Quotient.mk (hypersurfaceIdeal f)
          ((MvPolynomial.rename i.succAbove) q) := by
    simpa [hypersurfaceOtherCoordAlgHom,
      Ideal.Quotient.mkₐ_eq_mk] using hpq

  have hmem0 :
      (MvPolynomial.rename i.succAbove) p -
          (MvPolynomial.rename i.succAbove) q
        ∈ hypersurfaceIdeal f :=
    (Ideal.Quotient.eq).mp hmk

  have hmem :
      (MvPolynomial.rename i.succAbove) (p - q)
        ∈ hypersurfaceIdeal f := by
    simpa using hmem0

  have hdiv :
      f ∣ (MvPolynomial.rename i.succAbove) (p - q) := by
    simpa [hypersurfaceIdeal] using
      ((Ideal.mem_span_singleton).mp hmem)

  by_contra hpqne
  have hsub0 : p - q ≠ 0 := sub_ne_zero.mpr hpqne

  have hrename0 :
      (MvPolynomial.rename i.succAbove) (p - q) ≠ 0 := by
    exact
      (MvPolynomial.rename_eq_zero_iff_of_injective
        (p - q) Fin.succAbove_right_injective).not.mpr
        hsub0

  rcases hdiv with ⟨s, hs⟩

  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hrename0
    rw [hs, hsZero, mul_zero]

  have hdegf :
      MvPolynomial.degreeOf i f ≠ 0 :=
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).1 hi

  have hdegRename :
      MvPolynomial.degreeOf i
          ((MvPolynomial.rename i.succAbove) (p - q)) =
        0 :=
    degreeOf_rename_succAbove_eq_zero i (p - q)

  have hdegMul :
      MvPolynomial.degreeOf i (f * s) =
        MvPolynomial.degreeOf i f +
          MvPolynomial.degreeOf i s :=
    MvPolynomial.degreeOf_mul_eq
      (n := i) hf.ne_zero hs0

  have hzeroSum :
      MvPolynomial.degreeOf i f +
          MvPolynomial.degreeOf i s =
        0 := by
    rw [← hdegMul, ← hs]
    exact hdegRename

  have : MvPolynomial.degreeOf i f = 0 := by
    omega
  exact hdegf this

/-- The family of the `m` non-pivot coordinate classes in the hypersurface
coordinate ring. -/
noncomputable def hypersurfaceOtherCoord
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (i : Fin (m + 1)) :
    Fin m → HypersurfaceCoordRing f :=
  fun j =>
    Ideal.Quotient.mk (hypersurfaceIdeal f)
      (MvPolynomial.X (i.succAbove j))

/-- Its evaluation algebra hom is precisely the injective map constructed
above. -/
lemma aeval_hypersurfaceOtherCoord
    {m : ℕ}
    (f : Poly ℂ (m + 1))
    (i : Fin (m + 1)) :
    MvPolynomial.aeval
        (hypersurfaceOtherCoord f i) =
      hypersurfaceOtherCoordAlgHom f i := by
  ext j
  simp [hypersurfaceOtherCoord,
    hypersurfaceOtherCoordAlgHom]

/-- **Algebraic independence of the other coordinates.**

If `X_i` genuinely occurs in irreducible `f`, the remaining `m` coordinate
classes are algebraically independent over `ℂ` in the hypersurface coordinate
ring. -/
theorem algebraicIndependent_hypersurfaceOtherCoord
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    {i : Fin (m + 1)}
    (hi : i ∈ f.vars) :
    AlgebraicIndependent ℂ
      (hypersurfaceOtherCoord f i) := by
  rw [algebraicIndependent_iff_ker_eq_bot]
  apply (RingHom.injective_iff_ker_eq_bot _).mp
  rw [aeval_hypersurfaceOtherCoord]
  exact hypersurfaceOtherCoordAlgHom_injective hf hi

/-- Every irreducible hypersurface admits a pivot for which all remaining
coordinate classes are algebraically independent. -/
theorem exists_pivot_algebraicIndependent_otherCoords
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    ∃ i : Fin (m + 1),
      i ∈ f.vars ∧
      AlgebraicIndependent ℂ
        (hypersurfaceOtherCoord f i) := by
  obtain ⟨i, hi⟩ :=
    exists_mem_vars_of_irreducible hf
  exact
    ⟨i, hi,
      algebraicIndependent_hypersurfaceOtherCoord
        hf hi⟩

/-- The principal ideal of an irreducible hypersurface is prime. -/
lemma hypersurfaceIdeal_isPrime
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    (hypersurfaceIdeal f).IsPrime := by
  unfold hypersurfaceIdeal
  exact
    (Ideal.span_singleton_prime hf.ne_zero).2
      hf.prime

/-!
Stage-35 audit
--------------

This is the first strict internal theorem from the Bertini geometry itself.

For an irreducible hypersurface `f = 0`, choose any coordinate which really
occurs in `f`.  The other `m` coordinate classes in
`ℂ[X₀,...,X_m]/(f)` are algebraically independent.

The proof is elementary:
* the omitted-variable polynomial ring maps to the quotient;
* a kernel element would say `f` divides a polynomial of pivot degree zero;
* `degreeOf_mul_eq` says every nonzero multiple of `f` has positive pivot
  degree;
* contradiction.

For `m ≥ 3`, this supplies at least three algebraically independent regular
functions on the hypersurface, which is the field-theoretic input needed in
the generic-hyperplane irreducibility argument.

No Bertini theorem, dimension theorem, transcendence-degree theorem, or
geometric irreducibility theorem is assumed here.
-/


/-! ## Stage 36: pass hypersurface coordinates to the function field -/

abbrev HypersurfaceFunctionField
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :=
  FractionRing (HypersurfaceCoordRing f)

/-- The rational parameter fraction ring over the hypersurface coordinate
function ring, stated without requiring a `Field` instance in the type.
When `f` is irreducible the local prime-ideal instance upgrades the
coefficient fraction ring, and hence this ring, to the usual rational
parameter field. -/
abbrev HypersurfaceParamField
    {m : ℕ}
    (f : Poly ℂ (m + 1)) :=
  FractionRing
    (MvPolynomial (Fin m) (HypersurfaceFunctionField f))

/-- For an irreducible hypersurface the coordinate ring is a domain, hence
its fraction ring is a genuine field.  We keep this as an explicit helper
rather than asking typeclass search to recover irreducibility from `f`. -/
noncomputable def hypersurfaceFunctionFieldField
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    Field (HypersurfaceFunctionField f) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : IsDomain (HypersurfaceCoordRing f) := inferInstance
  exact FractionRing.field (HypersurfaceCoordRing f)

noncomputable def hypersurfaceCoordToFunctionField
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    HypersurfaceCoordRing f →ₐ[ℂ]
      HypersurfaceFunctionField f := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  exact
    IsScalarTower.toAlgHom
      ℂ
      (HypersurfaceCoordRing f)
      (HypersurfaceFunctionField f)

lemma hypersurfaceCoordToFunctionField_injective
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    Function.Injective
      (hypersurfaceCoordToFunctionField hf) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  change Function.Injective
    (algebraMap
      (HypersurfaceCoordRing f)
      (HypersurfaceFunctionField f))
  exact
    IsFractionRing.injective
      (HypersurfaceCoordRing f)
      (HypersurfaceFunctionField f)

noncomputable def hypersurfaceOtherCoordInFunctionField
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (i : Fin (m + 1)) :
    Fin m → HypersurfaceFunctionField f :=
  fun j =>
    hypersurfaceCoordToFunctionField hf
      (hypersurfaceOtherCoord f i j)

theorem algebraicIndependent_hypersurfaceOtherCoordInFunctionField
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    {i : Fin (m + 1)}
    (hi : i ∈ f.vars) :
    AlgebraicIndependent ℂ
      (hypersurfaceOtherCoordInFunctionField hf i) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  have hAI :=
    algebraicIndependent_hypersurfaceOtherCoord hf hi
  have hinj :=
    hypersurfaceCoordToFunctionField_injective hf
  change AlgebraicIndependent ℂ
    (fun j =>
      hypersurfaceCoordToFunctionField hf
        (hypersurfaceOtherCoord f i j))
  exact hAI.map' hinj

theorem exists_pivot_algebraicIndependent_otherCoords_functionField
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    ∃ i : Fin (m + 1),
      i ∈ f.vars ∧
      AlgebraicIndependent ℂ
        (hypersurfaceOtherCoordInFunctionField hf i) := by
  obtain ⟨i, hi⟩ := exists_mem_vars_of_irreducible hf
  exact
    ⟨i, hi,
      algebraicIndependent_hypersurfaceOtherCoordInFunctionField
        hf hi⟩

abbrev RationalParamRing
    (K : Type*) [Field K]
    (m : ℕ) :=
  Poly K m

abbrev RationalParamField
    (K : Type*) [Field K]
    (m : ℕ) :=
  FractionRing (RationalParamRing K m)

noncomputable def rationalParamVar
    (K : Type*) [Field K]
    {m : ℕ}
    (j : Fin m) :
    RationalParamField K m :=
  algebraMap
    (RationalParamRing K m)
    (RationalParamField K m)
    (MvPolynomial.X j)

lemma aeval_rationalParamVar
    (K : Type*) [Field K]
    (m : ℕ) :
    MvPolynomial.aeval
        (rationalParamVar K :
          Fin m → RationalParamField K m)
      =
    IsScalarTower.toAlgHom
      K
      (RationalParamRing K m)
      (RationalParamField K m) := by
  ext j
  simp [rationalParamVar]

theorem algebraicIndependent_rationalParamVar
    (K : Type*) [Field K]
    (m : ℕ) :
    AlgebraicIndependent K
      (rationalParamVar K :
        Fin m → RationalParamField K m) := by
  rw [algebraicIndependent_iff_injective_aeval]
  rw [aeval_rationalParamVar]
  change Function.Injective
    (algebraMap
      (RationalParamRing K m)
      (RationalParamField K m))
  exact
    IsFractionRing.injective
      (RationalParamRing K m)
      (RationalParamField K m)

/-!
Stage-36 audit:
the hypersurface coordinates are algebraically independent in the function
field, and generic rational-function coordinates are algebraically independent
over their coefficient field.  These are exactly the two transcendence layers
needed for the Jouanolou field argument.
-/


/-! ## Stage 37: injective one-variable substitution over a domain

The remaining Jouanolou independence statement is ultimately triangular.

This stage formalizes the elementary algebra behind that statement.

For an integral domain `R`, substitution
    `p(T) ↦ p(q)`
is injective as soon as `q` is not constant.  Mathlib's
`Polynomial.comp_eq_zero_iff` makes this completely elementary.

We then package the same fact for multivariate polynomial rings indexed by
`Option σ`: the `none` variable is singled out as the polynomial variable,
while the `some σ` variables form the coefficient ring.  An injective
coefficient-ring map together with a nonconstant image of the singled-out
variable therefore gives an injective algebra homomorphism.

Finally, the images of all coordinate variables under such an injective
substitution are algebraically independent.
-/

/-- Composition by a nonconstant polynomial over a domain is injective. -/
lemma polynomial_comp_injective_of_not_constant
    {R : Type*} [CommRing R] [IsDomain R]
    {q : Polynomial R}
    (hq : q ≠ Polynomial.C (q.coeff 0)) :
    Function.Injective (Polynomial.compRingHom q) := by
  intro p r hpr
  change p.comp q = r.comp q at hpr
  have hzero :
      (p - r).comp q = 0 := by
    rw [Polynomial.sub_comp, hpr, sub_self]
  rcases (Polynomial.comp_eq_zero_iff.mp hzero) with hsub | hconst
  · exact sub_eq_zero.mp hsub
  · exact False.elim (hq hconst.2)

/-- Map coefficients injectively and then substitute a nonconstant polynomial:
the resulting polynomial homomorphism is injective. -/
lemma polynomial_map_then_comp_injective
    {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S)
    (hφ : Function.Injective φ)
    (q : Polynomial S)
    (hq : q ≠ Polynomial.C (q.coeff 0)) :
    Function.Injective
      (fun p : Polynomial R =>
        (Polynomial.map φ p).comp q) := by
  exact
    (polynomial_comp_injective_of_not_constant hq).comp
      (Polynomial.map_injective φ hφ)

/-- `eval₂` with coefficient map `C ∘ φ` is the same as coefficient mapping
followed by polynomial composition. -/
lemma polynomial_eval₂_C_comp_eq_map_comp
    {R S : Type*}
    [CommRing R] [CommRing S]
    (φ : R →+* S)
    (q : Polynomial S)
    (p : Polynomial R) :
    Polynomial.eval₂
        (Polynomial.C.comp φ) q p =
      (Polynomial.map φ p).comp q := by
  let F : Polynomial R →+* Polynomial S :=
    Polynomial.eval₂RingHom
      (Polynomial.C.comp φ) q
  let G : Polynomial R →+* Polynomial S :=
    (Polynomial.compRingHom q).comp
      (Polynomial.mapRingHom φ)
  have hFG : F = G := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [F, G]
    · simp [F, G]
  exact congrFun (congrArg DFunLike.coe hFG) p

/-- Hence the direct `eval₂` substitution is injective under the same
hypotheses. -/
lemma polynomial_eval₂_C_comp_injective
    {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S)
    (hφ : Function.Injective φ)
    (q : Polynomial S)
    (hq : q ≠ Polynomial.C (q.coeff 0)) :
    Function.Injective
      (fun p : Polynomial R =>
        Polynomial.eval₂
          (Polynomial.C.comp φ) q p) := by
  intro p r hpr
  apply
    polynomial_map_then_comp_injective
      φ hφ q hq
  simpa [polynomial_eval₂_C_comp_eq_map_comp] using hpr

/-! ### Option-variable form -/

/-- The universal one-variable substitution on a multivariate polynomial
ring indexed by `Option σ`.

* variables `some s` are sent through the coefficient map `ρ`;
* the distinguished variable `none` is sent to `q`.

The `optionEquivLeft` equivalence turns this into ordinary univariate
polynomial evaluation. -/
noncomputable def optionLinearSubstitution
    {σ τ : Type*}
    (ρ :
      MvPolynomial σ ℂ →ₐ[ℂ]
        MvPolynomial τ ℂ)
    (q : Polynomial (MvPolynomial τ ℂ)) :
    MvPolynomial (Option σ) ℂ →ₐ[ℂ]
      MvPolynomial (Option τ) ℂ :=
  (MvPolynomial.optionEquivLeft ℂ τ).symm.toAlgHom.comp
    ((Polynomial.eval₂AlgHom
      ((Polynomial.CAlgHom).comp ρ)
      q
      (fun _ => Commute.all _ _)).comp
        (MvPolynomial.optionEquivLeft ℂ σ).toAlgHom)

/-- On the distinguished variable, the option substitution gives the
polynomial `q`, transported back through `optionEquivLeft`. -/
@[simp] lemma optionLinearSubstitution_X_none
    {σ τ : Type*}
    (ρ :
      MvPolynomial σ ℂ →ₐ[ℂ]
        MvPolynomial τ ℂ)
    (q : Polynomial (MvPolynomial τ ℂ)) :
    optionLinearSubstitution ρ q
        (MvPolynomial.X none) =
      (MvPolynomial.optionEquivLeft ℂ τ).symm q := by
  simp [optionLinearSubstitution]

/-- On a coefficient variable `some s`, the substitution is just `ρ(X_s)`,
embedded into the target option-variable polynomial ring. -/
@[simp] lemma optionLinearSubstitution_X_some
    {σ τ : Type*}
    (ρ :
      MvPolynomial σ ℂ →ₐ[ℂ]
        MvPolynomial τ ℂ)
    (q : Polynomial (MvPolynomial τ ℂ))
    (s : σ) :
    optionLinearSubstitution ρ q
        (MvPolynomial.X (some s)) =
      MvPolynomial.rename some
        (ρ (MvPolynomial.X s)) := by
  change
    (MvPolynomial.optionEquivLeft ℂ τ).symm
        (Polynomial.C (ρ (MvPolynomial.X s))) =
      MvPolynomial.rename some (ρ (MvPolynomial.X s))
  simp [MvPolynomial.optionEquivLeft_symm_apply]

/-- Injectivity of the option-variable substitution. -/
theorem optionLinearSubstitution_injective
    {σ τ : Type*}
    (ρ :
      MvPolynomial σ ℂ →ₐ[ℂ]
        MvPolynomial τ ℂ)
    (hρ : Function.Injective ρ)
    (q : Polynomial (MvPolynomial τ ℂ))
    (hq : q ≠ Polynomial.C (q.coeff 0)) :
    Function.Injective
      (optionLinearSubstitution ρ q) := by
  intro p r hpr
  apply (MvPolynomial.optionEquivLeft ℂ σ).injective
  apply
    polynomial_map_then_comp_injective
      ρ.toRingHom hρ q hq
  have h :=
    congrArg
      (MvPolynomial.optionEquivLeft ℂ τ)
      hpr
  simpa [optionLinearSubstitution,
    polynomial_eval₂_C_comp_eq_map_comp] using h

/-- The coordinate images under an injective option substitution form an
algebraically independent family. -/
theorem algebraicIndependent_optionLinearSubstitution_X
    {σ τ : Type*}
    (ρ :
      MvPolynomial σ ℂ →ₐ[ℂ]
        MvPolynomial τ ℂ)
    (hρ : Function.Injective ρ)
    (q : Polynomial (MvPolynomial τ ℂ))
    (hq : q ≠ Polynomial.C (q.coeff 0)) :
    AlgebraicIndependent ℂ
      (fun o : Option σ =>
        optionLinearSubstitution ρ q
          (MvPolynomial.X o)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have hEq :
      MvPolynomial.aeval
          (fun o : Option σ =>
            optionLinearSubstitution ρ q
              (MvPolynomial.X o))
        =
      optionLinearSubstitution ρ q := by
    ext o
    simp
  rw [hEq]
  exact
    optionLinearSubstitution_injective
      ρ hρ q hq

/-!
Stage-37 audit
--------------

The key triangular algebra has now been isolated:

* composition by a nonconstant univariate polynomial is injective over a
  domain;
* this remains true after an injective coefficient extension;
* equivalently, in `MvPolynomial (Option σ)`, an injective map on the
  coefficient variables plus a nonconstant image of the distinguished
  variable gives an injective substitution;
* the substituted coordinate family is therefore algebraically independent.

This is precisely the mechanism needed for
    `ξ = Σ A_i g_i`.
After isolating one `g_i` as the distinguished variable, `ξ` is linear in
that variable with coefficient `A_i`.  Since `A_i` is a genuine polynomial
variable, the image is nonconstant.

No dimension/codimension theorem occurs here.
-/


/-! ## Stage 38: the Jouanolou mixed polynomial family is algebraically independent

Assume `m ≥ 2`.

We use the following coordinate convention.

Source variables:
* distinguished `none`       = `ξ`;
* `some (Sum.inl i)`         = `A_i`;
* `some (Sum.inr unit)`      = `δ`.

Target variables:
* distinguished `none`       = `g_0`;
* `some (Sum.inl i)`         = `A_i`;
* `some (Sum.inr j)`         = `g_{j+1}`.

Thus `δ` will become `g_1`, while
    `ξ = A_0 g_0 + Σ_j A_{j+1} g_{j+1}`.

The coefficient-variable map fixes every `A_i` and sends the single `δ`
variable to `g_1`.  The distinguished source variable is sent to the
nonconstant linear polynomial in `g_0` displayed above.

Stage 37 therefore proves that the entire source family
    `(A_i, ξ, δ)`
is algebraically independent as a family of polynomials in the independent
variables `(A_i, g_i)`.
-/

abbrev JouanolouSourceCoeffVar (m : ℕ) :=
  Sum (Fin m) PUnit

abbrev JouanolouTargetCoeffVar (m : ℕ) :=
  Sum (Fin m) (Fin (m - 1))

/-- Coefficient-variable embedding:
`A_i ↦ A_i`, `δ ↦ g_1`. -/
def jouanolouCoeffEmbed
    {m : ℕ} (hm : 2 ≤ m) :
    JouanolouSourceCoeffVar m →
      JouanolouTargetCoeffVar m
  | Sum.inl i => Sum.inl i
  | Sum.inr _ =>
      Sum.inr ⟨0, by omega⟩

lemma jouanolouCoeffEmbed_injective
    {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective
      (jouanolouCoeffEmbed hm) := by
  intro x y hxy
  rcases x with i | u
  · rcases y with j | v
    · simp [jouanolouCoeffEmbed] at hxy
      simpa [hxy]
    · simp [jouanolouCoeffEmbed] at hxy
  · rcases y with j | v
    · simp [jouanolouCoeffEmbed] at hxy
    · cases u
      cases v
      rfl

/-- Injective algebra hom on the coefficient polynomial rings. -/
noncomputable def jouanolouCoeffRename
    {m : ℕ} (hm : 2 ≤ m) :
    MvPolynomial (JouanolouSourceCoeffVar m) ℂ
      →ₐ[ℂ]
    MvPolynomial (JouanolouTargetCoeffVar m) ℂ :=
  MvPolynomial.rename (jouanolouCoeffEmbed hm)

lemma jouanolouCoeffRename_injective
    {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective
      (jouanolouCoeffRename hm) := by
  exact
    MvPolynomial.rename_injective
      (jouanolouCoeffEmbed hm)
      (jouanolouCoeffEmbed_injective hm)

/-- The parameter coefficient `A_0`. -/
noncomputable def jouanolouA0
    {m : ℕ} (hm : 2 ≤ m) :
    MvPolynomial (JouanolouTargetCoeffVar m) ℂ :=
  MvPolynomial.X
    (Sum.inl (⟨0, by omega⟩ : Fin m) : JouanolouTargetCoeffVar m)

/-- The part of `ξ` not involving `g_0`:
`Σ_{j : Fin (m-1)} A_{j+1} g_{j+1}`. -/
noncomputable def jouanolouRest
    {m : ℕ} (hm : 2 ≤ m) :
    MvPolynomial (JouanolouTargetCoeffVar m) ℂ :=
  ∑ j : Fin (m - 1),
    MvPolynomial.X
        (Sum.inl (Fin.cast (by omega) j.succ : Fin m) : JouanolouTargetCoeffVar m) *
      MvPolynomial.X
        (Sum.inr j : JouanolouTargetCoeffVar m)

/-- The linear polynomial in the distinguished target variable `g_0`
representing `ξ`. -/
noncomputable def jouanolouXiLinear
    {m : ℕ} (hm : 2 ≤ m) :
    Polynomial
      (MvPolynomial (JouanolouTargetCoeffVar m) ℂ) :=
  Polynomial.C (jouanolouA0 hm) *
      Polynomial.X +
    Polynomial.C (jouanolouRest hm)

/-- Its leading coefficient `A_0` is nonzero. -/
lemma jouanolouA0_ne_zero
    {m : ℕ} (hm : 2 ≤ m) :
    jouanolouA0 hm ≠ 0 := by
  simp [jouanolouA0]

/-- Hence the linear polynomial representing `ξ` is not constant. -/
lemma jouanolouXiLinear_not_constant
    {m : ℕ} (hm : 2 ≤ m) :
    jouanolouXiLinear hm ≠
      Polynomial.C
        ((jouanolouXiLinear hm).coeff 0) := by
  intro hconst
  have h1 :=
    congrArg (fun p :
      Polynomial
        (MvPolynomial
          (JouanolouTargetCoeffVar m) ℂ) =>
        p.coeff 1) hconst
  have ha0 : jouanolouA0 hm ≠ 0 :=
    jouanolouA0_ne_zero hm
  apply ha0
  simpa [jouanolouXiLinear] using h1

/-- The polynomial family representing the desired mixed variables. -/
noncomputable def jouanolouMixedPolynomialFamily
    {m : ℕ} (hm : 2 ≤ m) :
    Option (JouanolouSourceCoeffVar m) →
      MvPolynomial
        (Option (JouanolouTargetCoeffVar m)) ℂ :=
  fun o =>
    optionLinearSubstitution
      (jouanolouCoeffRename hm)
      (jouanolouXiLinear hm)
      (MvPolynomial.X o)

/-- **Core mixed-independence theorem, purely in a polynomial ring.** -/
theorem algebraicIndependent_jouanolouMixedPolynomialFamily
    {m : ℕ} (hm : 2 ≤ m) :
    AlgebraicIndependent ℂ
      (jouanolouMixedPolynomialFamily hm) := by
  exact
    algebraicIndependent_optionLinearSubstitution_X
      (jouanolouCoeffRename hm)
      (jouanolouCoeffRename_injective hm)
      (jouanolouXiLinear hm)
      (jouanolouXiLinear_not_constant hm)

/-- The source `A_i` variable maps to the corresponding target `A_i`. -/
lemma jouanolouMixedPolynomialFamily_A
    {m : ℕ} (hm : 2 ≤ m)
    (i : Fin m) :
    jouanolouMixedPolynomialFamily hm
        (some (Sum.inl i)) =
      MvPolynomial.X
        (some (Sum.inl i)) := by
  simp [jouanolouMixedPolynomialFamily,
    jouanolouCoeffRename,
    jouanolouCoeffEmbed]

/-- The source `δ` variable maps to target `g_1`. -/
lemma jouanolouMixedPolynomialFamily_delta
    {m : ℕ} (hm : 2 ≤ m) :
    jouanolouMixedPolynomialFamily hm
        (some (Sum.inr PUnit.unit)) =
      MvPolynomial.X
        (some
          (Sum.inr (⟨0, by omega⟩ : Fin (m - 1)) :
            JouanolouTargetCoeffVar m)) := by
  simp [jouanolouMixedPolynomialFamily,
    jouanolouCoeffRename,
    jouanolouCoeffEmbed]

/-- The distinguished source variable maps to the intended linear expression
`A_0 g_0 + Σ A_{j+1} g_{j+1}`. -/
lemma jouanolouMixedPolynomialFamily_xi
    {m : ℕ} (hm : 2 ≤ m) :
    jouanolouMixedPolynomialFamily hm none =
      MvPolynomial.X
          (some (Sum.inl (⟨0, by omega⟩ : Fin m) :
            JouanolouTargetCoeffVar m)) *
        MvPolynomial.X none +
      ∑ j : Fin (m - 1),
        MvPolynomial.X
            (some (Sum.inl (Fin.cast (by omega) j.succ : Fin m) :
              JouanolouTargetCoeffVar m)) *
          MvPolynomial.X
            (some (Sum.inr j : JouanolouTargetCoeffVar m)) := by
  apply
    (MvPolynomial.optionEquivLeft ℂ
      (JouanolouTargetCoeffVar m)).injective
  simp [jouanolouMixedPolynomialFamily,
    jouanolouXiLinear, jouanolouA0,
    jouanolouRest]

/-!
Stage-38 audit
--------------

The mixed algebraic-independence input that Stacks/Jouanolou normally obtains
from a codimension-two argument is now proved directly for our special graph
family at the polynomial level.

For `m ≥ 2`, the formal variables
    `A_0,...,A_{m-1}, ξ, δ`
with
    `ξ = Σ A_i g_i`
and
    `δ = g_1`
are algebraically independent whenever the underlying
    `A_i, g_i`
are independent variables.

This confirms that the earlier codimension-two detour is unnecessary in the
hypersurface graph setting: the stronger Stage-35 algebraic independence of
all coordinate functions supplies a direct triangular proof.

The next step is to evaluate this polynomial identity in the actual field
`K(A)` where `K` is the hypersurface function field, using:
* Stage 36 for algebraic independence of the `g_i`;
* `AlgebraicIndependent.sumElim_comp` for adjoining the `A_i`;
* `AlgebraicIndependent.aeval_of_algebraicIndependent` together with the
  theorem above.

That will give the exact Jouanolou mixed family in the function field.
-/


/-! ## Stage 39: evaluate the mixed family in an arbitrary field tower

Let
    `ℂ ⊆ K ⊆ L`,
let
    `g_0,...,g_n ∈ K`
be algebraically independent over `ℂ`, and let
    `A_0,...,A_n ∈ L`
be algebraically independent over `K`.

Mathlib's `AlgebraicIndependent.sumElim_comp` says that the combined family
`(A_i, g_i)` is algebraically independent over `ℂ` in `L`.

We reindex that combined family by the target variables of Stage 38, then
evaluate the algebraically independent polynomial family from Stage 38.
The result is the exact Jouanolou family
    `A_0,...,A_n, ξ = Σ A_i g_i, δ = g_1`.

Thus in our special graph setting the mixed-independence hypothesis of
Jouanolou follows directly from ordinary algebraic independence of the
coordinate functions.  No codimension-two lemma is required.
-/

/-- Reindex the target option variables as the combined family `(A_i,g_i)`.

For `n+1` geometric coordinates:
* `none` corresponds to `g_0`;
* `some (inl i)` corresponds to `A_i`;
* `some (inr j)` corresponds to `g_{j+1}`. -/
def jouanolouTargetEquivSucc
    (n : ℕ) :
    Option
        (Sum (Fin (n + 1)) (Fin n))
      ≃
    Sum (Fin (n + 1)) (Fin (n + 1)) where
  toFun
    | none => Sum.inr 0
    | some (Sum.inl i) => Sum.inl i
    | some (Sum.inr j) => Sum.inr j.succ
  invFun
    | Sum.inl i => some (Sum.inl i)
    | Sum.inr k =>
        Fin.cases none
          (fun j => some (Sum.inr j)) k
  left_inv := by
    intro x
    rcases x with _ | s
    · rfl
    · rcases s with i | j
      · rfl
      · rfl
  right_inv := by
    intro y
    rcases y with i | k
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · rfl

/-- The target-option family obtained from actual elements `A_i` and `g_i`. -/
def jouanolouUnderlyingFieldFamily
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    (n : ℕ)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K) :
    Option
        (JouanolouTargetCoeffVar (n + 1))
      → L :=
  fun o =>
    (Sum.elim A
      ((algebraMap K L) ∘ g))
      (jouanolouTargetEquivSucc n
        (by
          simpa [JouanolouTargetCoeffVar]
            using o))

/-- The actual mixed family:
* `none = ξ = Σ A_i g_i`;
* `some (inl i) = A_i`;
* `some (inr unit) = δ = g_1`. -/
def jouanolouMixedFieldFamily
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K) :
    Option
        (JouanolouSourceCoeffVar (n + 1))
      → L
  | none =>
      ∑ i : Fin (n + 1),
        A i * algebraMap K L (g i)
  | some (Sum.inl i) => A i
  | some (Sum.inr _) =>
      algebraMap K L (g ⟨1, by omega⟩)

/-- The underlying target family is algebraically independent over `ℂ`
whenever the `g_i` are independent over `ℂ` and the `A_i` are independent
over `K`. -/
theorem algebraicIndependent_jouanolouUnderlyingFieldFamily
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L]
    [Algebra K L] [IsScalarTower ℂ K L]
    (n : ℕ)
    (g : Fin (n + 1) → K)
    (hg : AlgebraicIndependent ℂ g)
    (A : Fin (n + 1) → L)
    (hA : AlgebraicIndependent K A) :
    AlgebraicIndependent ℂ
      (jouanolouUnderlyingFieldFamily n A g) := by
  have hCombined :
      AlgebraicIndependent ℂ
        (Sum.elim A
          ((algebraMap K L) ∘ g)) :=
    hg.sumElim_comp hA
  have hReindex :
      AlgebraicIndependent ℂ
        ((Sum.elim A
            ((algebraMap K L) ∘ g)) ∘
          (jouanolouTargetEquivSucc n)) :=
    (algebraicIndependent_equiv
      (jouanolouTargetEquivSucc n)).2
      hCombined
  change AlgebraicIndependent ℂ
    ((Sum.elim A ((algebraMap K L) ∘ g)) ∘
      (jouanolouTargetEquivSucc n))
  exact hReindex

/-- Evaluation of the Stage-38 `A_i` polynomial gives the actual `A_i`. -/
lemma aeval_jouanolouMixedPolynomialFamily_A
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ L] [Algebra K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K)
    (i : Fin (n + 1)) :
    (MvPolynomial.aeval
      (jouanolouUnderlyingFieldFamily n A g))
      (jouanolouMixedPolynomialFamily
        (m := n + 1) (by omega)
        (some (Sum.inl i)))
      =
    A i := by
  rw [jouanolouMixedPolynomialFamily_A]
  simp [jouanolouUnderlyingFieldFamily,
    jouanolouTargetEquivSucc,
    JouanolouTargetCoeffVar]

/-- Evaluation of `δ` gives `g_1`. -/
lemma aeval_jouanolouMixedPolynomialFamily_delta
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ L] [Algebra K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K) :
    (MvPolynomial.aeval
      (jouanolouUnderlyingFieldFamily n A g))
      (jouanolouMixedPolynomialFamily
        (m := n + 1) (by omega)
        (some (Sum.inr PUnit.unit)))
      =
    algebraMap K L (g ⟨1, by omega⟩) := by
  rw [jouanolouMixedPolynomialFamily_delta]
  simp [jouanolouUnderlyingFieldFamily,
    jouanolouTargetEquivSucc,
    JouanolouTargetCoeffVar]

/-- Evaluation of the distinguished mixed polynomial gives
`ξ = Σ A_i g_i`. -/
lemma aeval_jouanolouMixedPolynomialFamily_xi
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ L] [Algebra K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K) :
    (MvPolynomial.aeval
      (jouanolouUnderlyingFieldFamily n A g))
      (jouanolouMixedPolynomialFamily
        (m := n + 1) (by omega) none)
      =
    ∑ i : Fin (n + 1),
      A i * algebraMap K L (g i) := by
  rw [jouanolouMixedPolynomialFamily_xi]
  simp [jouanolouUnderlyingFieldFamily,
    jouanolouTargetEquivSucc,
    JouanolouTargetCoeffVar,
    Fin.sum_univ_succ]

/-- Evaluation of the whole Stage-38 family is the actual mixed field family. -/
lemma aeval_jouanolouMixedPolynomialFamily_eq
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ L] [Algebra K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (A : Fin (n + 1) → L)
    (g : Fin (n + 1) → K) :
    (fun o =>
      (MvPolynomial.aeval
        (jouanolouUnderlyingFieldFamily n A g))
        (jouanolouMixedPolynomialFamily
          (m := n + 1) (by omega) o))
      =
    jouanolouMixedFieldFamily n hn A g := by
  funext o
  rcases o with _ | s
  · exact
      aeval_jouanolouMixedPolynomialFamily_xi
        n hn A g
  · rcases s with i | u
    · exact
        aeval_jouanolouMixedPolynomialFamily_A
          n hn A g i
    · cases u
      exact
        aeval_jouanolouMixedPolynomialFamily_delta
          n hn A g

/-- **Direct Jouanolou mixed-independence theorem.**

No codimension hypothesis is present. -/
theorem algebraicIndependent_jouanolouMixedFieldFamily
    {K L : Type*}
    [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L]
    [Algebra K L] [IsScalarTower ℂ K L]
    (n : ℕ)
    (hn : 1 ≤ n)
    (g : Fin (n + 1) → K)
    (hg : AlgebraicIndependent ℂ g)
    (A : Fin (n + 1) → L)
    (hA : AlgebraicIndependent K A) :
    AlgebraicIndependent ℂ
      (jouanolouMixedFieldFamily n hn A g) := by
  have hUnderlying :
      AlgebraicIndependent ℂ
        (jouanolouUnderlyingFieldFamily n A g) :=
    algebraicIndependent_jouanolouUnderlyingFieldFamily
      n g hg A hA
  have hPoly :
      AlgebraicIndependent ℂ
        (jouanolouMixedPolynomialFamily
          (m := n + 1) (by omega)) :=
    algebraicIndependent_jouanolouMixedPolynomialFamily
      (m := n + 1) (by omega)
  have hEval :=
    hUnderlying.aeval_of_algebraicIndependent
      hPoly
  rw [aeval_jouanolouMixedPolynomialFamily_eq
        n hn A g] at hEval
  exact hEval

/-!
Stage-39 audit
--------------

The key mixed independence is now a direct field-theoretic consequence of two
ordinary algebraic-independent families:

    `g_i` independent over `ℂ`,
    `A_i` independent over `K`
      ⇒
    `(A_i, ξ = Σ A_i g_i, δ = g_1)` independent over `ℂ`.

This is exactly the special input required in Jouanolou's generic-hyperplane
field argument.

Therefore the codimension-two detour discussed after Stage 36 is definitively
unnecessary for this project: Stacks needs it only because its general
linear-system generators need not themselves be algebraically independent.
Our graph-hyperplane generators are coordinate functions, and Stage 35 proves
the stronger independence directly.

The next step is to instantiate this theorem with
    `K = HypersurfaceFunctionField f`
and
    `L = K(A_0,...,A_{m-1})`,
then formalize the remaining pure field lemma identifying the generic
hyperplane function field as geometrically integral.
-/


/-! ## Stage 40: instantiate the mixed-independence theorem on the hypersurface

We now specialize Stage 39 to the actual function-field tower of an
irreducible hypersurface.

For a pivot coordinate `i` occurring in `f`, put
    `K = Frac(ℂ[X]/(f))`
and
    `L = K(A₀,...,A_{m-1})`.

The geometric coordinate functions `g_j` are the non-pivot ambient
coordinates in `K`; by Stage 36 they are algebraically independent over `ℂ`.
The rational parameters `A_j` are algebraically independent over `K`.

Stage 39 therefore gives the exact mixed family
    `A_j, ξ = Σ A_j g_j, δ`
algebraically independent over `ℂ`.

To avoid any hidden dimension argument, we package the result only after
choosing a concrete `Fin m` equivalence with `Fin ((m-1)+1)`.
-/

/-- For `m ≥ 1`, the canonical equivalence
`Fin ((m - 1) + 1) ≃ Fin m`. -/
def finPredSuccEquiv
    {m : ℕ} (hm : 1 ≤ m) :
    Fin ((m - 1) + 1) ≃ Fin m :=
  Fin.castOrderIso (by omega)

/-- Reindex a `Fin m` family by `Fin ((m-1)+1)`. -/
def predSuccReindex
    {m : ℕ} (hm : 1 ≤ m)
    {α : Type*}
    (x : Fin m → α) :
    Fin ((m - 1) + 1) → α :=
  x ∘ finPredSuccEquiv hm

/-- Algebraic independence is preserved by the canonical predecessor/successor
reindexing. -/
lemma algebraicIndependent_predSuccReindex
    {K L : Type*}
    [CommRing K] [CommRing L] [Algebra K L]
    {m : ℕ} (hm : 1 ≤ m)
    {x : Fin m → L}
    (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K
      (predSuccReindex hm x) := by
  exact
    (algebraicIndependent_equiv
      (finPredSuccEquiv hm)).2 hx

/-- The actual graph-parameter family over the hypersurface function field. -/
noncomputable def hypersurfaceRationalParam
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    Fin m →
      HypersurfaceParamField f := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf
  exact
    rationalParamVar
      (HypersurfaceFunctionField f)

/-- The parameter family is algebraically independent over the hypersurface
function field. -/
theorem algebraicIndependent_hypersurfaceRationalParam
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    AlgebraicIndependent
      (HypersurfaceFunctionField f)
      (hypersurfaceRationalParam hf) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf
  exact
    algebraicIndependent_rationalParamVar
      (HypersurfaceFunctionField f) m

/-- Reindexed geometric coordinates, in the exact `n+1` format expected by
Stage 39. -/
noncomputable def hypersurfaceJouanolouG
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (hm : 1 ≤ m)
    (i : Fin (m + 1)) :
    Fin ((m - 1) + 1) →
      HypersurfaceFunctionField f :=
  predSuccReindex hm
    (hypersurfaceOtherCoordInFunctionField hf i)

/-- Reindexed graph parameters in the same format. -/
noncomputable def hypersurfaceJouanolouA
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (hm : 1 ≤ m) :
    Fin ((m - 1) + 1) →
      HypersurfaceParamField f :=
  predSuccReindex hm
    (hypersurfaceRationalParam hf)

/-- The geometric `g` family used by Jouanolou is algebraically independent. -/
theorem algebraicIndependent_hypersurfaceJouanolouG
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (hm : 1 ≤ m)
    {i : Fin (m + 1)}
    (hi : i ∈ f.vars) :
    AlgebraicIndependent ℂ
      (hypersurfaceJouanolouG hf hm i) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf
  exact
    algebraicIndependent_predSuccReindex
      hm
      (algebraicIndependent_hypersurfaceOtherCoordInFunctionField
        hf hi)

/-- The parameter `A` family is algebraically independent over the
hypersurface function field. -/
theorem algebraicIndependent_hypersurfaceJouanolouA
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (hm : 1 ≤ m) :
    AlgebraicIndependent
      (HypersurfaceFunctionField f)
      (hypersurfaceJouanolouA hf hm) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf
  exact
    algebraicIndependent_predSuccReindex
      hm
      (algebraicIndependent_hypersurfaceRationalParam hf)

/-- The concrete mixed family on the hypersurface parameter field.

It is deliberately defined by reusing the abstract Stage-39 family, so no
semantic identification is hidden in later proofs. -/
noncomputable def hypersurfaceJouanolouMixedFamily
    {m : ℕ}
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    (hm : 2 ≤ m)
    (i : Fin (m + 1)) :
    Option
      (JouanolouSourceCoeffVar ((m - 1) + 1)) →
      HypersurfaceParamField f := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf
  exact
    jouanolouMixedFieldFamily
      (m - 1)
      (by omega)
      (hypersurfaceJouanolouA hf (by omega))
      (hypersurfaceJouanolouG hf (by omega) i)

/-- **Project-specific Jouanolou mixed independence.**

For every irreducible hypersurface with at least two non-pivot coordinates,
and every pivot which occurs in `f`, the family
    `(A_j, ξ = Σ A_j g_j, δ)`
in the rational parameter extension of its function field is algebraically
independent over `ℂ`.
-/
theorem algebraicIndependent_hypersurfaceJouanolouMixedFamily
    {m : ℕ}
    (hm : 2 ≤ m)
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f)
    {i : Fin (m + 1)}
    (hi : i ∈ f.vars) :
    AlgebraicIndependent ℂ
      (hypersurfaceJouanolouMixedFamily hf hm i) := by
  letI : (hypersurfaceIdeal f).IsPrime :=
    hypersurfaceIdeal_isPrime hf
  letI : Field (HypersurfaceFunctionField f) :=
    hypersurfaceFunctionFieldField hf

  let K := HypersurfaceFunctionField f
  let L := RationalParamField K m

  have hg :
      AlgebraicIndependent ℂ
        (hypersurfaceJouanolouG hf (by omega) i) :=
    algebraicIndependent_hypersurfaceJouanolouG
      hf (by omega) hi

  have hA :
      AlgebraicIndependent K
        (hypersurfaceJouanolouA hf (by omega)) :=
    algebraicIndependent_hypersurfaceJouanolouA
      hf (by omega)

  have hmix :=
    algebraicIndependent_jouanolouMixedFieldFamily
      (K := K) (L := L)
      (m - 1)
      (by omega)
      (hypersurfaceJouanolouG hf (by omega) i)
      hg
      (hypersurfaceJouanolouA hf (by omega))
      hA

  simpa [hypersurfaceJouanolouMixedFamily, K, L]
    using hmix

/-- Every irreducible hypersurface admits a pivot for which the concrete
Jouanolou mixed family is algebraically independent. -/
theorem exists_pivot_hypersurfaceJouanolouMixedFamily
    {m : ℕ}
    (hm : 2 ≤ m)
    {f : Poly ℂ (m + 1)}
    (hf : Irreducible f) :
    ∃ i : Fin (m + 1),
      i ∈ f.vars ∧
      AlgebraicIndependent ℂ
        (hypersurfaceJouanolouMixedFamily hf hm i) := by
  obtain ⟨i, hi⟩ :=
    exists_mem_vars_of_irreducible hf
  exact
    ⟨i, hi,
      algebraicIndependent_hypersurfaceJouanolouMixedFamily
        hm hf hi⟩

/-!
Stage-40 audit
--------------

The mixed-independence part of Jouanolou is now fully instantiated in the
actual hypersurface function field.

For `m ≥ 2`:
* choose a pivot coordinate occurring in `f`;
* the remaining `m` hypersurface coordinates are algebraically independent;
* the `m` graph parameters are algebraically independent over that function
  field;
* therefore `(A_j, ξ, δ)` is algebraically independent over `ℂ`.

Thus the general Stacks codimension-two lemma is not needed for Problem 20.1.

The remaining content of `GenericGraphAbsoluteIrreducibility` is now exactly
the **infinite-base-field Jouanolou field lemma** (Stacks 37.32.1), specialized
to `k = ℂ`, followed by the identification of its generic hyperplane field
with the fraction field of `genericGraphSection f`.
-/


/-! ## Stage 41: translation automorphisms of the rational parameter field

This is the first dynamic ingredient in the proof of the infinite-base-field
Jouanolou lemma.

For a field `K`, a direction `c : Fin m → K`, and a scalar `b : K`, define
the affine translation
    `A_i ↦ A_i + b c_i`
on the polynomial parameter ring `K[A]`.

Translation by `-b` is its inverse, so this is a `K`-algebra automorphism.
Mathlib's fraction-ring API then extends it uniquely to
`K(A₀,...,A_{m-1})`.

For
    `ξ = Σ A_i g_i`
and
    `δ = Σ c_i g_i`
we prove exactly
    `σ_b(ξ) = ξ + b δ`
and
    `σ_b(δ) = δ`.

These are the automorphisms used in Stacks 37.32.1.
-/

/-- Polynomial-ring translation homomorphism. -/
noncomputable def rationalParamTranslateHom
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    RationalParamRing K m →ₐ[K]
      RationalParamRing K m :=
  MvPolynomial.aeval
    (fun i =>
      MvPolynomial.X i +
        MvPolynomial.C (b * c i))

@[simp] lemma rationalParamTranslateHom_X
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K)
    (i : Fin m) :
    rationalParamTranslateHom K b c
        (MvPolynomial.X i) =
      MvPolynomial.X i +
        MvPolynomial.C (b * c i) := by
  simp [rationalParamTranslateHom]

/-- Translation by `b c` followed by translation by `-b c` is the identity. -/
lemma rationalParamTranslateHom_comp_neg
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    (rationalParamTranslateHom K b c).comp
        (rationalParamTranslateHom K (-b) c)
      =
    AlgHom.id K (RationalParamRing K m) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalParamTranslateHom]
  ring

/-- The reverse composition is also the identity. -/
lemma rationalParamTranslateHom_neg_comp
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    (rationalParamTranslateHom K (-b) c).comp
        (rationalParamTranslateHom K b c)
      =
    AlgHom.id K (RationalParamRing K m) := by
  simpa using
    rationalParamTranslateHom_comp_neg
      K (-b) c

/-- Affine translation automorphism of the polynomial parameter ring. -/
noncomputable def rationalParamTranslatePolyEquiv
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    RationalParamRing K m ≃ₐ[K]
      RationalParamRing K m :=
  AlgEquiv.ofAlgHom
    (rationalParamTranslateHom K b c)
    (rationalParamTranslateHom K (-b) c)
    (rationalParamTranslateHom_comp_neg K b c)
    (rationalParamTranslateHom_neg_comp K b c)

@[simp] lemma rationalParamTranslatePolyEquiv_X
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K)
    (i : Fin m) :
    rationalParamTranslatePolyEquiv K b c
        (MvPolynomial.X i) =
      MvPolynomial.X i +
        MvPolynomial.C (b * c i) := by
  rfl

/-- Extend the polynomial translation to the rational function field. -/
noncomputable def rationalParamTranslateFieldEquiv
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    RationalParamField K m ≃ₐ[K]
      RationalParamField K m :=
  (IsFractionRing.fieldEquivOfAlgEquivHom
      K (RationalParamField K m))
    (rationalParamTranslatePolyEquiv K b c)

/-- Exact action of the fraction-field translation on a parameter coordinate. -/
@[simp] theorem rationalParamTranslateFieldEquiv_param
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K)
    (i : Fin m) :
    rationalParamTranslateFieldEquiv K b c
        (rationalParamVar K i)
      =
    rationalParamVar K i +
      algebraMap K (RationalParamField K m)
        (b * c i) := by
  unfold rationalParamVar
  simp [rationalParamTranslateFieldEquiv,
    IsFractionRing.fieldEquivOfAlgEquivHom_apply,
    rationalParamTranslatePolyEquiv,
    rationalParamTranslateHom]

/-- The inverse polynomial translation is translation by `-b`. -/
lemma rationalParamTranslatePolyEquiv_symm
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    (rationalParamTranslatePolyEquiv K b c).symm =
      rationalParamTranslatePolyEquiv K (-b) c := by
  apply AlgEquiv.coe_fun_injective
  funext p
  rfl

/-- The inverse fraction-field translation is translation by `-b`. -/
lemma rationalParamTranslateFieldEquiv_symm
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K) :
    (rationalParamTranslateFieldEquiv K b c).symm =
      rationalParamTranslateFieldEquiv K (-b) c := by
  let H :=
    IsFractionRing.fieldEquivOfAlgEquivHom
      K (RationalParamField K m)
  change (H (rationalParamTranslatePolyEquiv K b c)).symm =
    H (rationalParamTranslatePolyEquiv K (-b) c)
  rw [← rationalParamTranslatePolyEquiv_symm]
  exact (map_inv H (rationalParamTranslatePolyEquiv K b c)).symm

/-! ### Linear forms `ξ` and `δ` -/

/-- The universal linear combination
`ξ = Σ A_i * g_i` in `K(A)`. -/
noncomputable def rationalParamXi
    (K : Type*) [Field K]
    {m : ℕ}
    (g : Fin m → K) :
    RationalParamField K m :=
  ∑ i : Fin m,
    rationalParamVar K i *
      algebraMap K (RationalParamField K m)
        (g i)

/-- The fixed directional combination
`δ = Σ c_i g_i`, regarded inside `K(A)`. -/
noncomputable def rationalParamDelta
    (K : Type*) [Field K]
    {m : ℕ}
    (c g : Fin m → K) :
    RationalParamField K m :=
  algebraMap K (RationalParamField K m)
    (∑ i : Fin m, c i * g i)

/-- The parameter translation fixes every element coming from `K`. -/
@[simp] lemma rationalParamTranslateFieldEquiv_algebraMap
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c : Fin m → K)
    (x : K) :
    rationalParamTranslateFieldEquiv K b c
        (algebraMap K (RationalParamField K m) x)
      =
    algebraMap K (RationalParamField K m) x := by
  exact
    (rationalParamTranslateFieldEquiv K b c).commutes x

/-- **Stacks translation identity**
`σ_b(ξ) = ξ + b δ`. -/
theorem rationalParamTranslateFieldEquiv_xi
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c g : Fin m → K) :
    rationalParamTranslateFieldEquiv K b c
        (rationalParamXi K g)
      =
    rationalParamXi K g +
      algebraMap K (RationalParamField K m) b *
        rationalParamDelta K c g := by
  classical
  unfold rationalParamXi rationalParamDelta
  rw [map_sum]
  simp_rw [map_mul]
  simp_rw [rationalParamTranslateFieldEquiv_param]
  simp_rw [rationalParamTranslateFieldEquiv_algebraMap]
  push_cast
  simp only [Finset.sum_add_distrib]
  congr 1
  rw [map_sum]
  simp_rw [map_mul]
  ring_nf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The directional combination `δ` is fixed by every translation. -/
@[simp] theorem rationalParamTranslateFieldEquiv_delta
    (K : Type*) [Field K]
    {m : ℕ}
    (b : K)
    (c g : Fin m → K) :
    rationalParamTranslateFieldEquiv K b c
        (rationalParamDelta K c g)
      =
    rationalParamDelta K c g := by
  simp [rationalParamDelta]

/-! ### Relative separable closure over an algebraically closed base -/

/-- An algebraically closed base field is relatively separably closed in every
field extension.  This is the field-theoretic form of the fact that a field
extension of `ℂ` is geometrically irreducible over `ℂ`. -/
theorem separableClosure_eq_bot_of_isAlgClosed
    (F E : Type*)
    [Field F] [IsAlgClosed F]
    [Field E] [Algebra F E] :
    separableClosure F E = ⊥ := by
  exact
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
      (separableClosure F E)

/-!
Stage-41 audit
--------------

Two further pieces of the Stacks 37.32.1 proof are now internal:

1. the affine parameter translations extend to explicit automorphisms of the
   rational function field;
2. their exact action is
       `σ_b(ξ) = ξ + b δ`,
       `σ_b(δ) = δ`.

Additionally, the separable-closure criterion is easy over the original base
`ℂ`: since `ℂ` is algebraically closed, it is relatively separably closed in
every field extension.

The remaining hard field-theoretic part is now sharply localized:
prove that the relative separable closure of
    `K₁ = ℂ(A)(ξ)`
inside
    `Ω = K(A)`
is trivial.
The infinite-field Stacks argument achieves this by comparing finitely many
translated finite separable subextensions inside
    `K₂ = ℂ(A)(ξ,δ)`.

No new Bertini hypothesis is introduced.
-/


/-! ## Stage 42: the fields `K₀ ⊂ K₁ ⊂ K₂` and the pure-transcendence core

We now formalize the exact intermediate fields used in the infinite-base
Jouanolou argument.

For a base field `F`, ambient field `Ω`, a finite parameter family `A_i`,
and two distinguished elements `ξ, δ ∈ Ω`, define

    K₀ = F(A_i),
    K₁ = F(A_i, ξ),
    K₂ = F(A_i, ξ, δ).

The first part of this stage proves all finite-generation, containment, and
generator-membership facts directly from the `IntermediateField.adjoin` API.

The second part repackages a mixed algebraically independent family
    `(A_i, ξ, δ)`
into the statement that the pair `(ξ,δ)` is algebraically independent over
the *parameter algebra* `F[A_i]`.

This is the ring-level form of the pure-transcendence statement needed before
passing to the fraction field `K₀ = Frac(F[A_i])`.
-/

/-! ### The three Jouanolou intermediate fields -/

/-- `K₀ = F(A_i)`. -/
def jouanolouK0
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω) :
    IntermediateField F Ω :=
  IntermediateField.adjoin F (Set.range A)

/-- `K₁ = F(A_i, ξ)`. -/
def jouanolouK1
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ : Ω) :
    IntermediateField F Ω :=
  IntermediateField.adjoin F
    (Set.range A ∪ {ξ})

/-- `K₂ = F(A_i, ξ, δ)`. -/
def jouanolouK2
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    IntermediateField F Ω :=
  IntermediateField.adjoin F
    (Set.range A ∪ {ξ, δ})

/-- Every parameter belongs to `K₀`. -/
lemma jouanolouK0_param_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (i : ι) :
    A i ∈ jouanolouK0 F A := by
  exact
    (IntermediateField.subset_adjoin F (Set.range A))
      (Set.mem_range_self i)

/-- Every parameter belongs to `K₁`. -/
lemma jouanolouK1_param_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ : Ω)
    (i : ι) :
    A i ∈ jouanolouK1 F A ξ := by
  exact (IntermediateField.subset_adjoin F (Set.range A ∪ {ξ}))
    (Set.mem_union_left _ (Set.mem_range_self i))

/-- The distinguished element `ξ` belongs to `K₁`. -/
lemma jouanolouK1_xi_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ : Ω) :
    ξ ∈ jouanolouK1 F A ξ := by
  exact (IntermediateField.subset_adjoin F (Set.range A ∪ {ξ}))
    (Set.mem_union_right _ (Set.mem_singleton ξ))

/-- Every parameter belongs to `K₂`. -/
lemma jouanolouK2_param_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (i : ι) :
    A i ∈ jouanolouK2 F A ξ δ := by
  exact (IntermediateField.subset_adjoin F (Set.range A ∪ {ξ, δ}))
    (Set.mem_union_left _ (Set.mem_range_self i))

/-- `ξ ∈ K₂`. -/
lemma jouanolouK2_xi_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    ξ ∈ jouanolouK2 F A ξ δ := by
  exact (IntermediateField.subset_adjoin F (Set.range A ∪ {ξ, δ}))
    (Set.mem_union_right _ (by simp))

/-- `δ ∈ K₂`. -/
lemma jouanolouK2_delta_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    δ ∈ jouanolouK2 F A ξ δ := by
  exact (IntermediateField.subset_adjoin F (Set.range A ∪ {ξ, δ}))
    (Set.mem_union_right _ (by simp))

/-- `K₀ ≤ K₁`. -/
lemma jouanolouK0_le_K1
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ : Ω) :
    jouanolouK0 F A ≤
      jouanolouK1 F A ξ := by
  unfold jouanolouK0 jouanolouK1
  exact
    IntermediateField.adjoin.mono F
      (Set.subset_union_left)

/-- `K₁ ≤ K₂`. -/
lemma jouanolouK1_le_K2
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    jouanolouK1 F A ξ ≤
      jouanolouK2 F A ξ δ := by
  unfold jouanolouK1 jouanolouK2
  apply IntermediateField.adjoin.mono F
  intro x hx
  rcases hx with hxA | hxξ
  · exact Or.inl hxA
  · rcases hxξ with rfl
    exact Or.inr (by simp)

/-- `K₀ ≤ K₂`. -/
lemma jouanolouK0_le_K2
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    jouanolouK0 F A ≤
      jouanolouK2 F A ξ δ :=
  (jouanolouK0_le_K1 F A ξ).trans
    (jouanolouK1_le_K2 F A ξ δ)

/-! ### Finite generation -/

/-- `K₀/F` is finitely generated when the parameter index is finite. -/
lemma jouanolouK0_fg
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω) :
    (jouanolouK0 F A).FG := by
  unfold jouanolouK0
  exact
    IntermediateField.fg_adjoin_of_finite
      (Set.finite_range A)

/-- `K₁/F` is finitely generated. -/
lemma jouanolouK1_fg
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω)
    (ξ : Ω) :
    (jouanolouK1 F A ξ).FG := by
  unfold jouanolouK1
  apply IntermediateField.fg_adjoin_of_finite
  exact
    (Set.finite_range A).union
      (Set.finite_singleton ξ)

/-- `K₂/F` is finitely generated. -/
lemma jouanolouK2_fg
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω)
    (ξ δ : Ω) :
    (jouanolouK2 F A ξ δ).FG := by
  unfold jouanolouK2
  apply IntermediateField.fg_adjoin_of_finite
  exact
    (Set.finite_range A).union
      ((Set.finite_singleton ξ).union
        (Set.finite_singleton δ))

/-- Hence all three fields are essentially of finite type over the base. -/
lemma jouanolouK0_essFiniteType
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω) :
    Algebra.EssFiniteType F ↥(jouanolouK0 F A) := by
  rw [IntermediateField.essFiniteType_iff]
  exact jouanolouK0_fg F A

lemma jouanolouK1_essFiniteType
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω)
    (ξ : Ω) :
    Algebra.EssFiniteType F ↥(jouanolouK1 F A ξ) := by
  rw [IntermediateField.essFiniteType_iff]
  exact jouanolouK1_fg F A ξ

lemma jouanolouK2_essFiniteType
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*} [Finite ι]
    (A : ι → Ω)
    (ξ δ : Ω) :
    Algebra.EssFiniteType F ↥(jouanolouK2 F A ξ δ) := by
  rw [IntermediateField.essFiniteType_iff]
  exact jouanolouK2_fg F A ξ δ

/-! ### Reindex the mixed family as `(ξ,δ)` over the parameter family -/

/-- The two distinguished elements as a `Fin 2` family. -/
def jouanolouPair
    {Ω : Type*}
    (ξ δ : Ω) :
    Fin 2 → Ω
  | ⟨0, _⟩ => ξ
  | ⟨1, _⟩ => δ

@[simp] lemma jouanolouPair_zero
    {Ω : Type*}
    (ξ δ : Ω) :
    jouanolouPair ξ δ (0 : Fin 2) = ξ := rfl

@[simp] lemma jouanolouPair_one
    {Ω : Type*}
    (ξ δ : Ω) :
    jouanolouPair ξ δ (1 : Fin 2) = δ := rfl

/-- Reindex `Sum (Fin 2) ι` with the Stage-39 index
`Option (Sum ι PUnit)`:
* pair index `0` goes to `ξ`,
* pair index `1` goes to `δ`,
* right summand `i` goes to parameter `A_i`. -/
def jouanolouPairParamEquiv
    (ι : Type*) :
    Sum (Fin 2) ι ≃
      Option (Sum ι PUnit) where
  toFun
    | Sum.inl j =>
        Fin.cases none
          (fun _ => some (Sum.inr PUnit.unit))
          j
    | Sum.inr i =>
        some (Sum.inl i)
  invFun
    | none =>
        Sum.inl 0
    | some (Sum.inl i) =>
        Sum.inr i
    | some (Sum.inr _) =>
        Sum.inl 1
  left_inv := by
    intro z
    rcases z with j | i
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · fin_cases k
        rfl
    · rfl
  right_inv := by
    intro z
    rcases z with _ | s
    · rfl
    · rcases s with i | u
      · rfl
      · cases u
        rfl

/-- An abstract mixed family in the same indexing convention as Stage 39. -/
def jouanolouAbstractMixedFamily
    {ι Ω : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    Option (Sum ι PUnit) → Ω
  | none => ξ
  | some (Sum.inl i) => A i
  | some (Sum.inr _) => δ

/-- After reindexing, the mixed family is exactly
`Sum.elim (ξ,δ) A`. -/
lemma jouanolouAbstractMixedFamily_reindex
    {ι Ω : Type*}
    (A : ι → Ω)
    (ξ δ : Ω) :
    (jouanolouAbstractMixedFamily A ξ δ) ∘
        (jouanolouPairParamEquiv ι)
      =
    Sum.elim (jouanolouPair ξ δ) A := by
  funext z
  rcases z with j | i
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · fin_cases k
      rfl
  · rfl

/-- If the full mixed family `(A_i,ξ,δ)` is algebraically independent over
`F`, then the pair `(ξ,δ)` is algebraically independent over the parameter
algebra `F[A_i]`.

This is exactly `AlgebraicIndependent.sumElim_iff`, after the explicit
reindexing above. -/
theorem algebraicIndependent_pair_over_parameterAlgebra
    (F : Type*) [CommRing F]
    {Ω : Type*} [CommRing Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (hmix :
      AlgebraicIndependent F
        (jouanolouAbstractMixedFamily A ξ δ)) :
    AlgebraicIndependent
      ↥(Algebra.adjoin F (Set.range A))
      (jouanolouPair ξ δ) := by
  have hreindexed :
      AlgebraicIndependent F
        (Sum.elim (jouanolouPair ξ δ) A) := by
    have h :=
      (algebraicIndependent_equiv
        (jouanolouPairParamEquiv ι)).2 hmix
    simpa [jouanolouAbstractMixedFamily_reindex]
      using h
  exact
    (AlgebraicIndependent.sumElim_iff.mp
      hreindexed).2

/-- In particular `ξ` is transcendental over the parameter algebra. -/
theorem transcendental_xi_over_parameterAlgebra
    (F : Type*) [CommRing F]
    {Ω : Type*} [CommRing Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (hmix :
      AlgebraicIndependent F
        (jouanolouAbstractMixedFamily A ξ δ)) :
    Transcendental
      ↥(Algebra.adjoin F (Set.range A))
      ξ := by
  have hpair :=
    algebraicIndependent_pair_over_parameterAlgebra
      F A ξ δ hmix
  exact hpair.transcendental (0 : Fin 2)

/-- Likewise `δ` is transcendental over the parameter algebra. -/
theorem transcendental_delta_over_parameterAlgebra
    (F : Type*) [CommRing F]
    {Ω : Type*} [CommRing Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (hmix :
      AlgebraicIndependent F
        (jouanolouAbstractMixedFamily A ξ δ)) :
    Transcendental
      ↥(Algebra.adjoin F (Set.range A))
      δ := by
  have hpair :=
    algebraicIndependent_pair_over_parameterAlgebra
      F A ξ δ hmix
  exact hpair.transcendental (1 : Fin 2)

/-! ### Map an adjoin through an algebra automorphism -/

/-- If an algebra endomorphism sends every generator of `F(S)` into an
intermediate field `T`, then the image of `F(S)` lies in `T`. -/
lemma map_adjoin_le_of_forall_image_mem
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {S : Set Ω}
    (e : Ω →ₐ[F] Ω)
    (T : IntermediateField F Ω)
    (hS : ∀ x ∈ S, e x ∈ T) :
    IntermediateField.map e
        (IntermediateField.adjoin F S)
      ≤ T := by
  rw [IntermediateField.adjoin_map]
  rw [IntermediateField.adjoin_le_iff]
  rintro y ⟨x, hx, rfl⟩
  exact hS x hx

/-!
Stage-42 audit
--------------

The Stacks field tower is now explicit:

    K₀ = F(A),
    K₁ = F(A,ξ),
    K₂ = F(A,ξ,δ),

with:
* all generator-membership lemmas;
* `K₀ ≤ K₁ ≤ K₂`;
* finite generation / essential finite type of all three fields.

More importantly, Stage 40's mixed algebraic independence can now be read in
the exact pure-transcendence form:

    `(A_i, ξ, δ)` algebraically independent over `F`
        ⇒
    `(ξ,δ)` algebraically independent over the parameter algebra `F[A_i]`.

Thus `ξ` and `δ` are individually transcendental over `F[A]`; the pair is
independent there.

The remaining bridge is to pass this pair-independence from the parameter
*algebra* `F[A]` to its fraction field `K₀ = F(A)`.  The Mathlib instance
`IntermediateField.algebraAdjoinAdjoin.instIsAlgebraic...` plus
`Transcendental.extendScalars` already gives the elementwise part; the next
stage will package the pair statement over `K₀` and then prove that the
translations preserve `K₀` and `K₂`.
-/


/-! ## Stage 43: pass transcendence to `K₀ = F(A)` and preserve `K₀,K₂`
under the Stacks translations

Stage 42 proved that `ξ` and `δ` are transcendental over the parameter
*algebra* `F[A]`.  Mathlib identifies the field adjoin `F(A)` as a fraction
ring, hence as an algebraic extension of `F[A]`; therefore
`Transcendental.extendScalars` passes transcendence to `K₀ = F(A)`.

The second half of this stage restricts the Stage-41 parameter translations
to the original base field `F` and proves that they preserve exactly the two
intermediate fields needed in Stacks 37.32.1:

    K₀ = F(A_i),
    K₂ = F(A_i, ξ, δ).

The direction vector and translation scalar are required to lie in `F`;
this is essential, because then the translated parameters differ from the
original ones by constants already lying in `K₀`.
-/

/-! ### Transcendence from the parameter algebra to the parameter field -/

/-- The field adjoin `F(A)` is algebraic over the algebra adjoin `F[A]`.

This is the standard fraction-field fact already provided by Mathlib; we name
it here only to make later typeclass inference explicit. -/
noncomputable def parameterAlgebraToK0Algebra
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω) :
    Algebra
      ↥(Algebra.adjoin F (Set.range A))
      ↥(jouanolouK0 F A) :=
  IntermediateField.algebraAdjoinAdjoin.instAlgebraSubtypeMemSubalgebraAdjoinAdjoin
    F (Set.range A)

/-- `F[A] → F(A) → Ω` is a scalar tower. -/
lemma parameterAlgebra_K0_scalarTower
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω) :
    IsScalarTower
      ↥(Algebra.adjoin F (Set.range A))
      ↥(jouanolouK0 F A)
      Ω := by
  letI :
      Algebra
        ↥(Algebra.adjoin F (Set.range A))
        ↥(jouanolouK0 F A) :=
    parameterAlgebraToK0Algebra F A
  exact
    IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalgebraAdjoinAdjoin_1
      F (Set.range A) Ω

/-- `F(A)` is algebraic over `F[A]`. -/
lemma parameterAlgebra_K0_isAlgebraic
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω) :
    Algebra.IsAlgebraic
      ↥(Algebra.adjoin F (Set.range A))
      ↥(jouanolouK0 F A) := by
  letI :
      Algebra
        ↥(Algebra.adjoin F (Set.range A))
        ↥(jouanolouK0 F A) :=
    parameterAlgebraToK0Algebra F A
  exact
    IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebraAdjoinAdjoin
      F (Set.range A)

/-- `ξ` is transcendental over `K₀ = F(A)`. -/
theorem transcendental_xi_over_jouanolouK0
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (hmix :
      AlgebraicIndependent F
        (jouanolouAbstractMixedFamily A ξ δ)) :
    Transcendental ↥(jouanolouK0 F A) ξ := by
  let R :=
    Algebra.adjoin F (Set.range A)
  let K0 :=
    jouanolouK0 F A

  letI : Algebra R K0 :=
    parameterAlgebraToK0Algebra F A
  letI : IsScalarTower R K0 Ω :=
    parameterAlgebra_K0_scalarTower F A
  letI : Algebra.IsAlgebraic R K0 :=
    parameterAlgebra_K0_isAlgebraic F A

  have hR : Transcendental R ξ := by
    simpa [R] using
      transcendental_xi_over_parameterAlgebra
        F A ξ δ hmix

  exact hR.extendScalars K0

/-- Likewise `δ` is transcendental over `K₀`. -/
theorem transcendental_delta_over_jouanolouK0
    (F : Type*) [Field F]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ι : Type*}
    (A : ι → Ω)
    (ξ δ : Ω)
    (hmix :
      AlgebraicIndependent F
        (jouanolouAbstractMixedFamily A ξ δ)) :
    Transcendental ↥(jouanolouK0 F A) δ := by
  let R :=
    Algebra.adjoin F (Set.range A)
  let K0 :=
    jouanolouK0 F A

  letI : Algebra R K0 :=
    parameterAlgebraToK0Algebra F A
  letI : IsScalarTower R K0 Ω :=
    parameterAlgebra_K0_scalarTower F A
  letI : Algebra.IsAlgebraic R K0 :=
    parameterAlgebra_K0_isAlgebraic F A

  have hR : Transcendental R δ := by
    simpa [R] using
      transcendental_delta_over_parameterAlgebra
        F A ξ δ hmix

  exact hR.extendScalars K0

/-! ### Restrict the rational-parameter translation to the smaller base field -/

/-- Stacks translation on `K(A)`, viewed as an `F`-algebra automorphism.

Here
    `F ⊆ K`,
`b : F`, and `c_i : F`.
The underlying `K`-algebra automorphism is the Stage-41 translation by the
images of `b,c_i` in `K`. -/
noncomputable def rationalParamTranslateRestrict
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F) :
    RationalParamField K m ≃ₐ[F]
      RationalParamField K m := by
  letI : Algebra F (RationalParamField K m) :=
    Algebra.restrictScalars F K (RationalParamField K m)
  letI : IsScalarTower F K (RationalParamField K m) :=
    IsScalarTower.restrictScalars F K (RationalParamField K m)
  exact
    (rationalParamTranslateFieldEquiv
      K (algebraMap F K b)
      (fun i => algebraMap F K (c i))).restrictScalars F

/-- The restricted translation has the same underlying function as the
Stage-41 translation. -/
@[simp] lemma rationalParamTranslateRestrict_apply
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (x : RationalParamField K m) :
    rationalParamTranslateRestrict F K b c x =
      rationalParamTranslateFieldEquiv
        K (algebraMap F K b)
        (fun i => algebraMap F K (c i)) x := by
  simp [rationalParamTranslateRestrict]

/-- Exact action on a parameter coordinate. -/
theorem rationalParamTranslateRestrict_param
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (i : Fin m) :
    rationalParamTranslateRestrict F K b c
        (rationalParamVar K i)
      =
    rationalParamVar K i +
      algebraMap F (RationalParamField K m)
        (b * c i) := by
  rw [rationalParamTranslateRestrict_apply]
  rw [rationalParamTranslateFieldEquiv_param]
  simp [IsScalarTower.algebraMap_apply F K
    (RationalParamField K m)]

/-- Its inverse is the translation by `-b`. -/
theorem rationalParamTranslateRestrict_symm
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F) :
    (rationalParamTranslateRestrict F K b c).symm =
      rationalParamTranslateRestrict F K (-b) c := by
  ext x
  simp [rationalParamTranslateRestrict,
    rationalParamTranslateFieldEquiv_symm]

/-! ### Invariance of `K₀ = F(A)` -/

/-- One translation maps `K₀` into itself. -/
lemma map_jouanolouK0_translate_le
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F) :
    IntermediateField.map
        (rationalParamTranslateRestrict F K b c).toAlgHom
        (jouanolouK0 F
          (rationalParamVar K :
            Fin m → RationalParamField K m))
      ≤
    jouanolouK0 F
      (rationalParamVar K :
        Fin m → RationalParamField K m) := by
  apply map_adjoin_le_of_forall_image_mem
  intro x hx
  rcases hx with ⟨i, rfl⟩
  change
    rationalParamTranslateRestrict F K b c
        (rationalParamVar K i) ∈
      jouanolouK0 F
        (rationalParamVar K :
          Fin m → RationalParamField K m)
  rw [rationalParamTranslateRestrict_param]
  exact
    (jouanolouK0 F
      (rationalParamVar K :
        Fin m → RationalParamField K m)).add_mem
      (jouanolouK0_param_mem
        F
        (rationalParamVar K :
          Fin m → RationalParamField K m)
        i)
      ((jouanolouK0 F
        (rationalParamVar K :
          Fin m → RationalParamField K m)).algebraMap_mem
        (b * c i))

/-- Therefore every Stacks translation preserves `K₀` exactly. -/
theorem map_jouanolouK0_translate_eq
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F) :
    IntermediateField.map
        (rationalParamTranslateRestrict F K b c).toAlgHom
        (jouanolouK0 F
          (rationalParamVar K :
            Fin m → RationalParamField K m))
      =
    jouanolouK0 F
      (rationalParamVar K :
        Fin m → RationalParamField K m) := by
  let E :=
    jouanolouK0 F
      (rationalParamVar K :
        Fin m → RationalParamField K m)
  let e :=
    rationalParamTranslateRestrict F K b c

  have hfwd :
      IntermediateField.map e.toAlgHom E ≤ E :=
    map_jouanolouK0_translate_le F K b c

  have hinv :
      IntermediateField.map e.symm.toAlgHom E ≤ E := by
    rw [rationalParamTranslateRestrict_symm]
    exact map_jouanolouK0_translate_le F K (-b) c

  apply le_antisymm hfwd
  intro x hx
  have hxinvMap :
      e.symm x ∈ IntermediateField.map e.symm.toAlgHom E :=
    (IntermediateField.map_mem_map E e.symm.toAlgHom).2 hx
  have hxinv : e.symm x ∈ E :=
    hinv hxinvMap
  have hmem :
      e (e.symm x) ∈ IntermediateField.map e.toAlgHom E :=
    (IntermediateField.map_mem_map E e.toAlgHom).2 hxinv
  simpa using hmem

/-! ### Invariance of `K₂ = F(A,ξ,δ)` -/

/-- The directional coefficient vector, now regarded in `K`. -/
def scalarDirection
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (c : Fin m → F) :
    Fin m → K :=
  fun i => algebraMap F K (c i)

/-- The concrete `ξ` used in the translated tower. -/
noncomputable def translatedXi
    (K : Type*) [Field K]
    {m : ℕ}
    (g : Fin m → K) :
    RationalParamField K m :=
  rationalParamXi K g

/-- The concrete `δ = Σ c_i g_i`. -/
noncomputable def translatedDelta
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (c : Fin m → F)
    (g : Fin m → K) :
    RationalParamField K m :=
  rationalParamDelta K
    (scalarDirection F K c) g

/-- Exact translation rule for the concrete `ξ`. -/
theorem rationalParamTranslateRestrict_xi
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (g : Fin m → K) :
    rationalParamTranslateRestrict F K b c
        (translatedXi K g)
      =
    translatedXi K g +
      algebraMap F (RationalParamField K m) b *
        translatedDelta F K c g := by
  rw [rationalParamTranslateRestrict_apply]
  unfold translatedXi translatedDelta scalarDirection
  rw [rationalParamTranslateFieldEquiv_xi]
  simp [IsScalarTower.algebraMap_apply F K
    (RationalParamField K m)]

/-- `δ` is fixed. -/
@[simp] theorem rationalParamTranslateRestrict_delta
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (g : Fin m → K) :
    rationalParamTranslateRestrict F K b c
        (translatedDelta F K c g)
      =
    translatedDelta F K c g := by
  rw [rationalParamTranslateRestrict_apply]
  exact
    rationalParamTranslateFieldEquiv_delta
      K (algebraMap F K b)
      (scalarDirection F K c) g

/-- One translation maps `K₂` into itself. -/
lemma map_jouanolouK2_translate_le
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (g : Fin m → K) :
    IntermediateField.map
        (rationalParamTranslateRestrict F K b c).toAlgHom
        (jouanolouK2 F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g))
      ≤
    jouanolouK2 F
      (rationalParamVar K :
        Fin m → RationalParamField K m)
      (translatedXi K g)
      (translatedDelta F K c g) := by
  apply map_adjoin_le_of_forall_image_mem
  intro x hx
  rcases hx with hxA | hxPair
  · rcases hxA with ⟨i, rfl⟩
    change
      rationalParamTranslateRestrict F K b c
          (rationalParamVar K i) ∈
        jouanolouK2 F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g)
    rw [rationalParamTranslateRestrict_param]
    exact
      (jouanolouK2 F
        (rationalParamVar K :
          Fin m → RationalParamField K m)
        (translatedXi K g)
        (translatedDelta F K c g)).add_mem
        (jouanolouK2_param_mem
          F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g)
          i)
        ((jouanolouK2 F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g)).algebraMap_mem
          (b * c i))
  · simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hxPair
    rcases hxPair with rfl | rfl
    · change
        rationalParamTranslateRestrict F K b c
            (translatedXi K g) ∈
          jouanolouK2 F
            (rationalParamVar K :
              Fin m → RationalParamField K m)
            (translatedXi K g)
            (translatedDelta F K c g)
      rw [rationalParamTranslateRestrict_xi]
      exact
        (jouanolouK2 F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g)).add_mem
          (jouanolouK2_xi_mem
            F
            (rationalParamVar K :
              Fin m → RationalParamField K m)
            (translatedXi K g)
            (translatedDelta F K c g))
          ((jouanolouK2 F
            (rationalParamVar K :
              Fin m → RationalParamField K m)
            (translatedXi K g)
            (translatedDelta F K c g)).mul_mem
            ((jouanolouK2 F
              (rationalParamVar K :
                Fin m → RationalParamField K m)
              (translatedXi K g)
              (translatedDelta F K c g)).algebraMap_mem b)
            (jouanolouK2_delta_mem
              F
              (rationalParamVar K :
                Fin m → RationalParamField K m)
              (translatedXi K g)
              (translatedDelta F K c g)))
    · change
        rationalParamTranslateRestrict F K b c
            (translatedDelta F K c g) ∈
          jouanolouK2 F
            (rationalParamVar K :
              Fin m → RationalParamField K m)
            (translatedXi K g)
            (translatedDelta F K c g)
      rw [rationalParamTranslateRestrict_delta]
      exact
        jouanolouK2_delta_mem
          F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g)

/-- Hence `K₂` is preserved exactly by every translation. -/
theorem map_jouanolouK2_translate_eq
    (F K : Type*) [Field F] [Field K]
    [Algebra F K]
    {m : ℕ}
    (b : F)
    (c : Fin m → F)
    (g : Fin m → K) :
    IntermediateField.map
        (rationalParamTranslateRestrict F K b c).toAlgHom
        (jouanolouK2 F
          (rationalParamVar K :
            Fin m → RationalParamField K m)
          (translatedXi K g)
          (translatedDelta F K c g))
      =
    jouanolouK2 F
      (rationalParamVar K :
        Fin m → RationalParamField K m)
      (translatedXi K g)
      (translatedDelta F K c g) := by
  let E :=
    jouanolouK2 F
      (rationalParamVar K :
        Fin m → RationalParamField K m)
      (translatedXi K g)
      (translatedDelta F K c g)
  let e :=
    rationalParamTranslateRestrict F K b c

  have hfwd :
      IntermediateField.map e.toAlgHom E ≤ E :=
    map_jouanolouK2_translate_le
      F K b c g

  have hinv :
      IntermediateField.map e.symm.toAlgHom E ≤ E := by
    rw [rationalParamTranslateRestrict_symm]
    exact
      map_jouanolouK2_translate_le
        F K (-b) c g

  apply le_antisymm hfwd
  intro x hx
  have hxinvMap :
      e.symm x ∈ IntermediateField.map e.symm.toAlgHom E :=
    (IntermediateField.map_mem_map E e.symm.toAlgHom).2 hx
  have hxinv : e.symm x ∈ E :=
    hinv hxinvMap
  have hmem :
      e (e.symm x) ∈ IntermediateField.map e.toAlgHom E :=
    (IntermediateField.map_mem_map E e.toAlgHom).2 hxinv
  simpa using hmem

/-!
Stage-43 audit
--------------

Two bridges needed by the infinite-field Jouanolou proof are now internal.

1. The transcendence statements from Stage 42 pass from the polynomial
   parameter algebra `F[A]` to the field `K₀ = F(A)` using Mathlib's
   algebraic/fraction-field instance and `Transcendental.extendScalars`:

       `ξ` transcendental over `K₀`,
       `δ` transcendental over `K₀`.

2. The Stacks translations
       `A_i ↦ A_i + b c_i`
   with `b,c_i ∈ F` preserve exactly
       `K₀ = F(A_i)`
   and
       `K₂ = F(A_i,ξ,δ)`.

The exact action remains
       `σ_b(ξ)=ξ+bδ`,
       `σ_b(δ)=δ`.

The next missing step is no longer about the translation geometry.  It is the
finite-separable part of Stacks 37.32.1:

* prove the relative separable closure of `K₂` in `Ω` is finite over `K₂`;
* use finiteness of its intermediate-field lattice and infinitude of `F=ℂ`
  to find two distinct translations whose generated finite separable
  subfields coincide.

That is the target of Stage 44.
-/

end
end StrictStage2
end MazurOrlicz20_1
end PaperFormalization
