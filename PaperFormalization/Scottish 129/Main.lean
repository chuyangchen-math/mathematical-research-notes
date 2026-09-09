import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Nikliborc Problem 129 — strict logical layer

This file contains no `sorry`, no `axiom`, and no unproved theorem declaration.
It fully formalizes the cancellation argument in the paper:

    U_{Ω₂}(x) = d₂ + q(x) + h(x)
    U_{Ω₁}(x) = d₁ + q(x) + h(x)

on a nested pair Ω₁ ⊆ Ω₂, hence the shell potential

    U_A = U_{Ω₂} - U_{Ω₁}

is identically d₂ - d₁ on Ω₁.  It also includes the numerical specialization
`d₁ = 1/2`, `d₂ = 2`, giving `3/2` exactly.

The difficult analytic theorem producing smooth nested nonellipsoidal domains
with these interior-potential formulas is not postulated.  A complete
formalization of the original Problem 129 must formalize the obstacle problem,
free-boundary stability, Newtonian representation/uniqueness, and the
nonellipsoid criterion.
-/

namespace Nikliborc129

universe u

variable {Point : Type u}

/-- Potential of the shell obtained by subtracting the inner body's potential
from the outer body's potential. -/
def shellPotential (Uouter Uinner : Point → ℝ) (x : Point) : ℝ :=
  Uouter x - Uinner x

/--
Pure cancellation lemma: shared nonconstant terms cancel on the cavity.
-/
theorem shellPotential_constant_on_inner
    (Ωinner Ωouter : Set Point)
    (hNested : Ωinner ⊆ Ωouter)
    (Uinner Uouter q h : Point → ℝ)
    (dInner dOuter : ℝ)
    (hInner : ∀ x ∈ Ωinner, Uinner x = dInner + q x + h x)
    (hOuter : ∀ x ∈ Ωouter, Uouter x = dOuter + q x + h x) :
    ∀ x ∈ Ωinner,
      shellPotential Uouter Uinner x = dOuter - dInner := by
  intro x hx
  have hxOuter : x ∈ Ωouter := hNested hx
  rw [shellPotential, hOuter x hxOuter, hInner x hx]
  ring

/--
Specialization used in the manuscript: `d₁ = 1/2`, `d₂ = 2`, hence the shell
potential equals `3/2` throughout the cavity.
-/
theorem shellPotential_eq_three_halves
    (Ωinner Ωouter : Set Point)
    (hNested : Ωinner ⊆ Ωouter)
    (Uinner Uouter q h : Point → ℝ)
    (hInner : ∀ x ∈ Ωinner,
      Uinner x = (1 / 2 : ℝ) + q x + h x)
    (hOuter : ∀ x ∈ Ωouter,
      Uouter x = 2 + q x + h x) :
    ∀ x ∈ Ωinner,
      shellPotential Uouter Uinner x = (3 / 2 : ℝ) := by
  intro x hx
  have hconst := shellPotential_constant_on_inner
    Ωinner Ωouter hNested Uinner Uouter q h
    (1 / 2 : ℝ) 2 hInner hOuter x hx
  norm_num at hconst ⊢
  exact hconst

/--
A data package containing exactly the geometric and potential-theoretic facts
needed for the final counterexample deduction.
-/
structure ShellCounterexampleCertificate
    (AdmissibleBoundary : Set Point → Prop)
    (IsEllipsoid : Set Point → Prop) where
  inner : Set Point
  outer : Set Point
  nested : inner ⊆ outer
  Uinner : Point → ℝ
  Uouter : Point → ℝ
  q : Point → ℝ
  h : Point → ℝ
  innerFormula : ∀ x ∈ inner,
    Uinner x = (1 / 2 : ℝ) + q x + h x
  outerFormula : ∀ x ∈ outer,
    Uouter x = 2 + q x + h x
  innerAdmissible : AdmissibleBoundary inner
  outerAdmissible : AdmissibleBoundary outer
  innerNonellipsoid : ¬ IsEllipsoid inner
  outerNonellipsoid : ¬ IsEllipsoid outer

/--
The final negative-answer package extracted from a genuine analytic
certificate.  This theorem is fully proved and uses no unproved interface.
-/
theorem negative_answer_from_certificate
    (AdmissibleBoundary : Set Point → Prop)
    (IsEllipsoid : Set Point → Prop)
    (c : ShellCounterexampleCertificate AdmissibleBoundary IsEllipsoid) :
    ∃ Ωinner Ωouter : Set Point,
      Ωinner ⊆ Ωouter ∧
      AdmissibleBoundary Ωinner ∧
      AdmissibleBoundary Ωouter ∧
      ¬ IsEllipsoid Ωinner ∧
      ¬ IsEllipsoid Ωouter ∧
      (∀ x ∈ Ωinner,
        shellPotential c.Uouter c.Uinner x = (3 / 2 : ℝ)) := by
  refine ⟨c.inner, c.outer, c.nested,
    c.innerAdmissible, c.outerAdmissible,
    c.innerNonellipsoid, c.outerNonellipsoid, ?_⟩
  exact shellPotential_eq_three_halves
    c.inner c.outer c.nested
    c.Uinner c.Uouter c.q c.h
    c.innerFormula c.outerFormula

end Nikliborc129
