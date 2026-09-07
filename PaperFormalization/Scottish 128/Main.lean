import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

/-!
# Nikliborc Problem 128 — strict logical layer

This file contains no `sorry`, no `axiom`, and no unproved theorem declaration.
It formalizes the final deduction used in the paper:

* an admissible body whose interior Newtonian potential is polynomial,
* whose potential has a genuinely higher-than-quadratic part,
* cannot be an ellipsoid once one knows that ellipsoids have no such term.

The analytic existence of the Yuan–Liu polynomial inclusion is intentionally
NOT postulated here.  A complete formalization of the original Problem 128
must prove that existence theorem in Lean (together with the required
Newtonian-potential regularity theory).
-/

namespace Nikliborc128

universe u v

variable {Point : Type u} {Body : Type v}

/- Abstract interior Newtonian potential. -/
variable (potential : Body → Point → ℝ)

/- The geometric/topological hypotheses required by the printed problem. -/
variable (Admissible : Body → Prop)

/- Predicate saying that a body is an ellipsoid. -/
variable (IsEllipsoid : Body → Prop)

/- Predicate saying that a function is a polynomial on the interior. -/
variable (IsPolynomial : (Point → ℝ) → Prop)

/- Predicate recording the presence of a genuine term of degree `> 2`. -/
variable (HasDegreeGTTwo : (Point → ℝ) → Prop)

/-- A concrete polynomial-inclusion certificate sufficient for Problem 128. -/
structure PolynomialInclusionCertificate where
  body : Body
  admissible : Admissible body
  polynomialPotential : IsPolynomial (potential body)
  higherTerm : HasDegreeGTTwo (potential body)

/--
The exact short deduction used in the paper: if every ellipsoid has interior
potential of degree at most two, then a polynomial inclusion with a genuine
higher term is not an ellipsoid.
-/
theorem certificate_is_nonellipsoidal
    (ellipsoid_has_no_higher_term :
      ∀ Ω : Body, IsEllipsoid Ω → ¬ HasDegreeGTTwo (potential Ω))
    (c : PolynomialInclusionCertificate potential Admissible IsPolynomial HasDegreeGTTwo) :
    ¬ IsEllipsoid c.body := by
  intro hEll
  exact (ellipsoid_has_no_higher_term c.body hEll) c.higherTerm

/--
A formally closed counterexample statement, conditional only on an actual
certificate object.  There are no hidden axioms in this theorem.
-/
theorem negative_answer_from_certificate
    (ellipsoid_has_no_higher_term :
      ∀ Ω : Body, IsEllipsoid Ω → ¬ HasDegreeGTTwo (potential Ω))
    (c : PolynomialInclusionCertificate potential Admissible IsPolynomial HasDegreeGTTwo) :
    ∃ Ω : Body,
      Admissible Ω ∧
      IsPolynomial (potential Ω) ∧
      ¬ IsEllipsoid Ω := by
  refine ⟨c.body, c.admissible, c.polynomialPotential, ?_⟩
  exact certificate_is_nonellipsoidal
    potential Admissible IsEllipsoid IsPolynomial HasDegreeGTTwo
    ellipsoid_has_no_higher_term c

/--
Equivalent negation of the universal assertion "every admissible polynomial
inclusion is an ellipsoid".
-/
theorem not_every_polynomial_inclusion_is_ellipsoid
    (ellipsoid_has_no_higher_term :
      ∀ Ω : Body, IsEllipsoid Ω → ¬ HasDegreeGTTwo (potential Ω))
    (c : PolynomialInclusionCertificate potential Admissible IsPolynomial HasDegreeGTTwo) :
    ¬ (∀ Ω : Body,
        Admissible Ω →
        IsPolynomial (potential Ω) →
        IsEllipsoid Ω) := by
  intro hUniversal
  have hEll : IsEllipsoid c.body :=
    hUniversal c.body c.admissible c.polynomialPotential
  exact (certificate_is_nonellipsoidal
    potential Admissible IsEllipsoid IsPolynomial HasDegreeGTTwo
    ellipsoid_has_no_higher_term c) hEll

end Nikliborc128
