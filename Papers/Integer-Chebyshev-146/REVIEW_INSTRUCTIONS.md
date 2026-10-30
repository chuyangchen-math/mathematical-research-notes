# Independent review task

Review this claimed computer-assisted solution independently. Treat the mathematical claims, stored results, and printed PASS/PROVED messages as claims to test, not as evidence sufficient by themselves. Preserve the original files and run programs on a copy because they rewrite some results.

The claim is that, among all nonzero integer polynomials of degree at most 146 on [0,1], the unique minimizers up to sign are P(x)=Q(x(1-x)), where

Q(t) = t^46 (1-4t)^8 (1-5t)^6 (29t^2-11t+1)^2
       (941t^4-703t^3+193t^2-23t+1)
       (-4921t^5+4594t^4-1697t^3+310t^2-28t+1).

The claimed norm is approximately 8.31346358662477797985373396968e-55. Its exact algebraic specification and rational bounds are in the paper and the final norm certificate.

## Reproduce and inspect

1. Read the complete English paper and draw its logical dependency graph.
2. Verify the file checksums before running anything. Checksums establish identity, not correctness.
3. Install the listed dependencies in an isolated environment. Run `verify146_complete.py` and `crosscheck146_v2.py` without Python's `-O` option. Record the actual environment and full outputs.
4. Inspect the mathematical-to-program correspondence rather than only rerunning assertions.

## Required mathematical checks

- Does the initial candidate rigorously have norm below U=8.39524760655209405080e-55? Does this justify restricting all potential competitors to norm at most U?
- Check the rescaling of the high-order Markov inequality, factorial normalization, resultant leading-coefficient exponents, and derivation of factor multiplicities. Include polynomials whose actual degree is less than 146.
- Check all 35 interpolation steps: node counts, distinctness, nonvanishing denominators, completeness of root intervals, and strict inequalities. Reflection bounds must not assume the unknown polynomial is symmetric.
- Check primitivity, the integer quotient, the residual degree bound, and the identity F(x)=W(x(1-x)).
- Independently derive q(x)=A(t)+xB(t) with integer coefficients and degrees at most 16 and 15. Check the reflected difference and its bound 2U. No degree-145 optimality theorem is allowed to fill a gap.
- Check that both basis matrices are unimodular and cover all integer remainders. Reconstruct the exact evaluation numerators and denominators directly from the weighted polynomials.
- Check that the Gram and ellipsoid constraints are necessary, that G-J is positive semidefinite, and that J is positive definite. Verify the inverse-matrix coordinate bounds and rounding directions.
- Check that rounded point constraints only enlarge the possible set, including equality and half-integer thresholds.
- Audit LDL factorization, recursive coordinate ranges, Cauchy--Schwarz pruning, floating-point screening, shared mutable state, and fixed-width integer overflow. Every exclusion decision must be justified exactly.
- Confirm the alleged surviving sets are recomputed. Verify that the candidate vectors, residual polynomials, and factorizations agree identically.
- Check the final norm certificates against all endpoints and derivative roots, including roots of known factors. Verify root counts, interval arithmetic, strict norm comparisons, and the uniqueness conclusion.

## Independence

The crosscheck disables early point-constraint pruning but shares the certificate data, some mathematical constructions, and libraries with the main verifier. It is not a wholly independent implementation. At minimum, independently rederive and implement important checks, such as the evaluation embeddings, enumeration boundaries, or norm certification. If resources allow, implement the enumeration differently. Merely renaming variables in a copied verifier does not provide independence.

## Report

Start with one of: a fatal gap was found; no gap was found within the checks performed; or insufficient evidence to decide. Then list the actual checks, any defects with exact locations and mathematical consequences, independently rebuilt components, and remaining trust assumptions. Provide a minimal counterexample or failing assertion where possible. Do not equate failure to install a dependency with a mathematical counterexample, or successful assertions with a formal proof.

The purpose is to assess correctness. Establishing historical priority is outside the scope of this review.
