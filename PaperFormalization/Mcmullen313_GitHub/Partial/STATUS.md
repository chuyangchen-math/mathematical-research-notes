# Status of McMullen Question 3.13 Formalization

## Current status

The current Lean development provides a conditional formalization of the argument.

The verified core has been completed with explicit hypotheses and without hidden proof placeholders.

## Formalized components

The current development formalizes the logical consequences of the geometric hypotheses appearing in the main argument.

The Lean theorem statements isolate the necessary external geometric information and derive the corresponding periodicity conclusions.

## Remaining external inputs

The remaining mathematical components are explicit external inputs:

1. Leafwise Veech-type dichotomy.

2. Finite obstruction periodicity statement.

3. Horizontal parabolic-cylinder existence statement.

These statements are not encoded as hidden axioms. They are explicit assumptions of the conditional theorems.

## Verification boundary

The current status should be described as:

Conditional Lean formalization of the verified core.

A future complete formalization would require formalizing the remaining geometric inputs themselves.
