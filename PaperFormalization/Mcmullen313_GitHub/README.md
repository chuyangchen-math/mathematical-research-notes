# McMullen Question 3.13 Lean Formalization

This repository contains a Lean 4 formalization of the verified core of the argument for McMullen's Question 3.13.

## Formalization status

The current development is a conditional formalization.

The algebraic and combinatorial core of the argument has been formalized in Lean. Several geometric ingredients are isolated as explicit external inputs rather than hidden assumptions.

The remaining external inputs include:

- leafwise Veech-type input;
- finite obstruction periodicity input;
- horizontal parabolic-cylinder input.

These inputs appear as explicit hypotheses in the Lean statements. They are not introduced through hidden axioms or unverified proof placeholders.

The verified Lean theorems establish the corresponding periodicity conclusions from these stated geometric hypotheses.

## Verification

- Lean version: leanprover/lean4:v4.35.0-rc3
- No `sorry` placeholders in the formalized development
- No hidden proof placeholders introduced by the formalization layer

## Repository structure

- `McMullen313.lean` — main Lean formalization
- `Auxiliary/` — supporting formalizations
- `Logs/` — verification records
- `Partial/` — current mathematical status

## Scope

This repository does not claim that the original mathematical theorem has already been completely formalized without external inputs.

Instead, it provides a verified Lean framework in which the remaining geometric statements are explicitly identified.
