# Mathematical Research Notes

This repository contains formalized mathematical research notes, Lean 4 developments, and verification records.

## Projects

### Scottish Book Problems

Formalizations and verification records for selected Scottish Book problems.

### McMullen Question 3.13

Location:

`PaperFormalization/Mcmullen313_GitHub/`

This directory contains a Lean 4 formalization of the verified core of the argument for McMullen's Question 3.13.

## Formalization status

The current McMullen 3.13 development is a **conditional formalization**.

The algebraic and combinatorial core of the argument has been formalized in Lean. Several geometric ingredients are isolated as explicit external inputs rather than hidden assumptions.

The remaining external inputs include:

- leafwise Veech-type input;
- finite obstruction periodicity input;
- horizontal parabolic-cylinder input.

These inputs appear as explicit hypotheses in the Lean statements. They are not introduced through hidden axioms or unverified proof placeholders.

The verified Lean theorems establish the corresponding periodicity conclusions from these stated geometric hypotheses.

## Verification

For McMullen Question 3.13:

- Lean version: `leanprover/lean4:v4.35.0-rc3`
- No `sorry` placeholders in the formalized development
- External geometric assumptions are explicitly isolated

## Repository structure

- `PaperFormalization/Mcmullen313_GitHub/`
  - `McMullen313.lean` — main Lean formalization
  - `Auxiliary/` — supporting formalizations
  - `Logs/` — verification records
  - `Partial/STATUS.md` — current formalization status

## Scope

The McMullen 3.13 repository provides a verified Lean framework for the formalized core. It does not claim that all geometric inputs have already been formalized inside Lean.


## Chen–Yu Problem 3.2 — Quadratic differential strata

[Paper and Lean development](notes/chen-yu-problem-3-2/index.md). Conditional F1: internal proofs with explicit standard external inputs. See the theorem map, input registry, and verification record. No independent human review is recorded.
