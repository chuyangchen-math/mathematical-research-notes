# Machine-Assisted Mathematical Research Notes

This repository contains AI-assisted mathematical research notes and companion Lean formalizations for selected problems from the Scottish Book.

## Review status

> **No independent human mathematical review has been performed.**

These notes should be treated as exploratory mathematical records rather than independently verified mathematical results.

## AI generation

**AI-generation coordinators and contacts**

- Chuyang Chen — 22535018@zju.edu.cn
- Chenhao Bian — bch26@mails.tsinghua.edu.cn

Mathematical drafts were generated with **GPT-5.6 Sol** under their supervision.

## Lean verification

Some notes have accompanying Lean formalizations.

**Successful Lean verification establishes correctness of the formalized statement relative to its assumptions. It does not by itself establish that the formalized statement is exactly equivalent to the historical problem as originally formulated.**

Recorded environment:

- Lean: `4.33.1`
- Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- mathlib: `v4.33.1`
- exact mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`

## Notes

| Problem | Mathematical status | Formal verification |
|---|---|---|
| [45](notes/problem-45/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | F1 |
| [125](notes/problem-125/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | F1 |
| [128](notes/problem-128/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | Conditional F1; full-paper formalization partial |
| [129](notes/problem-129/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | Conditional F1; full-paper formalization partial |
| [150](notes/problem-150/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | Conditional F1 |
| [164](notes/problem-164/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | F1 |
| [165](notes/problem-165/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | F1 |
| [174](notes/problem-174/) | E1 — AI cross-checked; **NOT HUMAN VERIFIED** | F1 for a related real-scalar formal counterexample |

## Acknowledgments

Chuyang Chen and Chenhao Bian are grateful to their advisor, Fei Yu, for his guidance on this project.

## Publication status

First public release: **2026-09-15**

Current version: **v1.0**



## McMullen Question 3.13

| Project | Paper | Lean formalization | Status |
|---|---|---|---|
| McMullen Question 3.13 | [PDF](PaperFormalization/Mcmullen313_GitHub/McMullen313.pdf) | [Lean](PaperFormalization/Mcmullen313_GitHub/McMullen313.lean) | Conditional formalization with explicit external geometric inputs |

The McMullen 3.13 project contains a Lean 4 formalization of the verified core of the argument.

The formalization isolates geometric assumptions as explicit external inputs rather than hidden axioms. The Lean development verifies the corresponding consequences under these stated assumptions.

Files:

- [Lean source](PaperFormalization/Mcmullen313_GitHub/McMullen313.lean)
- [Paper PDF](PaperFormalization/Mcmullen313_GitHub/McMullen313.pdf)
- [Verification records](PaperFormalization/Mcmullen313_GitHub/Logs/)
- [Formalization status](PaperFormalization/Mcmullen313_GitHub/Partial/STATUS.md)



## Chen–Yu Problem 3.2 — Quadratic differential strata

[Paper and Lean development](notes/chen-yu-problem-3-2/index.md). Conditional F1: internal proofs with explicit standard external inputs. See the theorem map, input registry, and verification record. No independent human review is recorded.
