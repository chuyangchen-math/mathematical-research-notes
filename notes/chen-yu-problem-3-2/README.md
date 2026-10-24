# Spin Parity and Period Obstructions — Lean development

**Conditional formalization of the internal arguments, with explicit standard external inputs.**

This accompanies the supplied research note on Chen–Yu Problem 3.2. It is about quadratic differential strata, not Scottish Book Problem 3.2.

- `Main.lean`: entry point and final axiom audits.
- `STATUS.md`: theorem-to-file map and precise scope.
- `EXTERNAL_INPUTS.md`: standard results, coordinate interfaces, and assumption audit.
- `VALIDATION.md`, `logs/current/`: recorded local verification.
- `Verify.ps1`: Lake build and entry-point check.

The development constructs the section isomorphisms, local pole bounds, anti-invariant exactness, period quotient and kernel comparison, residual cubic argument, and the resulting exceptional-component criterion. The genus-four criterion is restricted to the non-hyperelliptic regular/irregular locus.

Riemann–Roch, ordinary Mittag–Leffler and global primitive theorems, the canonical-cover/germ interface, and the Chen–Möller component theorem are explicit inputs. Concrete compact Riemann surfaces and their analytic realization are not constructed here. See the input registry before interpreting a checked theorem as a geometric claim.

The original finite-basis Main.lean is not imported or republished as the new proof. No independent human mathematical or statement-correspondence review is recorded.

## Build

With Lean's elan/Lake tools installed, open PowerShell in this directory:

```powershell
lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Dependency setup failed' }
./Verify.ps1
```

The toolchain and Mathlib revision are pinned in lean-toolchain, lakefile.toml, and lake-manifest.json. This recipe is distinct from the local cached-dependency verification actually recorded in VALIDATION.md.
