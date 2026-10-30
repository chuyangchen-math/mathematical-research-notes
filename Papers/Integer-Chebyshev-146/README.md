# Degree-146 integer Chebyshev manuscript: English edition

The English manuscript is dated October 30, 2026. Its mathematics and computational data are based on certificate version v2, verified locally on October 25, 2026. This translation is not an independent audit.

## Files

- `main.tex`: English LaTeX source.
- `chebyshev146-en.pdf`: compiled English paper.
- `certificates/`: exact certificate data, Python verifiers, original execution records, pinned dependencies, and a checksum manifest.
- `REVIEW_INSTRUCTIONS.md`: an English task for an independent reviewer.

## Compile the paper

Run XeLaTeX twice in this directory:

```text
xelatex -interaction=nonstopmode -halt-on-error main.tex
xelatex -interaction=nonstopmode -halt-on-error main.tex
```

The compiler produces `main.pdf`; the supplied copy is named `chebyshev146-en.pdf`. The source uses standard LaTeX packages and does not require Chinese fonts. It is also intended to be compatible with pdfLaTeX; the delivered PDF was compiled with XeLaTeX.

## Check the mathematics

First read `REVIEW_INSTRUCTIONS.md`. In a copy of `certificates/`, install `requirements.txt`, then run:

```text
python verify146_complete.py
python crosscheck146_v2.py
```

Do not use `python -O`. Verify hashes before execution: some result files are rewritten when programs run. The original environment was Python 3.12, SymPy 1.14.0, NumPy 2.5.4.

The supplied local verification records are not independent-review results. No external audit, formal proof-assistant verification, or priority claim is asserted. No author name or affiliation has been assigned on the user's behalf.
