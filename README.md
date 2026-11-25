# Paper 1: Prefix Stabilizer Maxima, Recursive Coset Orderings, and Escape Deficits in Finite Groups

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_prefix_stabilizers.py` — Standalone Python 3 (stdlib only) verifier reproducing all small-group maxima, labeled counts, the `C12` non-nested witness, Stanley connectivity double count, dihedral DP counts, and the `F7 x| C3` Vosper escape count.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).
2. Edit `\author`, `\email`, and `\address` at the top of `main.tex` if desired.

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `math.GR` (Group Theory)
- **MSC 2020:** Primary `05E16`, `20D60`; Secondary `05A05`, `11B30`, `20D15`
- **Target journals (zero-fee):** *Electronic Journal of Combinatorics*, *Enumerative Combinatorics and Applications*, *Australasian Journal of Combinatorics*.

## Verify Computations
```bash
python3 verify_prefix_stabilizers.py
```
