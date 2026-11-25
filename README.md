# Paper 1: Prefix Stabilizer Maxima, Recursive Coset Orderings, and Escape Deficits in Finite Groups

**Authors:** Daniyar Kuttymbek, Adilkhan Kuttymbek, Amina Kolpenova, Mukhammadali Kottumbekov, and Dayana Kuttymbek

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `PrefixStabilizers.lean` — Zero-dependency Lean 4 formal verifier (uses Lean 4 core `Init` only, zero `sorry`, zero `native_decide`, pure kernel reduction; verified with Lean 4.36.0).
- `verify_prefix_stabilizers.py` — Standalone Python 3 (stdlib only) verifier reproducing all small-group maxima, labeled counts, the `C12` non-nested witness, Stanley connectivity double count, dihedral DP counts, and the `F7 x| C3` Vosper escape count.
- `LICENSE` — MIT License.

## How to Verify
### 1. Lean 4 formal verification (zero dependencies)
```bash
lean PrefixStabilizers.lean
```
Machine-checks:
- **Abstract group theory (all groups `G`):** Lemma 2.1 (free left action, subgroup property of `Stab_G(S)`, complementation invariance, right-translation invariance), Lemma 3.1 (local stabilizer inclusion `H_j <= L_j`), Lemma 3.2 (normal partial-block localization), Lemma 4.1 (accumulated coset containment `B_j x_1 <= T_j` and `B_{m-1} < G`), Theorem 1.2(c) (unique top-subgroup recovery `K = <H_1, ..., H_{m-1}>`).
- **Symbolic arithmetic & combinatorics (all primes `p`, `a >= 1`, `m`):** Theorem 1.3 (`sum_{j=1}^{p^a} (gcd(j, p^a) - 1) = a(p-1)p^{a-1}`), Section 11.1 (Stanley connectivity double count), Theorem 1.5 (escape-deficit identity).
- **Pure-kernel finite certificates (`decide` / `decide +kernel`, zero `native_decide`):** Example 7.1 (`C12` witness), Proposition 8.1 (`S3` subset DP + all 720 labeled permutations: 360 total, 216 hierarchical, 144 nonhierarchical), exact DP for `C1..C4`, `C2xC2`, `C6`, `C8`, `Q8`, `D8`, cyclic recurrence `C4..C12`, Table 1 dihedral DP (`D6`, `D10`, `D14`), `F7 x| C3` counts, and Vosper mean exclusion in `F7`.

### 2. Python standalone verification
```bash
python3 verify_prefix_stabilizers.py
```

## How to Compile PDF
Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `math.GR` (Group Theory)
- **MSC 2020:** Primary `05E16`, `20D60`; Secondary `05A05`, `11B30`, `20D15`
- **Target journals (zero-fee):** *Electronic Journal of Combinatorics*, *Enumerative Combinatorics and Applications*, *Australasian Journal of Combinatorics*.
