# Finite ordinary source moments: θ = 8747729897/10000000000

**Status: proved in the attached standalone manuscript; complete resumed Lean development compilation and final axiom audit passed; full independent exact-head replay pending.** Submitted by Hailey Collet, [@HaileyStormC](https://x.com/HaileyStormC), with substantial AI assistance.

## 1. Change

Replace the frozen final-section parameter search with an ordinary-source moment induction, an intermediate analytic return, then a selected feedback graph and final physical/Mellin return. The starting input is ArviFoxy's accepted two-level affine Hecke theorem, tracker PR #67, revision `0db497edc397d7076b1652b060e49c76b683e901`, boundary 174963413/200000000.

This is a separate complete proof route, not a proposed edit to one line of the preprint's `build/paper.tex`. Consequently there are no replacement line numbers in that file. The relevant comparison scope is the Part II moment/count/return chain covered by this repository's audit of lines 3723–16677. Precise new locations are the attached [sources](../../submissions/hailey-collet-1252270103/paper/sources.tex), [first return](../../submissions/hailey-collet-1252270103/paper/first-return.tex), [feedback](../../submissions/hailey-collet-1252270103/paper/feedback.tex), and [final return](../../submissions/hailey-collet-1252270103/paper/return.tex). The [foundations](../../submissions/hailey-collet-1252270103/paper/foundations.tex) and full paper supply the analytic context.

## 2. Exact statement and discharged inputs

For every positive integer q, every presented Dirichlet character χ modulo q, and every complex s,

`8747729897/10000000000 < Re(s)` and `¬(χ = 1 ∧ s = 1)` imply `L(χ,s) ≠ 0`.

This is `Candidate.bound` in the archived `src/Candidate/Main.lean`. The paper gives the finite-order Hecke theorem over Q(√−3) and the zeta consequence as well. No new source-existence or energy hypothesis appears in the final statement.

Starting from the accepted bound, weaken it to 87481891/100000000, giving natural cost 112445673/25000000. The 64 derived bootstrap faces and their return prove β ≤ 8747759/10000000. Then, and only then, use

`K = 6(2β − 1) ≤ 11243277/2500000`.

With this cost, the parent-closed graph of 222 nodes (natural node plus 221 derived faces) supplies the two ordinary moments for the final same-zero count and Mellin return. Exact coefficients, all exponent inequalities, admission intervals, complementary sectors and rational Bernstein certificates are printed in the paper and formalized in the used Lean closure. The [certificate section](../../submissions/hailey-collet-1252270103/paper/certificates.tex) and final return are the modified budget supplied for this route.

## 3. Payoff

The strict boundary is θ = **8747729897/10000000000 = 0.8747729897**, or c = **1252270103/10000000000**. The manuscript's result is unconditional, building on proved analytic inputs; it is separate from this repository's conditional H1–H5 nested-level proposals. Formal acceptance remains a separate pending check.

## 4. Evidence

The [submission package](../../submissions/hailey-collet-1252270103/README.md) contains the 138-page standalone paper, its complete TeX, all 6,471 used Lean modules with exact source/tool/package pins, source provenance and licenses, plus local process receipts and compiler output. The full closure was compiled across a clean 6,431-module prefix and a successful 40-module resumed completion. The separate final theorem audit exited zero with only `propext`, `Classical.choice`, `Quot.sound`. Finite scalar development checked 657 modules and 2,953 theorem/lemma audits; additional divisor-kernel and restoration components passed their stated checks.

A protected tracker attempt compiled 3,305 modules freshly and reused 2,923 authenticated cache entries before exhausting its shared three-hour budget. Complete fresh final replay and canonical Comparator plus Lean/NanoDa/con-ron endpoint acceptance are still pending. The attached verification summary distinguishes these scopes. No floating-point search is used as a substitute for a required certificate.

## 5. Affected proof interfaces

The standalone proof carries the ordinary two-factor coefficient, original full-zero filtering, natural-zero conventions, common punctures, root multiplicity, six-unit normalization, independent heights and shared profiles through source induction, exceptional-sector bounds, same-zero counting, physical restoration and the Mellin return. It retains primitive/imprimitive scope and excludes the principal pole. No change to `budget.py`, `certify.py`, the historical audit, or the existing Track A constants is required to read this contribution.

The paper's [attribution](../../submissions/hailey-collet-1252270103/paper/attribution.tex) gives original credits. [QRH-Catalogue](https://github.com/HaileyStorm/QRH-Catalogue), used extensively in this development, provides source-backed discovery and reuse links; it does not replace the proofs or their verification receipts.
