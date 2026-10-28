# Independent Lean audit of PRs #1–#28 (October 2026)

Status as of 28 October 2026: **PRs #23 and #28 pass in full.** The other 18 non-Lean PRs (#1–#3, #5–#7, #11–#15, #17, #19, #20, #24–#27) replay cleanly. **PR #8's fresh rebuild is 82% complete with no proof errors so far; PR #9 is reconstructed and queued.** This PR will be updated when those two finish.

All 23 PRs on GitHub show as closed. Each was merged into `main` by a manual merge commit. Five of them carry Lean: #8, #9, #10, #23 and #28.

## Environment

- Fresh Linux sandbox with 2 vCPU and 7.8 GB RAM, starting from no compiled objects.
- The Mathlib cache hosts were unreachable, so Mathlib and every dependency were **compiled from source** at the pinned commits.
- Lean v4.31.0 and v4.34.1 came from the official GitHub release archives. The v4.34.1 SHA-256 is `47bf4bbd…e4e4`, which matches `.github/workflows/lean-tau-comparator.yml`.
- Every build used the committed `lake-manifest.json`. `lake update` was never run.

## Checks applied to each Lean PR

1. `lake build` from source.
2. **An all-declarations axiom audit** ([`audit_all_decls.sh`](audit_all_decls.sh)). This script was written for this audit. It enumerates *every* constant in the PR's modules, not just the ones the author lists, runs `Lean.collectAxioms` on each, and flags anything outside `propext`, `Classical.choice` and `Quot.sound`. A planted module containing `sorry`, a custom `axiom` and `native_decide` was correctly flagged on all three.
3. The author's own audit files and negative controls.
4. `leanchecker --fresh`, which replays the module and all imported declarations in an empty kernel environment.

## Results

| PR | Lean | Build | Axioms (all declarations) | Author audit / controls | Kernel replay | Verdict |
|---|---|---|---|---|---|---|
| #28 inverse slot capacity (S. Das) | `QRHResearch`, Lean 4.34.1, Mathlib `d13f23b` | exit 0, 1,537 jobs | 25 declarations, 20 theorems, 0 non-standard | `AxiomAudit.lean`: 19/19 standard. `NegativeControls.lean` fails as required (3 linarith errors) | `leanchecker --fresh QRHResearch` exit 0 (2 min 42 s) | **Pass** |
| #23 structural budget lemmas (S. Thakrar) | `BudgetLemmas`, `Audit`, Lean 4.31.0, Mathlib v4.31.0; `SHA256SUMS` OK | exit 0 | 70 declarations, 55 theorems, 0 non-standard | All 31 `#guard_msgs` axiom guards and 8 concrete checks pass | `leanchecker --fresh --verbose Audit` exit 0 (2 min 13 s) | **Pass** |
| #8 standalone endpoint θ = 8747729897/10¹⁰ (H. Collet) | 6,471 candidate modules, Lean 4.34.1 | **In progress:** 5,337/6,471 candidate modules built, no proof errors | Every compiled module's printed axiom report so far lists only the three standard axioms | See below | Pending | Pending |
| #10 earlier replay record for #8 | wrapper + evidence | Covered by this audit's own target and replay of #8 | | | | Covered by #8 |
| #9 Track A point 139999/160000 | external Argonaut overlay + `apply_tau.py` | Queued after #8 | | | | Pending |

Logs: [`logs/`](logs/).

### PR #8: checks completed

- **Provenance.** All 6,471 `.lean` files in `lean-sources.zip` are byte-identical to the frozen tracker revision `HaileyStorm/QuasiRiemannTracker@ac76d5ef`. `check_bundle.py` passes.
- **Patches.** The PrimeNumberTheoremAnd and rellich-kondrachov Lean 4.34.1 patches were re-downloaded from the tracker revision. They are identical to `verification/pr8-independent/dependency-patches/`, and the applied diffs hash to the recorded `diff_sha256` values (`45c98e…`, `0c121d…`).
- **Statement.** The tracker's canonical challenge `verifier/upstream-challenge.lean` has SHA-256 `8fb13ad9…`, which equals `challenge_sha256` in `toolchain/pins.json`. [`pr8/Target.lean`](pr8/Target.lean) restates it at the PR #8 boundary, importing only `Mathlib.NumberTheory.LSeries.DirichletContinuation`. [`pr8/Endpoint.lean`](pr8/Endpoint.lean) must close it with `Candidate.bound` and derive the ζ corollary. Both files are independent of PR #10's wrapper.
- **Build log.** The 57 failures in the log all come from a disk-full interruption, on Mathlib modules; those were rebuilt successfully afterwards. No compiled module has reported a Lean error.
- **Why it is slow.** On 7.8 GB of RAM, each deep module re-reads about 4 GB of imported `.olean` files (about 45 s per module), so the last ~1,100 modules will take several more hours.

### PR #9: reconstruction completed

- Argonaut `Lean_Proof_Source.zip` SHA-256 is `37602f93…5a93`.
- All 12,055 overlay files match `SOURCE-MANIFEST.json`. The dependency files are byte-identical to the pinned clones. This used [`pr9_reconstruct.py`](pr9_reconstruct.py), a reimplementation of the reviewed `reconstruct.py`.
- All 42 dependencies were fetched at their pinned revisions, with the overlay's Lean 4.34.1 patches applied ([`pr9_deps.py`](pr9_deps.py)).
- `apply_tau.py` makes numeral-only changes (51 lines) and reproduces PR #9's recorded `PerturbedBoundaryMain.lean` SHA-256, `aa22e3cd…7a18`.
- **Not reproducible from this repository alone:** the Lean sources are external.

## Non-Lean PRs

Every documented certificate command was re-run at the PR head and on `main`, and each exits 0. Outputs are byte-identical to committed logs where they exist, otherwise they match the documented transcripts. See [`logs/non-lean-replays-INDEX.txt`](logs/non-lean-replays-INDEX.txt), which lists each command, exit code and runtime.

| PR | Claim | Replay |
|---|---|---|
| #1, #2, #3, #6 | conditional θ bounds on H1–H5 (e.g. 0.874810282, 0.874809989, 0.874809963, 0.874807887) | `depth3/certify_*.py`: byte-identical |
| #5, #7, #11 | analysis / docs / chart | no checkable claim; scripts reproduce |
| #12, #13, #20 | Track A N = 5824 and near-edge 4374785349/5·10⁹ | `certify.py`, the audit and edge scripts, and an independent Node BigInt replay all agree exactly |
| #14, #15, #17, #19, #24 | exact limit lemmas | each script exits 0; all exact checks pass |
| #25 | early analytic audit | runs, but its checks are mostly illustrative |
| #26, #27 | conditional Track B θ = 0.87477137 / 0.87477128 | finite certificates replay identically; **no Lean endpoint** |

## Issues found

1. **Root `certify.py` always exits 0, even on failure** (for example `certify.py 3000 405967/500000` prints `False` and returns rc=0). Automation must parse its `True`/`OK` lines.
2. `depth3/__pycache__/*.pyc` is committed on `main`.
3. PR #9's "Lean-verified" result has no Lean source in this repo; it depends on Argonaut's external release.
4. The θ values of PRs #1–#3, #6, #26, #27 and #28's adaptive caps are **not** Lean results. The #28 Lean development proves supporting algebraic lemmas (Lemma S takes Heath-Brown's large sieve as a hypothesis), not a zero-free region.
5. The `pr/1` ref points at PR #2's merge commit.

Prepared by Rohan Arun with Claude (AI-assisted).
