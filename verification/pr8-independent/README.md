# Independent replay of hillclimb PR #8

This directory records an AI-assisted independent verification attempt against the
frozen source revision `ac76d5ef6008d976a7b8f3c1d921af2317e79ce9`, submitted in
[hillclimb PR #8](https://github.com/rohanarun/quasi-rh-hillclimb/pull/8) and
[tracker PR #69](https://github.com/GTimG/QuasiRiemannTracker/pull/69).
The candidate sources are unchanged. Original authorship and licensing remain
with Hailey Collet and the credited upstream contributors.

## Result: passed on October 22, 2026

The complete native Lean 4.34.1 replay finished with process exit zero at
`2026-10-22T05:53:58.708165+00:00` (01:53 EDT). All **6,471 submission and baseline
modules compiled fresh**, with no candidate object cache. The independently
compiled canonical target matched `Candidate.bound`; both endpoint axiom audits
reported only `propext`, `Classical.choice`, and `Quot.sound`. Lean's
`leanchecker --fresh --verbose IndependentEndpoint` then exited zero after
1,808.597 seconds. The complete source-build-and-replay run took approximately
2 hours 55 minutes, excluding environment setup.

The final source hashes are unchanged. All 6,471 source/log/object/receipt
bindings passed an independent consistency audit, and regenerating the canonical
target produced byte-identical output. The six additional printed source endpoint
audits, including Hecke and zeta nonvanishing, likewise list only the same three
standard axioms; these imported declarations were included in the fresh kernel
replay. The separate canonical statement comparison is for the all-moduli
Dirichlet endpoint.

Evidence: [final result](replay-result.json), [canonical endpoint and axiom output](endpoint.log),
[kernel output](kernel-replay.log), [source compilation audit](compilation-audit.json),
[all compiler receipts](compile-receipts.jsonl), [all compiler logs](compiler-logs.zip),
[supplemental endpoint audits](supplemental-endpoints.json), and
[canonical target reproduction](canonical-recheck.json).

This establishes the submitted Lean endpoint at the frozen source revision.
Tracker Comparator/NanoDa/con-ron admission remains pending. The native replay
does not claim that separate admission or an independent line-by-line
formalization audit of the entire manuscript.

## Checked before the replay

- The bundled integrity checker passed all 6,471 source hashes, package hashes,
  and 41 archived receipt/log bindings. This checks the submitted evidence's
  integrity; it does not independently establish its proof claims.
- `source-equivalence.json` compares every archived Lean source with the Git blob
  at the frozen tracker revision: all 6,471 match.
- All 20 package source revisions match the pinned manifest. The only applied
  changes are the tracker's published Lean 4.34.1 compatibility patches for
  PrimeNumberTheoremAnd and rellich-kondrachov, copied here for inspection.
- The official cache for the pinned Mathlib dependency was downloaded. The two
  additional package import targets compiled successfully.
- `IndependentTarget.lean` was compiled before loading candidate sources. It
  defines the all-positive-moduli Dirichlet nonvanishing proposition at the exact
  rational boundary `8747729897/10000000000`, excluding the principal pole.
- The repository's existing `certify.py` passes. This is only a baseline check;
  it does not certify PR #8.

## Replay procedure and evidence

`replay_local.py` checks source hashes against the supplied inventory, derives
the import graph, and requires that the 6,471 inventoried modules are exactly
the closure of `Candidate.Main`. It starts without existing candidate or
baseline objects, compiles each module after its imports have exited zero,
and records a source hash, object hash, log hash, elapsed time and process exit
code for every module. Official Mathlib dependency objects are reused.

After compilation, `IndependentEndpoint.lean` must prove the separately compiled
target using `Candidate.bound`. Both theorem axiom audits must contain only
`propext`, `Classical.choice`, and `Quot.sound`. Finally,
`leanchecker --fresh --verbose IndependentEndpoint` replays imported and newly
defined constants in an empty Lean kernel environment. This is Lean's own kernel
replay, not a separate external kernel implementation.

`run-identity.json` binds the source inventory, replay driver, canonical target,
endpoint wrapper and local Lean/checker executables by SHA-256. The approved
runtime directory is `/Users/rohanarun/LocalBuilds/quasi-rh-pr8`, outside iCloud.
The user explicitly authorized this exception to their SSD-only policy because
the external volume lacked enough free space for the build.

The successful verdict above comes from the final process exits and independent
evidence checks, not from partial module counts or the author's archived receipts.
Full tracker Comparator, NanoDa and con-ron acceptance is a separate outstanding
check. This native macOS run does not claim tracker admission or the Linux
Palomar sandbox's security properties, and does not establish that every
sentence in the accompanying manuscript has been formalized.

## Comparison chart

`auto-research/plot_pr8_comparison.py` reads the saved live tracker catalogue and
submission metadata. It ranks exact fractions and keeps accepted tracker records
distinct from the new independent native Lean result. Without a successful
replay receipt, the chart explicitly says verification is pending.

The comparison snapshot has 26 accepted tracker entries. Its strongest boundary
is Zhongpai Gao's `8748087/10000000`; PR #8 claims `8747729897/10000000000`.
The difference is exactly `357103/10000000000`. Relative to the accepted record's
improvement beyond `7/8`, the additional improvement is about 18.7%. That
percentage is not a reduction of 18.7% in the boundary itself.

The chart is scoped to these cited sources. It does not assert a worldwide record.

Regenerate the verified chart from the retained snapshot:

```sh
python3 -B auto-research/plot_pr8_comparison.py \
  --replay verification/pr8-independent/replay-result.json
```
