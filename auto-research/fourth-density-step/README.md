# Fourth density step: exact scalar candidate at 0.873981

This AI-assisted research bundle builds on Rohan Arun's and Sil's density-split
work in [tracker PR84](https://github.com/GTimG/QuasiRiemannTracker/pull/84), pinned
to `71996e7e79840455f7beead063a73b7b31cfb586`. All mathematical implications remain
conditional on the preprint's seven-eighths theorem. This bundle contains the
exact finite scalar receipts; their formal integration is in
[tracker PR #85](https://github.com/GTimG/QuasiRiemannTracker/pull/85).
The tracker's [proof verification](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/40622628467)
accepted the exact PR head with the canonical Comparator and all three kernels.
Review and merge remain pending.

The certified boundary is `theta = 873981/1000000 = 0.873981`, using PR84's
original `h = 16109/20000 = 0.80545`. It is `1/250000 = 0.000004` below PR84's
`174797/200000 = 0.873985`. The Lean proof supplies the source and return
assembly described below and excludes the principal character's pole.

## Reproduce

From this directory, with Python and SymPy installed:

```sh
python3 replay.py
python3 verify_source_receipt.py
python3 verify_return_receipt.py
```

`replay.py` checks the 33 upstream source snapshots against their Git blob IDs,
then regenerates the exact source, return, and ablation receipts. It takes about
four seconds in the research environment. All paths are relative to the script
directory. Do not use `python -O`; the replay rejects disabled assertions.
The two independent receipt verifiers use a separate Bernstein basis solver.

`source-pins.json` contains upstream URLs, commit and blob pins, and SHA256 hashes.
The copied Lean source retains its original attribution and Apache-2.0 notices.
New search/checker code was produced with OpenAI Codex assistance.

## What is exact

Both candidate transitions start from `G(99/100,239/100,1/10)`:

| Role | Child B | Child L | Child cap | A | D | Crossing |
| --- | --- | --- | --- | --- | --- | --- |
| Physical numerator | 49461297/50000000 | 23767/10000 | 1/10 | 27/50 | 94 | 291/5000 |
| Count envelope | 987987/1000000 | 2357/1000 | 1/10 | 103/200 | 23 | 61/1000 |

For excess `v = w - crossing`, the selection is `u = A*v/(1+D*v)` and the
density threshold is

```
q = (999/1000)*L0*A / ((L0-L)*(1+D*v)+(6*B0-L0)*A).
```

`certify_fourth.py` proves all 14 strict gates from `HybridGates.lean`, the
three denominator inequalities, the LOW identities, the selection derivative
identity, and the `DSFace` side conditions over the full closed excess interval.
The known third transition is also replayed as a calibration case. Positivity
uses exact rational Bernstein coefficients and subdivision; floating searches
are never accepted as certificates.

The child boundary gain is `(L0-L)*(w-crossing)`. The count child is weaker
below `61/1000`, so the inherited parent count face remains in the envelope.
The physical child's crossing is below every marked width used by the final
new-conductor schedule, with this overlap checked exactly.

`return_certify.py` verifies:

* All 15 admission guards on 29 upward windows: 13 inherited parent count
  windows, 13 additional fourth count windows, and three inherited capped
  parent windows. Every window reaches `p=1/2`.
* All four conductor-edge margins over `delta in [0,3/4]`, `p in [0,1/2]`,
  using a closed cover of 91 rational rectangles and reserve `1/10^8`.
* The old count denominator on the entire rectangle, all 45 scalar geometry
  and schedule inequalities, both geometry identities, positive capacities,
  the source cap restrictions, and the reserve comparison to `rowFee=1/10^9`.

For each return rectangle and each edge, the receipt names an available count
branch whose rational row-margin polynomial has a positive Bernstein lower
bound. Since the count envelope is at most that branch, its row also closes.
The full conductor intervals follow the pinned `Conductor.lean` argument:
each clipped capacity gives the maximum of two affine row expressions in the
conductor, so their endpoints suffice. The independent audit checks exact
rectangle coverage and availability as well as all coefficients.

The `BoundsN.floor_margin` reserve is `12159799/3000000000000 > 0`.
The receipt preserves a negative control: `theta=436991/500000`, `h=8059/10000`
passes the earlier row-only calculation but fails that geometry field by
`-428480201/3000000000000`. A row check alone is insufficient.

The exact ablation at `delta=11/25`, `p=1/2`, the top conductor, shows that the
specified parent-only return fails the proposed theta:
`E-theta = 46874289255519/2599244500000000000 > 0`.
Adding only the new physical face also fails there. Adding both fourth faces
gives a negative excess. This is a point diagnostic, not a global optimum claim.

## Formal integration

The finite scalar verification is complete for the stated model. The source
instances and assembled endpoint were subsequently elaborated in Lean in
[tracker PR #85](https://github.com/GTimG/QuasiRiemannTracker/pull/85).
The declaration-level trace used for that integration is:
`HybridGates` and `DSFace` -> `Density.dsGates` -> density leaf ->
`CubeFree.cubefree_step` -> global source. PR84's final theorem supplies the
generic diagonal provider. PR #85 adds and checks both fourth instances,
while retaining the inherited analytic estimate. The research bundle alone
supplies arithmetic receipts; the tracker submission supplies the Lean theorem.

The return port must retain four distinct branch roles:

| Role | B | L | Cap |
| --- | --- | --- | --- |
| inherited parentC | 99/100 | 239/100 | 9999/100000 |
| inherited parentCap | 99/100 | 239/100 | 31/500 |
| additional fourthC | 987987/1000000 | 2357/1000 | 9999/100000 |
| physical numerator | 49461297/50000000 | 23767/10000 | 3/50 |

In PR84, `capP` and the physical numerator share `physicalB/physicalLambda`.
The integrated proof separates them. Replacing those shared constants globally
would change the inherited capped count branch and would not implement this
certificate. PR #85 keeps `parentCap` attached to the old source, adds `fourthC`,
retains `parentC` in the envelope, and uses a common mesh for the inherited,
fourth count, and fourth physical sources. It ports the exact window and edge
certificates and completes the physical schedule, endpoint assembly, Lean build,
and axiom audit.

## Search record

`search_fourth.py` and `numerical-candidates.json` record the initial numerical
source-face search. `return_probe.py`, `return_search.py`, and
`return-search.json` record numerical return diagnostics. Running those scripts
also requires NumPy and SciPy. They are optional and are not used by replay.

The constrained numerical search, including the floor condition, approaches
`theta ~ 0.87398078913`, `h ~ 0.805460186`. That is only a diagnostic; the
accepted exact candidate keeps the original, simpler `h=0.80545`.

The tracker frontier checked when this work began was merged PR84 at 0.873985.
The source transitions here are distinct from the original hillclimb's fixed
side-budget recurrence and from its PR29 bootstrap-limit result. As of 28 October
2026, independent [tracker PR #86](https://github.com/GTimG/QuasiRiemannTracker/pull/86)
has passed admission with the stronger bound 0.8739558 using a finer chain.
