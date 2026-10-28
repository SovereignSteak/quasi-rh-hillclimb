# Attribution and proof scope

The copied Lean files are unmodified Git blobs from GTimG/QuasiRiemannTracker
at 71996e7e79840455f7beead063a73b7b31cfb586. Their original copyright and license
comments are retained. `source-pins.json` identifies every file, source path,
Git blob and SHA256 digest. These files are Apache-2.0 material; the license is
included as `LICENSE-APACHE-2.0`.

The scalar formulas and proof architecture build on Sil's density-split work
and Rohan Arun's third transition, with inherited work by Hailey Collet,
ArviFoxy, and OpenAI. In particular the return layout is adapted upstream from
Hailey Collet's Record1252270103 finite return; the source gate layout and
checker are credited upstream to Sil. The present bundle adds exact Python
candidate certificates, numerical diagnostics, an independent receipt audit,
and a handoff. These additions were produced with OpenAI Codex assistance.

Relevant baseline attribution from the pinned tracker's NOTICE:

> QRH Bounds — new code licensed under Apache-2.0.
> Canonical statement and baseline mathematics: OpenAI math, commit
> fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0. Upstream license preserved
> in verifier/UPSTREAM-LICENSE. The relevant upstream source closure is vendored
> in submissions/openai-baseline/src/Submissions/openai_baseline/OAI/. Lean
> import paths are relocated to this submission; theorem bodies and declaration
> namespaces are preserved.

Inherited Hailey Collet attribution retained in the parent research repository:

> Copyright 2026 Hailey Collet. New manuscript and formalization material is
> offered under Apache-2.0. Reused work retains its original authorship,
> licenses and notices.
>
> This development uses OpenAI’s QRH framework, Akash Levy’s weighted-numerator
> development, Hailey Collet’s earlier QRH formalizations, Zhongpai Gao’s
> refinements and physical-source machinery, timbalud’s marked asymmetric
> counting and coupled radical allocation, DaysSky’s affine detector
> integration, related arithmetic prepared for liqsweep, and ArviFoxy’s computed
> ledger and two-level affine bootstrap. The used-source provenance map
> identifies exact revisions, paths, hashes and adaptations.
>
> Portions adapt Zhongpai Gao’s Target830 and Target836 counting, physical
> numerator, transport and incumbent-source developments, retaining their
> inherited OpenAI, Hailey Collet, Akash Levy, DaysSky and other source-specific
> notices. New parameterized interfaces, finite certificates and assembly code
> are by Hailey Collet.
>
> Hailey Collet is the sole human author of the current manuscript. Research,
> drafting and formalization were AI-assisted. The paper and source notices
> give the contribution account.
>
> Lean, mathlib and the pinned supporting packages retain their own authorship
> and licenses.

No Lean build, kernel replay, new analytic theorem, or maintainer endorsement
is asserted for this bundle. All mathematical implications here remain
conditional on the preprint's seven-eighths theorem.
