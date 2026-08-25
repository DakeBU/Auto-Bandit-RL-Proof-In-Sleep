# ABRL anonymous Lean/code artifact

This supplement supports the submission **ABRL: A Target-Faithful
Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement
Learning Theory**.  It is a positive-allowlist export of the Lean library,
focused canaries, declaration/status evidence, proof-graph tooling and frozen
result-free evaluation protocol.  It is not a mirror of the authoring
repository.

The archive is produced by a positive allowlist plus a private, producer-side
identity scan before its byte manifest is written.  The private blacklist is
not embedded as readable strings, unsalted digests, or a membership oracle in
the anonymous ZIP.  The packaged verifier independently checks every manifest
hash and generic email/absolute-host-path leaks, so mutation relative to the
supplied manifest is detected without revealing who or which private endpoints
were screened.

## What the artifact establishes

- The pinned Lean 4 and Mathlib environment is recorded by `lean-toolchain`,
  `lakefile.lean`, and `lake-manifest.json`.
- `BanditRLProof/` and `BanditRLProof.lean` contain the submitted Lean library.
- `Tests/` contains focused public canaries, including the delayed-feedback,
  succinct-support, stochastic-gradient-bandit, textbook lower-bound,
  random-time RL, ETC, and curvature--noise--gap routes.
- `evidence/claim-ledger.json` records compiled, partial, blocked, prototype,
  and planned boundaries without promoting an open theorem.
- `evidence/theorem-audit-comparison.json` is the claim-ledger-backed outcome
  matrix for the scoped Chapter 15 positive control and the three source-frozen
  external audits.  It separates contract stress, strongest compiled bridge,
  blocking obligations, and promotion status.
- `evidence/local_lean_declarations.json` is the packaged declaration index.
- `evidence/source-freeze.json` records the three-paper portfolio, official
  URLs, SHA-256 digests, page counts, theorem windows, and case-specific
  source-lock timing.  The delayed lock and its initial feasibility slice were
  co-published; the other two locks preceded their case-specific Lean slices.
- `evidence/*-proof-obligations.md` records the open delayed-feedback,
  succinct-geometry, and stochastic-gradient-bandit dependency boundaries.
- `evidence/proof-graph/` contains the current environment export and report,
  the frozen benchmark configuration, and the conservative CNG audit reports.
- `evaluation/` and the matching tools specify a **result-free** target-drift
  study.  The authoring-repository base identifier is redacted; packaged
  machine fields use a 40-hex non-Git placeholder derived from the anonymous
  source-tree binding in `evidence/anonymous-base-manifest.json`.  Because the
  ZIP deliberately contains no Git object database, the production
  materializer is not runnable from this archive; the protocol and component
  code are supplied for inspection and component tests only.  No provider
  run, grade, analysis result, or numerical outcome is included or claimed.
  The producer first verifies the public external-comparator plan and seal
  against the original primary-protocol bytes.  It then rebinds their SHA-256
  fields to the redacted protocol and canonical plan bytes packaged in this
  derivative archive.  The retained `sealed_on` date records when the
  result-free design was frozen; it is not a claim that the anonymized byte
  presentation existed unchanged on that date.  The packaged validator checks
  this derivative hash chain directly.

The delayed-feedback flagship contains 197 compiled source-audit declarations:
89 implementation-facing declarations, 19 separately counted
diagnostic/conditional/repair declarations, a 16-declaration processed-prefix
producer, a 9-declaration deterministic processed-trace-summary adapter, and a
15-declaration ordered no-switch structural transition, a 12-declaration
ordered trace layer, a 6-declaration nonnegative-gap D.11 domain leaf, and a
31-declaration Algorithm-5 line-10 initializer.
Five generic multi-regime contract declarations are counted separately, so the
`BanditRLProof/DelayedFeedback` directory contains 202 declarations in total;
those five generic declarations are not evidence for a Delayed SAPO endpoint.
The processed-prefix layer derives D.1 count, factor-three/factor-ten width, and
recursive-UCB inputs for a conditional same-snapshot factor-20 result from an
explicit certificate.  The adapter constructs that certificate only
conditional on the explicit D.4 count clause.  The 15-declaration layer compiles
one no-switch Algorithm-5 lines 3--4/7--8 step: append an arbitrary newly
observed source before forming the line-7 summary, then preserve the round-start
active-set invariant through exact line-8 removal.  Its numerical confidence
surfaces are explicit inputs.  The D.11 leaf is restricted to the nonnegative
stochastic-loss-gap domain, and line 10 initializes only newly eliminated arms.
Lemma D.13, EAP/BSC evolution beyond initialization, the measurable Delayed SAPO
trajectory, simultaneous D.4 `2/T` probability bound, ordered multi-snapshot
elimination, and the terminal regret chain remain open.  These declarations do
not verify or refute the source lemmas or paper-level theorem.  Across Textbook
Chapters 13--17, Chapter 15 Lemma 15.1 and
the exact Theorem 15.2 Gaussian expected-pseudo-regret/minimax terminals
compile, and Chapter 13 has a compiled constant-`1/54` downstream consumer.
Whole-chapter Notes/Exercises and the Chapter 16--17 terminals remain open, so
the multi-chapter spine stays partial.  The
proof-graph and CNG material is a prototype measurement study, not evidence of
search acceleration or a new general bandit calculus.

The independent succinct stochastic-bandit audit contains 54 named
declarations for the source-shaped unit-atom system, succinct-support contract,
Definitions 3.1--3.3, and Lemmas 3.1--3.4.  The strict-support route converts
local `R` equality into unit correlations and applies finite Bessel to prove,
for the same vector, strict representation-size minimality and uniqueness.  A
separate compiled diagnostic
records that the globally real-valued `R` candidate set can be unbounded
outside the atom-generated directions.  This is a regularity/codomain
obligation, not a source-error claim; the global Lemmas 3.5--3.6, Assumption
3.7, Theorem 3.8, and every regret endpoint remain outside the compiled slice.

The independent stochastic-gradient-bandit audit contains 44 named
declarations.  Its first 26 compile the finite-action algebra underlying
Algorithm 1 and Equations (3)--(7): softmax normalization, the zero-sum
parameter update, the exact finite conditional-mean increment, the
best-coordinate minimum-gap lower bound, and the
post-convergence/failure-mass decomposition.  A separate 18-declaration layer
constructs the recursive measurable softmax state, canonical generated
action/reward trajectory, initial and successor conditional laws, and
Equation-(5) history-step-kernel integrals under explicit coordinate-update
integrability and arm-reward integral equalities.  It does not provide the
source paper's uniform reward-regularity producer for those hypotheses.  The
learning-rate regimes and Theorems
1--4 remain outside the compiled slice.

## Quick verification

Use a short extraction path on Windows.  Network access is needed only on the
first dependency fetch; the pinned revisions are recorded in
`lake-manifest.json`.

```text
python artifact/verify_artifact.py
lake build BanditRLProof Tests
lake env lean Tests/Basic.lean
lake env lean Tests/DelayedFeedbackPaperAuditCanary.lean
lake env lean Tests/CurvatureNoiseGapGeometry.lean
lake env lean Tests/TextbookPartIVChapter13Canary.lean
lake env lean Tests/TextbookPartIVChapter14Canary.lean
lake env lean Tests/TextbookPartIVChapter15Canary.lean
lake env lean Tests/TextbookPartIVChapter16Canary.lean
lake env lean Tests/TextbookPartIVChapter17Canary.lean
lake env lean Tests/SuccinctLowerBoundPaperAuditCanary.lean
lake env lean Tests/StochasticGradientBanditPaperAuditCanary.lean
python -m unittest tools/test_proof_graph_lab.py
python tools/validate_target_drift_external_comparator.py
```

`lake build` is the full kernel/build gate.  The focused commands make the
paper-facing boundaries easy to inspect but do not replace the full build.
Target-drift developer tests are included, but tests that query the frozen Git
base belong to the authoring checkout and are not an archive-level
reproducibility gate.  The archive-level ledger therefore keeps the matched
study at `planned`.

## Reproducing the current proof-graph benchmark

```text
lake exe proof_graph_export --compact reproduced-proof-graph.json
python tools/proof_graph_lab.py validate-export --graph reproduced-proof-graph.json
python tools/proof_graph_lab.py benchmark --graph reproduced-proof-graph.json --config evidence/proof-graph/benchmark_roots.json --output reproduced-benchmark-report.json
```

The three benchmark-root support metrics are structural and expected to match
the packaged report.  Wall-clock fields in the historical measurement record
are single-machine observations, not portable proof costs.  ZDD construction
times are diagnostic timings and are not asserted byte-for-byte across hosts.

## External sources and redistribution boundary

The three camera-ready PDFs are not redistributed.  Their official URLs,
SHA-256 hashes, physical-page windows, and selection statuses are recorded in
`evidence/source-freeze.json`.  Mathlib and Lean are fetched from their pinned
upstream revisions.  See `THIRD_PARTY_NOTICES.md`.

## Data, models, seeds, and hardware

No training dataset or model weights are needed to check the Lean artifact.
The controlled target-drift study is preregistered but unexecuted, so there are
no experimental seeds, provider outputs, grades, or result tables to
reproduce.  Historical proof-check timings name their local environment and
are explicitly non-portable; the mathematical and structural checks do not
depend on that processor model.
