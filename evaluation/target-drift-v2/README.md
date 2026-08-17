# Target-drift suite v2

Status: `balanced_variants_designed_execution_not_started`

Version 2 preserves the frozen v1 source cases and fixes execution-validity
problems before any model run.  It does not overwrite v1 and contains no
outcomes.

The 30 base cases, three matched conditions, and five paired replicates still
yield 450 planned runs.  The sealed materializer assigns one hidden proposed
requirement to every target-replicate pair by fixed case/replicate parity:

- 75 pairs receive a source-faithful requirement;
- 75 pairs receive the injected-drift requirement;
- all three conditions receive the same variant within a pair.

Thus an always-reject strategy fails the faithful half, while sensitivity to
drift and specificity on faithful requests are both observable.  Replicates
are aggregated within target before primary paired inference.

Both variants now use exactly the same frozen field/value sentence template.
The validator rejects legacy variant-specific style markers and freezes a
leave-one-pair-out text-only diagnostic (currently 0.633 for the deterministic
Bernoulli-naive-Bayes negative control).  A separate source-absent frozen-model
audit and an independent blind wording review remain mandatory human fields;
the diagnostic is not a formalization result.

Every evaluated workspace is built from commit
`d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9`, the public base immediately
before the source-frozen paper audit and challenge artifacts.  This prevents
the common Lean tree or the ABRL overlay from containing case-specific audit
answers.  The compile-only and source-aware conditions use an explicit core
allowlist; the ABRL condition uses the same base with `evaluation/` removed.

The execution seal must cover the normalized config, balanced assignments,
the complete operator-only challenge ground truth, the v2 protocol, exact
prompts, paired wording, portable source manifest and all four PDF byte streams,
grading rubric, resource policy, adapter/grader contracts,
materializer/runner/checker/grader/analysis code, and their per-file hashes.
Evaluated agents receive opaque IDs and one requirement.  Primary graders see
neutralized final artifacts and post-hoc checker evidence, not condition or
variant labels or condition-specific workflow traces.

Each run must also emit a hash-bound workflow-compliance record.  Compile-only
has no condition-specific evidence file, source-aware must retain a run-local
`blueprint.md`, and ABRL must retain a target contract, blueprint, failure
ledger, and promotion-gate log.  The neutral checker verifies those files and
their hashes; primary graders see only the common compliance result.

Before the 450 runs, the following are mandatory:

1. fill and freeze every field in `execution-template.json`;
2. materialize and verify a content-addressed sealed pack;
3. freeze a real adapter command/container and pass forbidden-path/string,
   budget, trace, and sandbox isolation probes;
4. run one case × three conditions × one replicate as infrastructure-only
   smoke tests;
5. verify budget/timeout/retry enforcement and the hash-bound neutral checker;
6. materialize blind grader packets and freeze the target-aware analysis code.

The grader-packet materializer and packet-order seed are frozen before model
execution.  Packet contents and their aggregate digest are produced only after
neutral checking and are frozen before any primary grader sees them.  The two
complete blind response files and an adjudicator file for every binary-label
or structured source-field disagreement are then combined by
`tools/assemble_target_drift_grades.py`; the target-level analysis consumes only
that digest-bound 450-record ledger and applies Benjamini--Hochberg adjustment
to the preregistered secondary endpoints.

No pilot output may enter the final result set, and no challenge may be
replaced after difficulty is observed.

For the two-stage seal, edit a copy of `execution-template.json` only at the
human/provider fields and create a `frozen_ready` copy of the source manifest
with exact local PDF paths.  Then run:

```text
python tools/finalize_target_drift_config.py preseal --draft HUMAN-DRAFT.json --source-manifest SOURCES.json --output PRESEAL.json
python tools/prepare_target_drift_execution.py --config PRESEAL.json --materialize PRESEAL-PACK
python tools/finalize_target_drift_config.py freeze --preseal-config PRESEAL.json --preseal-pack PRESEAL-PACK --output FROZEN.json
python tools/prepare_target_drift_execution.py --config FROZEN.json --materialize FROZEN-PACK
python tools/prepare_target_drift_execution.py --verify-pack FROZEN-PACK
```

The preseal and frozen configurations normalize to the same digest input; the
second materialization must reproduce the first aggregate exactly.

For each semantic run selected by the operator, the frozen runner prepares an
opaque view, invokes the configured adapter without a shell, enforces an
orchestrator process-tree timeout, validates the response/JSONL trace, rejects
trace accounting beyond the token/tool/build/retry/time/cost budgets, and
rehashes the completed view.  A trusted checker-only dependency-cache prelude
(or an explicitly empty one for a cache-complete image) is frozen as argv and
included in the seal; it never enters the evaluated agent's resource view.  The
same sealed pack is then required by the neutral checker:

```text
python tools/run_target_drift_execution.py --pack FROZEN-PACK --run-id SEMANTIC-RUN-ID --output RUN-DIR
python tools/run_target_drift_execution.py --pack FROZEN-PACK --execute RUN-DIR
python tools/check_target_drift_run.py --pack FROZEN-PACK --run-dir RUN-DIR
```

After all 450 runs have terminal checked records, the blind grading and
digest-bound analysis chain is:

```text
python tools/prepare_target_drift_grading.py --pack FROZEN-PACK --runs-root RUNS --output GRADING-PACK
python tools/assemble_target_drift_grades.py --pack FROZEN-PACK --grading-pack GRADING-PACK --grader-response GRADER-A.json --grader-response GRADER-B.json --adjudication ADJUDICATION.json --output GRADES.json
python tools/analyze_target_drift_execution.py --pack FROZEN-PACK --grading-pack GRADING-PACK --grades GRADES.json --output ANALYSIS.json
```

These commands make the interface executable; they do not supply a provider,
container image, credentials, budget choices, or grader identities.  Those
remain deliberately unfrozen and no primary run has started.
`tools/fake_target_drift_adapter.py` is only a deterministic fixture for the
excluded local plumbing smoke test; it is not a model provider or isolation
attestation and cannot satisfy the real-execution gate.
