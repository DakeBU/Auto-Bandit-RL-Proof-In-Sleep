# Target-drift suite v2

Status: `balanced_variants_designed_execution_not_started`

Version 2 preserves the frozen v1 source cases and revises the design to address
identified execution-validity problems before any model run.  It does not
overwrite v1 and contains no outcomes.

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

The protocol requires every future evaluated workspace to be built from commit
`d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9`, the public base immediately
before the source-frozen paper audit and challenge artifacts.  This prevents
the common Lean tree or the ABRL overlay from containing case-specific audit
answers.  The compile-only and source-aware conditions use an explicit core
allowlist; the ABRL condition uses the same base with `evaluation/` removed.

The execution seal must cover the normalized config, balanced assignments,
the complete operator-only challenge ground truth, the v2 protocol, exact
prompts, paired wording, portable source manifest and all four PDF byte streams,
grading rubric, resource policy, agent/checker/grader contracts, checker
isolation-probe report, the canonical Docker launcher, image recipe and verified
SBOM, materializer/runner/host-controller/container-controller/inner-checker/
grader/analysis code, the actual adapter entrypoint, its absolute host runtime,
and their per-file hashes.  The runner substitutes only the entrypoint copy
inside the sealed pack and rejects a changed runtime executable before launch.
Future evaluated agents will receive opaque IDs and one requirement.  Primary graders will see
neutralized final artifacts and post-hoc checker evidence, not condition or
variant labels or condition-specific workflow traces.

Each future run must also emit a hash-bound workflow-artifact record.  Compile-only
has no condition-specific evidence file, source-aware must retain a run-local
`blueprint.md`, and ABRL must retain a target contract, blueprint, failure
ledger, and promotion-gate log.  The current checker verifies only the required
files, paths, and hashes; it does not prove that the named workflow was actually
followed.  Primary graders will see only this common artifact-presence result.

Before the 450 runs, the following are mandatory:

1. fill and freeze every field in `execution-template.json`;
2. materialize and verify a content-addressed sealed pack;
3. freeze a real adapter command/container, its entrypoint and host-runtime
   bytes, and pass forbidden-path/string,
   budget, trace, and sandbox isolation probes;
4. run three real-provider/real-sandbox runs (one case × three conditions × one
   replicate) as infrastructure-only smoke tests excluded from the primary 450;
5. freeze a digest-pinned checker image and canonical launcher implementing the
   tracked controller/worker-separation contract, then pass all seven isolation
   probes;
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

For the staged seal, edit a copy of `execution-template.json` only at the
human/provider fields, replace the image-SBOM template with a real
`built_manifest_verified_probe_pending` record plus its build-input,
cache-manifest, and build-log sidecars, and create a `frozen_ready` copy of the
source manifest with exact local PDF paths.  Bind the canonical
Docker executable and runtime identity, run the seven-probe recorder using that
runtime-bound config, and only then preseal:

```text
python tools/finalize_target_drift_config.py bind-runtime --draft HUMAN-DRAFT.json --runtime-executable ABSOLUTE-DOCKER-PATH --output RUNTIME-BOUND.json
python tools/record_target_drift_checker_isolation_probe.py --config RUNTIME-BOUND.json --work-dir FRESH-PROBE-WORK --output CONFIGURED-PROBE-REPORT.json --probe-commit FULL-GIT-COMMIT --host-platform HOST-DESCRIPTION
python tools/finalize_target_drift_config.py preseal --draft RUNTIME-BOUND.json --source-manifest SOURCES.json --output PRESEAL.json
python tools/prepare_target_drift_execution.py --config PRESEAL.json --materialize PRESEAL-PACK
python tools/finalize_target_drift_config.py freeze --preseal-config PRESEAL.json --preseal-pack PRESEAL-PACK --output FROZEN.json
python tools/prepare_target_drift_execution.py --config FROZEN.json --materialize FROZEN-PACK
python tools/prepare_target_drift_execution.py --verify-pack FROZEN-PACK
```

The preseal and frozen configurations normalize to the same digest input; the
second materialization must reproduce the first aggregate exactly.

For each future semantic run selected by the operator, the frozen runner code prepares an
opaque view, invokes the configured adapter without a shell, enforces an
orchestrator process-tree timeout, validates the response/JSONL trace, rejects
trace accounting beyond the token/tool/build/retry/time/cost budgets, and
rehashes the completed view.  The adapter command receives the entrypoint only
through `{{ADAPTER_ENTRYPOINT_PATH}}`, resolved to the content-addressed pack;
the frozen absolute runtime is checked as one regular, unlinked executable.
The checker host controller then verifies the
pack/run chain without executing Lean, reconstructs a pristine condition-view
snapshot, and emits a sanitized request containing only the base, submitted
patch, public declaration names, expected file hashes, and opaque/hash
bindings.  The sandbox never receives the complete pack, operator directory,
challenge ground truth, source bank, semantic ID, condition label, requirement
variant, current Git checkout, credentials, or container socket.  The inner
checker performs patch replay, build, canary, axiom, and post-worker source-hash
checks.  Only a hash- and identity-validated artifact bundle is atomically
published and allowed to enter blind grading.

A real checker must use an immutable cache-complete image, an empty prelude,
read-only request/base/patch mounts, no network, a read-only root filesystem,
resource limits, and separate trusted-controller/Lean-worker identities.  The
image must expose the complete `.lake` dependency seed at the fixed in-image
path and a byte-complete manifest.  The manifest is SBOM/runtime-bound; the
inner checker verifies every cached file, then directs the already restricted
worker to copy it into the per-run tmpfs replay before any offline `lake build`.
No host dependency cache is mounted.
The reproducible recipe can now construct the checker image from the exact
common pre-audit Git snapshot instead of assuming that an undocumented
cache-complete base image already exists.  On a short-path, LF-normalized clean checkout (for example
`C:\abrl-checker-build` on Windows), an operator with the audited Linux Docker
daemon prepares the minimal context, verifies it, builds the image, and emits
the image/cache/toolchain SBOM as follows:

```text
python tools/prepare_target_drift_checker_image.py prepare-context --workspace-base-commit d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9 --lean-base-image REGISTRY/LEAN@sha256:DIGEST --output C:\abrl-checker-context
python tools/prepare_target_drift_checker_image.py verify-context --context C:\abrl-checker-context
python tools/prepare_target_drift_checker_image.py build-image --context C:\abrl-checker-context --image-tag abrl-target-drift-checker:candidate --sbom-output evaluation/target-drift-v2/checker-image-sbom.json --cache-manifest-output evaluation/target-drift-v2/checker-cache-manifest.json --build-log checker-image-build.log
```

The context contains only the allowlisted Lean/Lake base snapshot plus the
checker recipe/controller/inner checker/cache-manifest generator.  It excludes
the evaluation bank, condition metadata, operator ground truth, current
post-base library, Git database, and credentials.  The multi-stage recipe runs
`lake exe cache get` and `lake build BanditRLProof Tests`, materializes only
cache-internal symbolic links that resolve to regular files as ordinary bytes,
then rejects every remaining link, reparse point, special file, and multiply
linked cache file and records every final cache byte.  The final image does not
contain the builder-stage source snapshot.  The
builder then mounts the exact frozen `lean-toolchain` into that final image and,
with network disabled, the filesystem read-only, and UID/GID `10002:10002`,
executes a minimal Lean file plus `lean --version` and `lake --version`; the
reported release must match the pinned toolchain before an SBOM can be emitted.
The emitted `built_manifest_verified_probe_pending` SBOM is still only an image-construction record:
it cannot replace the seven production isolation probes, the real one-case by
three-condition smoke, or any model run.

The first successful result-free Linux candidate build is recorded in
[`checker-image-candidate-32137509103.json`](checker-image-candidate-32137509103.json).
GitHub Actions [run 32137509103](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32137509103)
built both Lean targets, produced a 121,277-file byte manifest for the complete
Lake cache, verified its frozen-source provenance, and passed the final-image
offline Lean 4.29.1 / Lake 5.0.0-src+f72c35b probe as UID/GID
`10002:10002`.  The resulting image
digest was local to the ephemeral runner and was not published.  This closes a
candidate construction/attestation check only; the final production image,
seven bound isolation probes, real three-condition smoke, and every model run
remain pending.

The sealed launcher accepts only the allowlisted Docker installation, rechecks the
executable/signature-or-package ledger plus client/server/daemon identity, and
constructs the complete argv itself.  Before every probe or replay it uses
non-executing image inspection and extraction to verify the actual in-image
controller, inner-checker, and cache-manifest bytes.  The exact image,
recipe/SBOM, argv,
attestations, and passed isolation-probe report are sealed.  The same sealed
pack is required by the host controller but is never mounted into the
untrusted Lean sandbox:

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

These commands expose executable code paths; they do not supply a provider,
agent image, final published production checker image,
credentials, budget choices, or grader identities.  The current local gate
includes target-drift component tests covering deterministic assignment, seal hashing,
opaque prompts, manifest/digest checks, selected fail-closed paths, and
synthetic 450-record analysis.  The deterministic fake fixture and two local
fail-closed probes are nonexperimental and do not pass the real-infrastructure
gate.  No real three-condition smoke, final pack, primary model run, grader
response, grade ledger, or analysis output exists.
`tools/fake_target_drift_adapter.py` and
`tools/fake_target_drift_cache_prelude.py`, and
`tools/fake_target_drift_checker_sandbox.py` are deterministic fixture helpers
for local plumbing experiments; no tracked full-chain smoke is claimed.  They
are not a model provider, sandbox, or cache-image attestation and cannot satisfy
the real-execution gate.
