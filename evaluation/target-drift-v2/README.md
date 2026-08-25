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
grading rubric, resource policy, exact no-replacement/no-imputation policy,
   completion-ledger builder, agent/checker/grader contracts, checker
isolation-probe report, the canonical Docker launcher, image recipe and verified
SBOM, materializer/runner/host-controller/container-controller/inner-checker/
grader/analysis code, the actual adapter entrypoint, its absolute host runtime,
the separately invoked Codex CLI client executable and exact `--version` output,
and their per-file hashes.  The runner substitutes only the entrypoint copy
inside the sealed pack and rejects a changed adapter or provider-client executable
before launch.
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
6. hash-seal `complete_450_no_replacement_no_imputation_v1` and its completion-
   ledger builder, then materialize the 450-ID completion ledger;
7. materialize blind grader packets and freeze the target-aware analysis code.

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

The missing-run policy is now executable but still result-free.  After an
individual adapter or checker failure, the remaining preregistered runs continue;
the failed run is never replaced and its outcome is never imputed.  The operator
ledger covers all 450 semantic run IDs and reports missingness by terminal state,
reason, condition, and requirement variant.  Only a literal 450/450 set of
production-result-eligible checked records may enter blind grading or inferential
analysis.  Otherwise the analysis command emits only missingness counts and
omits every effect estimate, interval, p-value, q-value, and success claim.

For the staged seal, edit a copy of `execution-template.json` only at the
human/provider fields, replace the image-SBOM template with a real
`built_manifest_verified_probe_pending` record plus its build-input,
cache-manifest, and build-log sidecars, and create a `frozen_ready` copy of the
source manifest with exact local PDF paths.  Bind the canonical
Docker executable and runtime identity, run the seven-probe recorder using that
runtime-bound config, and only then preseal:

```text
python tools/prepare_target_drift_checker_probe_config.py --template evaluation/target-drift-v2/execution-template.json --context CHECKER-CONTEXT --artifact-dir CHECKER-BUILD-ARTIFACTS --probe-report CONFIGURED-PROBE-REPORT.json --probe-artifacts-dir FRESH-PROBE-ARTIFACTS --output CHECKER-PROBE-DRAFT.json
python tools/finalize_target_drift_config.py bind-runtime --draft CHECKER-PROBE-DRAFT.json --runtime-executable ABSOLUTE-DOCKER-PATH --output RUNTIME-BOUND.json
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
The v2 adapter contract records adapter-level `model_invocations`, not invented
HTTP request IDs: the Codex CLI exposes a task/thread ID and turn-level usage,
but not provider-internal request or retry identities. The local Codex CLI
client is hash-bound and rechecked; the remote model version is a frozen
provider/operator attestation, not a fact derived from JSONL. Cache-read,
cache-write, and reasoning-output tokens are retained as observable categories;
cost is recomputed
from separately frozen dated USD-per-million-token rates rather than trusted
from adapter prose.
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

The manual `target-drift-checker-image.yml` workflow now closes the former
human-copy gap for a candidate: after building on one Docker daemon, it
materializes a checker-only draft from the verified SBOM and sidecars, binds
that exact daemon/runtime, and executes the sealed seven-probe recorder.  Its
`if: always()` upload step preserves whatever evidence was produced.  Once the
recorder starts, its pipefail/tee attempt log is preserved; a passed run
additionally contains the sealed probe report and raw probe artifacts.  An
earlier materialization or runtime-binding failure may contain only the sidecars
produced before that failure.  Any failed probe fails the job.  This is still
result-free candidate evidence: the ephemeral
image is not published, a successful candidate probe is not a final production
seal, and the workflow never invokes a model.

The first successful result-free Linux candidate build is recorded in
[`checker-image-candidate-32137509103.json`](checker-image-candidate-32137509103.json).
GitHub Actions [run 32137509103](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32137509103)
built both Lean targets, produced a 121,277-file byte manifest for the complete
Lake cache, verified its frozen-source provenance, and passed the final-image
offline Lean 4.29.1 / Lake 5.0.0-src+f72c35b probe as UID/GID
`10002:10002`.  The resulting image
digest was local to the ephemeral runner and was not published.  This closes a
  candidate construction/attestation check only; the final production image,
  real three-condition smoke, and every model run remain pending.

A later result-free candidate build and isolation run is recorded in
[`checker-image-candidate-32419343467.json`](checker-image-candidate-32419343467.json).
GitHub Actions [run 32419343467](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32419343467)
rebuilt one unpublished cache-complete image, bound the exact Docker
client/server/daemon and command boundary, and passed all seven candidate
isolation probes.  The worker reported `CapEff=0000000000000000`; every probed
write to protected input/output paths failed; request/base/patch/host sentinels
were unchanged; and cid- plus label-indexed inspection proved cleanup.  The
downloaded artifact manifest and image/cache/build/runtime hash chain were
independently recomputed.  This closes the result-free candidate-probe gate for
that ephemeral digest only.  It does not publish or freeze the final production
checker, instantiate the production agent sandbox, satisfy the real
one-case-by-three-condition smoke, or report a model/formalization outcome.

A separate result-free agent lifecycle candidate is recorded in
[`agent-lifecycle-candidate-32436339541.json`](agent-lifecycle-candidate-32436339541.json).
GitHub Actions [run 32436339541](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32436339541)
built one unpublished digest-recorded image whose controller was PID 1, launched
a fixture that escaped the direct child's session and process group, and then
abruptly killed the host Docker client.  Before that crash the escaped
descendant's heartbeat strictly increased from `1` to `2`; after Docker stdin
closed, the controller recorded `control_channel_eof`, its direct child returned
`-15`, the labeled container disappeared, and the heartbeat remained frozen at
`2`.  The downloaded report independently matches the exact command digest,
five source/workflow bindings, two raw Docker runtime ledgers, image/base
digests, and raw ready/exit/fixture/cid artifacts.  This closes only the recorded
Linux PID-namespace lifecycle component for that ephemeral image/runtime/command.
It is not the final provider-capable agent image and does not instantiate its
authentication, model-visible filesystem, network/tool, or active-budget
boundaries.  The PID-1 controller must be incorporated into the final agent
image and the same destructive probe must be rerun on that final digest before
the real smoke.

The combined result-free lane is implemented as
`.github/workflows/target-drift-agent-image.yml`.  It first rebuilds the
cache-complete checker base from the common pre-audit Git snapshot.  It then
verifies the exact registry SRI and SHA-512 in
`agent-image-sources.json`, extracts only the native Linux Codex executable,
bundled `bwrap`, bundled `rg`, and package identity, and layers those bytes with
the adapter and PID-1 controller onto that Lean base.  The agent context also
copies and cross-checks the checker SBOM, raw build-input manifest, and cache
manifest, so the inherited workspace/source provenance is not a free-standing
hash claim.  Its two probes are provider-free: one observes workspace
write, persistent-write denial outside the workspace, an explicit kernel
socket-creation or route denial while the outer control reaches the same
resolved IPv4 endpoint, inability to read the outer credential sentinel, exact
AppArmor profile inheritance, fresh PID visibility, and
Codex/Lean/Lake/cache byte bindings; the other kills
the host Docker client and requires namespace reaping on the same final digest.
After checkout, the lane initializes a result-free attempt ledger and its
`always()` upload step attempts to retain every artifact produced before a
failure; an earlier checkout/platform failure may remain visible only in the
Actions log.  GitHub Actions
[run 32464814750](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32464814750)
completed both probes on one exact unpublished image digest.  The downloaded
23-artifact set was independently checked against every recorded byte count and
SHA-256, the report/SBOM/cache/source bindings, the outer-reachable and
inner-`socket_create`/`EPERM` network observations, the lifecycle report and
runtime ledgers, and the final heartbeat artifact.  The durable metadata is recorded in
[`agent-image-candidate-32464814750.json`](agent-image-candidate-32464814750.json).
This is an unpublished provider-client-capable result-free candidate, not a
credential-bearing production run, a real smoke, or a model/formalization
outcome.

The current source additionally defines a narrowly scoped outer-boundary
candidate in `tools/launch_target_drift_agent_container.py`.  It intentionally
has no production or provider action.  Its only command verifies the local
image digest and in-image controller/probe bytes, then mounts a literal fake
`auth.json` and fake agent input read-only under a root PID-1 controller.  The
controller copies only the input into disposable tmpfs, opens the fixed fake
auth once as a read-only descriptor, passes it to the irreversibly dropped
uid/gid 10002 worker, and closes its copy.  The worker exactly consumes and
closes that descriptor before launching the offline Codex sandbox.  The nested
probe requires zero capabilities, denied network, immutable original input, a
writable copied workspace, EACCES/EPERM on the existing auth/control paths, and
no auth descriptor or broker environment marker.  This one-time fake handoff is
not the real Codex provider authentication path.  GitHub Actions
[run 32735680163](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/32735680163)
exercised the fake-only component on the same unpublished image digest as the
offline-isolation and destructive-lifecycle probes.  Independent review of all
29 artifact files checked 116 hash, schema, source-binding, and boundary
conditions with no error.  The raw control directory contained exactly
`controller-report.json`, `pid1-ready.json`, `pid1-exit.json`, and the
root-only sentinel; the nested sandbox recorded `EACCES` on both existing auth
and control paths, no broker environment marker or auth-targeting descriptor,
and zero worker and nested effective capabilities.  The durable public record
is
[`agent-outer-boundary-candidate-32735680163.json`](agent-outer-boundary-candidate-32735680163.json).
No real credential or remote model was used.  The record closes only this
result-free fake-only component gate; it does not publish a production image or
satisfy the real credential/model/budget/smoke gates.

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

The schedule runner executes runs in sealed presentation order, never revisits a
terminal state, and continues with the remaining preregistered IDs after a
run-level failure.  It writes the completion ledger and exits nonzero when fewer
than 450 runs are production-result-eligible:

```text
python tools/run_target_drift_schedule.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json
```

The ledger may also be rebuilt read-only from an already attempted run root:

```text
python tools/build_target_drift_completion_ledger.py --pack FROZEN-PACK --runs-root RUNS --output COMPLETION-LEDGER.json
```

For an incomplete ledger, do not create grader packets.  The only permitted
analysis output is the non-inferential missingness report (also exit-nonzero):

```text
python tools/analyze_target_drift_execution.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json --output INCOMPLETE-ANALYSIS.json
```

Only after the ledger certifies all 450 runs may the blind grading and
digest-bound inferential chain run:

```text
python tools/prepare_target_drift_grading.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json --output GRADING-PACK
python tools/assemble_target_drift_grades.py --pack FROZEN-PACK --grading-pack GRADING-PACK --grader-response GRADER-A.json --grader-response GRADER-B.json --adjudication ADJUDICATION.json --output GRADES.json
python tools/analyze_target_drift_execution.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json --grading-pack GRADING-PACK --grades GRADES.json --output ANALYSIS.json
```

These commands expose executable code paths; they do not supply a provider,
agent image, final published production checker image,
credentials, budget choices, or grader identities.  The current local gate
includes target-drift component tests covering deterministic assignment, seal hashing,
opaque prompts, manifest/digest checks, selected fail-closed paths, a synthetic
450-record analysis, and complete/incomplete/tampered completion-ledger cases.
The deterministic fake fixture and two local
fail-closed probes are nonexperimental and do not pass the real-infrastructure
gate.  `tools/prepare_target_drift_smoke.py` and
`tools/run_target_drift_smoke.py` provide a separate operator-only lane for the
preregistered one-case-by-three-condition check.  The plan binds one matched
case/replicate/requirement triplet and both tool hashes; the runner withholds the
smoke purpose from the agent request and records every successful production
checker run as `checked_smoke_nonexperimental` with
`result_eligible=false`.  `tools/prepare_target_drift_grading.py` independently
rejects this execution purpose.  Thus even a passed smoke cannot enter the 450,
blind grading, or inferential analysis.

After a final pack exists, the intended operator commands are:

```text
python tools/prepare_target_drift_smoke.py --pack FROZEN-PACK --run-id ONE-PRIMARY-RUN-ID --output SMOKE-PLAN.json
python tools/run_target_drift_smoke.py --pack FROZEN-PACK --plan SMOKE-PLAN.json --ledger SMOKE-LEDGER.json
```

The runner accepts no execution-root override.  Production smoke orchestration
is fail-closed on Windows until a tested private DACL and job-object boundary is
implemented; on POSIX it creates an owner-only `0700`
`/tmp/.abrl-runs/RUNS-<opaque>` root and requires the opaque basename recorded in
the plan.  Prompt source/workspace locations are relative to the common agent
root.  This removes operator-supplied smoke markers from the model-visible
current working directory and prompt paths.  A final production agent sandbox
with a reviewed real-execution action derived from the result-free-only outer
launcher remains required before the real smoke runs.  The result-free
agent-image workflow is designed
to combine the exact provider client, offline Lean cache, adapter, and PID-1
controller and to rerun the destructive lifecycle probe, but it supplies no
credential and makes no model call.  The source-level outer-boundary candidate
adds root-only control, a fake single-file credential, and a disposable
non-root workspace, but has no real adapter execution action.  A passing
candidate must still be extended with that fixed real execution path and
reprobed on the published final digest before a
controller crash can be claimed not to leave a real provider child consuming
budget or mutating the resumable attempt.

This lane is implemented and component-tested, but it has not been run with a
real provider/agent sandbox.  No real three-condition smoke, final pack, primary
model run, grader response, grade ledger, or analysis output exists.

The primary three-condition study is a controlled mechanism comparison, not a
claim that ABRL has already been compared with a current public end-to-end
autoformalization workflow.  [`external-comparator-plan.json`](external-comparator-plan.json)
therefore independently pins LeanFlow's paper, public repository commit, and license and
defines a separate 30-run descriptive calibration after a result-ineligible
smoke.  Replicate index zero, the 15/15 hidden-variant balance, two allowed
contrasts, and a no-inference/no-ranking boundary are fixed before any primary
or comparator outcome.  It reuses the frozen cases, hidden requirements, checker, and expert
rubric while preserving framework-native event semantics.  Those runs are not
part of the 450-run primary estimand, have not started, and currently support no
numerical or superiority claim.
The adjacent `external-comparator-plan.seal.json` content-addresses both this
plan and the unchanged 18 August primary protocol; the independent validator
rejects any byte drift or prematurely created comparator-results file.
The separate LeanFlow plumbing seal now additionally binds a deterministic
30-ID `leanflow_external` schedule, an exact completion-ledger schema, and one
excluded-fixture request.  The fixture entrypoint is deliberately incapable of
running LeanFlow: its contract requires provider mode, network, credential
access, subprocess use, repository execution, and model-call budget all to be
disabled.  It emits only a zero-usage, result-ineligible plumbing receipt and
fails closed on unknown fields or production-result filenames.  The tracked
`external-comparator-results.json` and
`leanflow-external-completion-ledger.json` files remain absent.  This is not the
real-infrastructure smoke required by the external-comparator plan.
The result-free ledger template carries each run's source and stratum and
reports missingness by cause, condition, hidden requirement variant, paper
source cluster, and individual textbook target; it still permits no effect
estimate while any external run is unmaterialized.

The result-free lane can be checked without credentials, network, a LeanFlow
checkout, or a model invocation:

```text
python tools/build_leanflow_target_drift_schedule.py --check evaluation/target-drift-v2/leanflow-external-schedule.json
python tools/validate_target_drift_external_comparator.py
python -m unittest tools.test_target_drift_external_comparator -v
```

`tools/codex_target_drift_adapter.py` is a result-free candidate adapter. Its
component tests cover the supported Codex JSONL schema (including item updates,
errors, and fail-closed forbidden-tool events), observable task/thread identity,
cache-read/cache-write/reasoning token accounting, build/recovery boundaries,
Lean patch construction, protected-output link rejection, process-failure
terminal evidence, frozen-price cost reconstruction, and unknown-event
rejection. The candidate explicitly disables web search, MCP/plugin/app,
collaboration, browser/computer/image, skill-discovery, and related tool
surfaces; copies one auth file into a fresh disposable `CODEX_HOME`; gives model-spawned commands
only a frozen allowlisted environment; and launches no automatic second CLI
invocation. Provider-client-internal retries remain outside the observable
adapter trace and must be separately frozen or disclosed before execution.
Its machine failure definition treats a nonzero CLI exit, missing thread or
terminal usage, observable runtime error, forbidden-tool event, or ambiguous
multi-build accounting as a retained `infrastructure_failure` governed by the
hash-sealed no-replacement/no-imputation policy and 450-ID completion ledger.
The recovery metric observes only a
direct `lake build` or `lake env lean` invocation at command start or after a
frozen shell separator; command text that merely mentions a build is excluded.
These are code-level constraints, not a passed production isolation probe. It
does not make the current host a production agent sandbox: the exact provider
client, remote-model attestation, agent image, visibility/network/process probes, prices,
budgets, and three-condition smoke remain unfrozen and unrun.
`tools/fake_target_drift_adapter.py` and
`tools/fake_target_drift_cache_prelude.py`, and
`tools/fake_target_drift_checker_sandbox.py` are deterministic fixture helpers
for local plumbing experiments; no tracked full-chain smoke is claimed.  They
are not a model provider, sandbox, or cache-image attestation and cannot satisfy
the real-execution gate.
