# Target-drift suite v2

Status: `balanced_variants_amended_pre_execution_execution_not_started`

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

## Pre-execution fixed-benchmark ITT method amendment

The result-free, hash-bound
[`method-amendment-fixed-target-paired-bootstrap-2026-08-31.json`](method-amendment-fixed-target-paired-bootstrap-2026-08-31.json)
(SHA-256
`5aed16ea25975786d79792ee194d87c081ec01247dbb1d314da05c8f582fdb9d`)
freezes the analysis boundary before any primary or external-comparator outcome
or evaluation provider call was observed.  The existing `protocol.json` bytes
remain unchanged and are bound by the amendment; the amendment supersedes only
the historical hierarchical-bootstrap interpretation in its dependence-plan
text.  Any future frozen execution configuration must bind the amended analysis
script.  The execution template now fixes the amendment path and SHA-256; the
materializer copies its exact bytes as `method-amendment.json`, and pack
verification checks those bytes against both the config and the amendment's
unchanged-protocol, analysis-script, and analysis-test bindings.  The bound
analysis test bytes are also carried under `execution_code/`.

The primary estimand is the equal-target-weighted, bundled-workflow
intention-to-treat effect of ABRL minus source-aware blueprint on the fixed set
of 30 frozen targets.  It does not generalize to a population of papers,
theorems, or targets and does not isolate one mechanism inside either workflow.
Compile-only remains a prespecified descriptive baseline.

Each target-condition receives five fresh, separately initiated provider
invocations.  Independence is an analysis assumption.  Replicate indices pair
the hidden requirement assignment across conditions, but they are not provider
seeds and do not pair provider randomness.  The amended 95% percentile
bootstrap therefore holds the 30 targets and each target's fixed 2/3 variant
allocation constant, and independently resamples invocations within each
target/condition/variant cell.  The schedule fixes the ordered labels exactly as
`[0, 1, 2, 3, 4]`; pack verification additionally reconstructs the canonical
agent-case order and requires the complete unique 30 × 3 × 5 run universe,
variant parity, run IDs, and presentation-order permutation.

The analysis now emits a machine-readable status for every primary-success
gate: the bootstrap lower endpoint must be strictly positive; all three
leave-one-paper-out point estimates must be nonnegative; and target-weighted
injected-drift sensitivity and faithful-request specificity must both be
reported for all three conditions.  Target-weighted fixed-benchmark rates are
separated from raw run-weighted counts and rates, which are descriptive only.
The 32,768-assignment exact sign flip over three paper clusters plus twelve
textbook targets is retained as a 15-unit sensitivity analysis, including after
Benjamini--Hochberg adjustment for secondary endpoints; it is not an extra
success gate or paper-population inference.

Both variants now use exactly the same frozen field/value sentence template.
The validator rejects legacy variant-specific style markers and freezes a
leave-one-pair-out text-only diagnostic.  It was 0.633 before the source-contract
pre-audit amendments and is 0.533 on the amended, resealed requirement bank for
the deterministic Bernoulli-naive-Bayes negative control.  A separate
source-absent frozen-model
audit and an independent blind wording review remain mandatory human fields;
the diagnostic is not a formalization result.
The checked-in `wording-negative-control-record.json` binds that deterministic
value to the exact paired-requirement bank and audit-script bytes; the v2
validator requires the exact top-level and nested schemas, schema version, and
recorded audit command before recomputing all three bindings.  Extra result or
claim fields are rejected.  The record is result-ineligible and does not
replace either mandatory leakage review.

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
grader/grader-exporter/analysis code, the actual adapter entrypoint, its absolute host runtime,
the separately invoked Codex CLI client executable and exact `--version` output,
the result-free human-review protocols and validators, and their per-file hashes.
The sealed review subpack additionally binds the packet/templates, three review
payloads, preregistered role registry and exact `allowed_signers` bytes, three
review-payload signatures, the self-attested completion, the external verifier's
receipt and detached signature, and the rebuilt external attestation.  The runner
substitutes only the entrypoint copy
inside the sealed pack and rejects a changed adapter or provider-client executable
before launch.
Future evaluated agents will receive opaque IDs and one requirement.  Primary
graders will receive only a physically separate, exact-positive-allowlist
export containing normalized packets, the frozen prompt and rubric, a response
template, and a digest manifest.  It contains no operator mapping, completion
ledger, condition or variant labels, condition-specific workflow traces, or
execution cost, duration, token, tool-call, build-attempt, and retry metadata.
Those metrics are stored only in the digest-bound operator mapping and are
restored to the adjudicated analysis ledger after blind grading.  Both grader
responses and adjudication bind the substantive grader-input digest over the
packets, prompt, and rubric, as well as the internal grading-pack digest.  The
manifest separately hashes the response template and distributable-payload
aggregate, while verification reconstructs every expected byte.  The condition-specific workflow artifacts and
their common compliance pass/fail manipulation check follow the same
operator-only boundary.

Each future run must also emit a hash-bound workflow-artifact record.  Compile-only
has no condition-specific evidence file, source-aware must retain a run-local
`blueprint.md`, and ABRL must retain a target contract, blueprint, failure
ledger, and promotion-gate log.  The current checker verifies only the required
files, paths, and hashes; it does not prove that the named workflow was actually
followed.  Primary graders will not see the condition-specific files or the
common workflow-compliance pass/fail value; the latter is restored only in the
post-adjudication analysis ledger.

Before the 450 runs, the following are mandatory:

1. complete the two-layer source-contract review gate described below, without
   any benchmark outcome being observed;
2. fill and freeze every field in `execution-template.json`;
3. materialize and verify a content-addressed sealed pack;
4. freeze a real adapter command/container, its entrypoint and host-runtime
   bytes, and pass forbidden-path/string,
   budget, trace, and sandbox isolation probes;
5. run three real-provider/real-sandbox runs (one case × three conditions × one
   replicate) as infrastructure-only smoke tests excluded from the primary 450;
6. freeze a digest-pinned checker image and canonical launcher implementing the
   tracked controller/worker-separation contract, then pass all seven isolation
   probes;
7. hash-seal `complete_450_no_replacement_no_imputation_v1` and its completion-
   ledger builder, then materialize the 450-ID completion ledger;
8. atomically materialize the operator grading pack, create and verify its
   physically separate grader-only export, and freeze the target-aware analysis
   code.

## Two-layer human source-contract prerequisite and external trust anchor

The repository contains only result-free protocols, preparation/validation code,
and adversarial tests.  It contains no real reviewer identity, qualification
evidence, private escrow record, signer key, signature, completed review, receipt,
externally validated attestation, or real public signer trust anchor.  Every
corresponding evidence path in
`execution-template.json` remains `UNSET`.

The packet preparer can now materialize both the unchanged three-file machine
packet and a deterministic role-separated dispatch kit:

```text
python tools/prepare_target_drift_human_contract_review.py \
  --output ABSOLUTE-EMPTY-CORE-PACKET \
  --dispatch-output ABSOLUTE-EMPTY-DISPATCH-KIT
python tools/prepare_target_drift_human_contract_review.py \
  --verify-dispatch ABSOLUTE-DISPATCH-KIT
```

Each reviewer directory contains only a human-readable guide, one unfilled
response, the frozen review protocol, and a four-source HTTPS/SHA-256 index with
all 30 exact locators.  It excludes the other reviewer, adjudication, operator
material, model runs, grades, conditions, metrics, and outcomes.  The adjudicator
starter is withheld until both reviewer responses have been frozen.  The operator
directory carries the unchanged core packet plus result-free registry, receipt,
and trust-anchor templates.  `--verify-dispatch` reconstructs the kit from the
current frozen inputs and rejects any changed, missing, added, linked, or
role-misrouted file.  Source PDFs are not redistributed; each reviewer must
acquire the named public bytes independently and verify the frozen hash.  A
successfully verified dispatch kit is preparation evidence only, never a
completed review or a production-eligibility claim.

The first layer machine-checks the self-attested review bundle against the exact
frozen challenges and paired requirements.  Every production-eligible case must
use exactly `match`, `source_critical_change`, and `exact`; reviewer disagreement
is recomputed over every decision and every target-card field.  Any
`needs_correction`, `not_auditable`, or noncanonical final card yields only
`benchmark_amendment_required`.  A clean bundle yields the deliberately limited
status
`self_attested_review_bundle_complete_external_identity_qualification_verification_required`.
That status still records both `independent_human_expert_validation_complete=false`
and `production_execution_eligible=false`.

The second layer requires a preregistered four-role Ed25519 registry (reviewer A,
reviewer B, adjudicator, and a distinct external verifier), exact OpenSSH
`allowed_signers` bytes, detached signatures over the three canonical review
payloads, and the external verifier's detached signature over a canonical
identity/qualification/independence/COI escrow receipt.  Successful validation
returns only
`externally_signed_identity_qualification_attestation_complete`, while retaining
`cryptographically_proven_human=false` and
`production_execution_eligible=false` as well as
`production_execution_eligible_from_this_layer_alone=false`.  OpenSSH establishes
registered-key possession and signed-byte integrity; the human, qualification,
independence, COI, and pre-outcome assertions remain the external verifier's
attestation, not cryptographic facts or a trusted timestamp.

Neither layer supplies its own trust root: one operator can generate four keys
and a self-consistent registry.  Production preseal therefore additionally
requires a separately tracked public trust-anchor record whose exact bytes were
already present at a named strict-ancestor Git commit.  The anchor binds the raw
and canonical registry hashes, exact `allowed_signers` hash, external-verifier
principal and Ed25519 fingerprint, and public escrow locator and receipt hash.
Live preseal also requires the anchor-declared credential-free GitHub origin URL, queries
`refs/heads/main`, and checks that the anchor commit is reachable from that live
public ref; a missing network check fails closed.
The pack carries a minimal Git-object proof of the ancestor chain and tracked
anchor path, so `--verify-pack` can recheck this membership from packed bytes
without consulting an operator-local checkout.  The packed proof cannot replay
the earlier online visibility query; it binds the repository/ref/commit locator
for independent rechecking.  Git object identity, the live ref query, and ancestry
show only public byte availability and ordering under the host Git/TLS boundary.
They do not prove trusted time,
human identity, qualification, independence, or COI; those claims still depend
on the verifier's signed attestation and escrow evidence.

The checked-in anchor contract contains no real anchor.  Its template values are
all `UNSET`, so the current normal production preseal is deliberately blocked.
The four-ephemeral-key positive signature fixture is labeled
`excluded_fixture_unanchored`; even when all signatures verify, it must retain
`combined_prerequisite_satisfied=false` and cannot set any production eligibility
field.

During a future production preseal, the finalizer first rebuilds the self-attested
completion and requires no amendment and exact frozen cards, reruns the SSH
external validator, and verifies the prior public trust anchor.  Only after all
three checks succeed may the execution layer derive
`human_source_contract_prerequisite_satisfied=true`.  Materialization snapshots
the exact validated bytes, rewrites operator-local source-manifest, adapter,
runtime, auth, checker, and human-review paths to portable `SEALED/`,
`HOST-BOUND/`, or `OPERATOR-SECRET/` locators, includes 17 hash-bound review-chain
objects plus the three packet files in the aggregate, and includes the
preparation/finalization/validation code and tests under `execution_code/`.
`--verify-pack` rejects any other file set, rejects duplicate JSON keys, and
reruns both validators and the trust-anchor proof from packed protocol,
challenge, paired-card, review, signature, receipt, anchor, and Git-proof bytes;
it never trusts a status summary alone.  Before those checks, `--verify-pack` requires the live
materializer and both human-review validators (plus their packet preparer) to be
byte-identical to the copies and hashes sealed under `execution_code/`; the
invoked Python runtime, host OpenSSH, and host Git implementations remain explicit host trust
anchors rather than facts proved by the pack.  The anonymous supplement allowlist includes only the result-free
protocols, trust-anchor contract, tools, and tests, never a future real anchor or
  Git proof, reviewer, registry, escrow, receipt, or signature material.

The current v2 readiness check is explicit because the preserved v1 suite has
a different template and a different unresolved-field count:

```text
python tools/prepare_target_drift_execution.py --config evaluation/target-drift-v2/execution-template.json --check-template
```

At this checkpoint the template status remains `template_unfrozen`; the
command reports `ABRL-TARGET-DRIFT-V2` and 161 unresolved placeholders across
machine, human, and provenance fields.  The unqualified command intentionally checks v1;
its 26-field report is not evidence that v2 is closer to execution.  No
primary or external model run has been performed.

The grader-packet materializer, grader-only exporter, and packet-order seed are
frozen before model execution.  Packet contents and their aggregate digest are
produced only after neutral checking.  Before export or assembly, the internal
pack is reconstructed byte for byte from the sealed 450-run manifest, the
current complete ledger, and every current result-eligible checked-run evidence
chain; its deterministic shuffle, grade IDs, packets, operator mapping, and
manifest must match.  The internal pack and the separate grader-only export are
both validated before any primary grader sees them.  The
operator-only mapping retains semantic labels, execution metrics, and the
workflow-compliance manipulation check; it is digest-bound with the packets but
is absent from the exact export tree.  The exporter rejects extra files or
directories, path aliases, multiply linked files, invalid packet paths,
duplicate JSON keys, non-finite JSON values, and recursive blindness failures.
It provides atomic visibility of a completed tree but does not claim
power-loss durability, protect a concurrently created empty destination directory
on POSIX, enforce administrator behavior or distribution ACLs, or prevent
inference from proof style.  Production materialization therefore requires one
operator-owned output parent.  The two complete blind response files and
an adjudicator file for every binary-label or structured source-field
disagreement are then combined by the sealed
`tools/assemble_target_drift_grades.py`.  The ledger records the assembler,
response, adjudication, and combined-input digests.  The target-level analyzer
does not trust that ledger alone: it accepts the same two responses and
adjudication, reruns the current hash-matched sealed assembler in a fresh output
directory, and requires an exact byte match before inference.  It then applies
Benjamini--Hochberg adjustment to the prospectively specified secondary
endpoints.

No pilot output may enter the final result set, and no challenge may be
replaced after difficulty is observed.

The missing-run policy is now executable but still result-free.  After an
individual adapter or checker failure, the remaining prospectively specified runs continue;
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
source manifest with exact local PDF paths.  The result-free source helper can
perform that last acquisition step from the four checked-in HTTPS URLs:

```text
python tools/fetch_target_drift_sources.py --cache-root ABSOLUTE-EXTERNAL-CACHE --output-manifest ABSOLUTE-EXTERNAL-SOURCES.json
python tools/fetch_target_drift_sources.py --cache-root ABSOLUTE-EXTERNAL-CACHE --output-manifest ANOTHER-ABSOLUTE-EXTERNAL-SOURCES.json --offline
```

The helper cross-checks every expected digest against the frozen challenge
bank, accepts only HTTPS and `application/pdf`, bounds the response size,
checks the PDF header and EOF marker, verifies SHA-256 before atomically
publishing `sha256/<prefix>/<digest>.pdf`, and refuses to place either the
cache or the generated machine-local manifest inside the Git repository.  It
never commits or redistributes the PDFs.  The offline form performs no network
request and verifies an existing cache from bytes.  A successful helper run
only prepares operator-local source inputs; it does not freeze the execution
configuration, run a model, satisfy the real smoke, or close any of the 450
production runs.

Bind the canonical
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
candidate in `tools/launch_target_drift_agent_container.py`.  Every enabled
mode is provider-free and result-ineligible.  The reserved `production-execute`
mode validates a final-seal schema and then stops before credential inspection
or Docker launch because the tracked production gate is false.  The original probe verifies the local
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

The adjacent `production-fixture` mode closes a different code-level gap
without claiming production safety.  A checked-in manifest supplies one prompt,
one request, and one tiny Lean workspace.  Root copies those immutable bytes to
`/agent/run` tmpfs, brokers only the literal fake auth descriptor to uid/gid
`10002`, and launches the hash-bound
`target_drift_agent_action_driver.py`.  The driver consumes and closes the
descriptor, creates a temporary worker-owned auth-only directory, and invokes
the actual in-image `codex_target_drift_adapter.py`.  That adapter is pointed at
the hash-bound local `target_drift_agent_fake_codex.py`, not the native provider
client.  Docker network is `none`; the fake executable imports no network or
subprocess client, writes a blocked fixture result, and emits deterministic
zero-usage Codex JSONL.  After independent response/trace/output validation,
root copies the exact adapter and output files to a separate host bind and
writes a receipt; the host launcher re-hashes every copied byte.  This exercises
the production-shaped adapter path, not a provider/model call.

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

Before the schedule CLI advances primary runs, it replays the
bound three-condition smoke evidence and requires all three real `codex_cli`
provider invocations, observed usage, completed adapter termination, and
production checker receipts.  A missing, failed, tampered, result-free, or
differently bound smoke ledger stops the schedule before any of the 450 primary
runs.  After that gate, the runner executes runs in sealed presentation order,
never revisits a terminal state, and continues with the remaining prospectively specified
IDs after a run-level failure.  It writes the completion ledger and exits nonzero
when fewer than 450 runs are production-result-eligible:

```text
python tools/run_target_drift_schedule.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json --smoke-plan SMOKE-PLAN.json --smoke-ledger SMOKE-LEDGER.json
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
python tools/export_target_drift_grader_pack.py create --pack FROZEN-PACK --runs-root RUNS --grading-pack GRADING-PACK --output GRADER-ONLY
python tools/export_target_drift_grader_pack.py verify --pack FROZEN-PACK --runs-root RUNS --grading-pack GRADING-PACK --grader-export GRADER-ONLY
python tools/assemble_target_drift_grades.py --pack FROZEN-PACK --runs-root RUNS --grading-pack GRADING-PACK --grader-export GRADER-ONLY --grader-response GRADER-A.json --grader-response GRADER-B.json --adjudication ADJUDICATION.json --output GRADES.json
python tools/analyze_target_drift_execution.py --pack FROZEN-PACK --runs-root RUNS --completion-ledger COMPLETION-LEDGER.json --grading-pack GRADING-PACK --grader-export GRADER-ONLY --grades GRADES.json --grader-response GRADER-A.json --grader-response GRADER-B.json --adjudication ADJUDICATION.json --output ANALYSIS.json
```

Distribute only `GRADER-ONLY`, never `GRADING-PACK`.  Its manifest distinguishes
export schema 1, packet schema 1, and grader-response schema 2; response schema
1 is rejected rather than silently migrated.  Each primary grader makes
an independent copy of `response-template.json`, preserves all three digest
fields, replaces the assigned grader ID, and fills exactly one record per
packet.  The adjudicator receives the verified export plus the two completed
responses and records only conflicts.  Its file has schema version 2 and this
shape (all placeholders must match the frozen config and export manifest):

```json
{
  "schema_version": 2,
  "adjudicator_id": "FROZEN_ADJUDICATOR_ID",
  "grading_pack_sha256": "INTERNAL_GRADING_PACK_DIGEST",
  "grader_export_sha256": "SUBSTANTIVE_GRADER_INPUT_DIGEST",
  "grader_prompt_sha256": "FROZEN_PROMPT_DIGEST",
  "grades": []
}
```

`grades` must cover exactly the packet IDs whose binary labels or structured
source-critical field lists disagree; the assembler rejects missing, extra, or
duplicate adjudications.  `GRADING-PACK`, `GRADER-ONLY`, `GRADES.json`, and
`ANALYSIS.json` must remain outside the sealed pack, run root, and each other;
single-file outputs are staged, fsynced where supported, and published without
clobbering an existing path.  The directory publication gives atomic visibility
of a complete tree, not a claim of power-loss durability on every filesystem.

These commands expose executable code paths; they do not supply a provider,
agent image, final published production checker image,
credentials, budget choices, or grader identities.  The current local gate
includes target-drift component tests covering deterministic assignment, seal hashing,
opaque prompts, manifest/digest checks, selected fail-closed paths, a synthetic
450-record analysis, and complete/incomplete/tampered completion-ledger cases.
The completion ledger is an operator-trusted consistency check over frozen
bytes and recorded artifacts, not an attestation against an operator who can
execute modified Python before its bootstrap checks.  Ordinary source or
sealed-copy drift fails closed; adversarial code-execution provenance requires
an external trusted launcher or equivalent attestation.
The deterministic fake fixture and two local
fail-closed probes are nonexperimental and do not pass the real-infrastructure
gate.  `tools/prepare_target_drift_smoke.py` and
`tools/run_target_drift_smoke.py` provide a separate operator-only lane for the
prospectively specified one-case-by-three-condition check.  The plan binds one matched
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
with a reviewed real-provider action remains required before the real smoke
runs.  The result-free agent-image workflow is designed
to combine the exact provider client, offline Lean cache, adapter, and PID-1
controller and to rerun the destructive lifecycle probe, but it supplies no
credential and makes no model call.  The source-level outer-boundary candidate
adds root-only control, a fake single-file credential, and a disposable
non-root workspace.  The adjacent excluded-provider execution component now
exercises the same PID-1/controller boundary with the exact tracked
`agent-excluded-execution-request.json` and hash-bound argv in
`agent-excluded-execution-contract.json`.  It uses Docker network `none`, the
literal fake auth sentinel, and the in-image excluded adapter; it validates a
one-event zero-usage trace, production-shaped response and five-file output
surface, immediate root descriptor closure, worker descriptor consumption, and
clean PID-1 child exit.  The request fixes `primary_result_eligible=false`, all
provider/credential/network access false, model-call budget zero, and zero
token/tool/build/cost budgets.  The adapter imports no provider, network, or
subprocess client and performs no Lean build.

The fixed production-action fixture goes one step further through the real
Codex adapter while remaining permanently result-ineligible.  Its canonical
Linux command is:

```text
python tools/launch_target_drift_agent_container.py --component-mode production-fixture --image-sbom AGENT-IMAGE-SBOM.json --agent-input evaluation/target-drift-v2/agent-production-action-fixture --auth-sentinel FIXED-FAKE-AUTH-DIRECTORY/auth.json --control-output FRESH-ROOT-CONTROL-DIRECTORY --artifact-output FRESH-COPYBACK-DIRECTORY --apparmor-source evaluation/target-drift-v2/agent-codex-native.apparmor --report FRESH-PRODUCTION-FIXTURE-REPORT.json --probe-commit FULL-GIT-COMMIT
```

`agent-production-action-contract.json` also defines the reserved final seal:
Linux, canonical Docker identity, published final digest/SBOM, frozen execution
config, provider/model/settings/prices/budgets, per-run input manifest, final
image and PID-1 probes, a real single-file credential-visibility probe that
records neither secret bytes nor a secret-derived digest, provider-only egress
enforcement, and the permanently result-ineligible three-condition real smoke.
Candidate, fake, fixture, result-free, unsealed, or `UNSET` bindings are rejected.
Even a structurally valid seal cannot execute in tracked source:
`production_execution_enabled=false` remains the hard gate until those external
Linux final-digest checks are reviewed.  Opening that data gate is still not
enough: a separate reviewed code change must implement and enable the real
controller action; tracked source contains only the strict interface candidate.

The canonical component entrypoint is:

```text
python tools/launch_target_drift_agent_container.py --component-mode excluded-execute --image-sbom AGENT-IMAGE-SBOM.json --agent-input EXACT-EXCLUDED-REQUEST-DIRECTORY --auth-sentinel FIXED-FAKE-AUTH-DIRECTORY/auth.json --control-output FRESH-ROOT-CONTROL-DIRECTORY --apparmor-source evaluation/target-drift-v2/agent-codex-native.apparmor --report FRESH-EXCLUDED-EXECUTE-REPORT.json --probe-commit FULL-GIT-COMMIT
```

The request directory must contain only `request.json`, byte-for-byte equal to
the tracked excluded request.  The auth file must contain only the fixed
`RESULT_FREE_SENTINEL_DO_NOT_USE` fixture bytes; any other bytes fail before
Docker starts.  This command is component evidence only.  It cannot consume a
real credential, cannot enter the smoke or 450-run ledger, and does not change
`execution_not_started`.  A real-provider action must still be separately
reviewed, frozen, credential-visibility probed, and lifecycle-probed on the
published production digest.

The provider-disabled execute path is implemented and component-tested, but it
has not been run with a real provider/credential action and is permanently
result-ineligible.  The production-action fixture is source- and unit-tested,
but the updated image/workflow has not yet produced Linux final-digest fixture
evidence; any future passing fixture will remain permanently result-ineligible.
No real three-condition smoke, final pack, primary model
run, grader response, grade ledger, or analysis output exists.

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
plan and the pre-execution-amended primary protocol; the independent validator
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

An adjacent real-checkout preflight candidate is now implemented without
changing or resealing that frozen result-free plumbing.  The candidate contract
`leanflow-real-adapter-contract.json` pins LeanFlow commit
`72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d`, its Git tree, release `0.3.0`,
`uv.lock`, license, project metadata, and the source bytes that expose the
current clean-room/toolset policy.  The pinned file hashes are the canonical LF
Git blob bytes.  A fresh local source tree can be materialized without
platform CRLF conversion as follows (the target directory must not exist):

```bash
LEANFLOW_SOURCE_ROOT=/absolute/new/leanflow-pinned-source
git init "${LEANFLOW_SOURCE_ROOT}"
git -C "${LEANFLOW_SOURCE_ROOT}" remote add origin https://github.com/epfl-lara/LeanFlow
GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_TERMINAL_PROMPT=0 \
  git -c credential.helper= -c core.askPass= -c submodule.recurse=false \
  -C "${LEANFLOW_SOURCE_ROOT}" fetch --no-tags --depth=1 origin \
  72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d
git -c core.autocrlf=false -c core.hooksPath=/dev/null \
  -c submodule.recurse=false -C "${LEANFLOW_SOURCE_ROOT}" \
  checkout --detach --force 72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d
git -C "${LEANFLOW_SOURCE_ROOT}" remote remove origin
```

Given that exact canonical checkout, the command below performs only two
allowlisted local `git rev-parse` queries and byte checks:

```text
python tools/leanflow_target_drift_adapter.py --mode result-free-preflight --contract evaluation/target-drift-v2/leanflow-real-adapter-contract.json --source-root ABSOLUTE-PINNED-LEANFLOW-CHECKOUT --response FRESH-PREFLIGHT-RESPONSE.json --trace FRESH-PREFLIGHT-TRACE.jsonl
```

The Python adapter has no credential-reading path and imports or calls no
network or provider client.  It does start the locally resolved Git executable
for the two identity queries; its SHA-256 is recorded but not pre-frozen, and
neither that executable's OS-level behavior nor OS-level network isolation is
attested.  It does not start LeanFlow or formalization, and `--mode execute`
fails before reading the contract, source checkout, or output paths.  The
preflight deliberately reports the production gate closed: pinned LeanFlow's
`--clean-room` retains general web/paper search and its proving toolset contains
web access, while the external comparison requires research, web, and
public-repository search to be disabled.  A disclosed no-web upstream interface
or audited overlay plus provider-only network containment remains mandatory
before a real, permanently result-ineligible smoke.  Passing this preflight is
not a LeanFlow run or comparison result.

The earlier source inventory used platform-transformed CRLF working-tree bytes
(including obsolete `uv.lock` SHA-256
`1239513509ee29a580c3f3f293e86dd16f77c298dbe9a99cba6aaaf93a1b0dd5`).
Those hashes and every response, trace, or attestation bound to that obsolete
inventory are invalid as source-preflight artifacts.  They must not be cited
or mixed with the canonical-LF contract.

The tracked GitHub Actions workflow
`.github/workflows/leanflow-source-preflight.yml` makes that same boundary
reproducible on an Ubuntu runner.  It is named **LeanFlow pinned-source
preflight (result-free, not results)** and performs these operations only:

1. check out ABRL with credential persistence disabled and run the adapter and
   independent-validator component tests;
2. initialize an empty Git repository, fetch exactly public LeanFlow commit
   `72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d` with terminal prompting and
   credential helpers disabled, materialize the canonical LF Git bytes with
   `core.autocrlf=false`, detach at that commit, and remove the remote;
3. run the existing adapter in `result-free-preflight` mode, then independently
   validate the response/trace schemas, commit, tree, lock, pinned-file count,
   cross-file hashes, ordered events, zero model calls, and every false
   eligibility/execution/outcome flag; and
4. only when `github.repository` is exactly
   `DakeBU/Auto-Bandit-RL-Proof-In-Sleep` and the event is a `push` to
   `refs/heads/main`, upload the response, trace, and validation attestation
   under an artifact name containing
   `source-preflight-not-results`; pull requests and manual dispatches run the
   same checks but upload no artifact.

The workflow never installs or starts LeanFlow, invokes a model/provider,
reads a provider credential, or runs a general network client.  Its only
command-step source acquisition is the exact public Git fetch; the ABRL
checkout and main-push-only artifact upload remain explicit GitHub control-plane
actions.  Checkout is pinned to
`actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803` (v6) and upload
to `actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02`
(v4); those action commits are distinct from the pinned LeanFlow source
commit.  The uploaded files contain no Lean proof, score, cost, checker
outcome, or comparison result.  The validator itself imports neither
`subprocess` nor a provider/network client.  It first requires the entire
workflow byte stream to match SHA-256
`69cb85f9cb19135890f50bdf5e82fbc80740b0b779162f9abf178824c0961323`;
therefore any additional job, step, environment field, or run command changes
the hash and fails closed.  Structural checks and negative tests additionally
cover dotted and bracket-form secret references, `github.token`, inline
`python -c`/`urllib`, general downloaders, dependency runners, LeanFlow
commands, privileged pull-request triggers, extra source URLs, changed action
SHAs, and a changed LeanFlow object ID.
`.gitattributes` fixes this workflow path to `text eol=lf`; tests require that
Git attribute, reject CRLF-transformed workflow bytes, and verify that the
expected SHA-256 is computed over the same canonical bytes accepted by Git's
clean filter and used by an Ubuntu checkout.

This exact-byte validator is a drift check against the currently reviewed
trusted-main workflow bytes, not an unforgeable provenance mechanism.  A pull
request can modify the workflow, validator, tests, and expected hash together;
therefore a green pull-request check or a locally generated attestation is not
CI evidence by itself.  The attestation records either explicit
`local_non_evidence` provenance or the GitHub Actions `github.sha`, `run_id`,
`run_attempt`, event, ref, workflow name/ref, repository, and run URL.  Even on
a main push it keeps `ci_evidence_eligible=false` internally because that file
is not self-authenticating.  Treat a run as CI source-preflight evidence only
after independently confirming all of the following:

- the run URL belongs to the trusted repository and its protected `main` push;
- `github.sha` contains the reviewed workflow and validator bytes;
- the run used the two pinned action commits above; and
- the artifact digest is the `artifact-digest` emitted by that run's pinned
  upload action.  The job summary records the trusted-main run URL and digest.

Pull-request, manual-dispatch, and local outputs remain check-only non-evidence
and are never promoted by copying their JSON files elsewhere.  A fork
repository slug is rejected by the provenance validator and its main push is
ineligible for the upload step.  This source
preflight deliberately adds no no-web overlay: that
production gate remains false and still precedes any real-infrastructure
smoke or 30-run calibration.

The result-free workflow boundary and artifact grammar can be checked locally
without acquiring LeanFlow source:

```text
python -m unittest tools.test_leanflow_target_drift_adapter tools.test_leanflow_source_preflight -v
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
These are code-level constraints, not a passed production isolation probe. The
excluded-provider execute path tests the sealed request/argv and
response/trace/output/PID-1 plumbing without API use; the fixed production-action
fixture additionally traverses the real Codex adapter and verifies copied-back
artifacts through a local fake executable.  Neither makes the current host a
production agent sandbox: the enabled real-provider action, exact
provider client, remote-model attestation, credential boundary, published agent
image, final visibility/network/process probes, prices, budgets, and
three-condition smoke remain unfrozen and unrun.
`tools/fake_target_drift_adapter.py` and
`tools/fake_target_drift_cache_prelude.py`, and
`tools/fake_target_drift_checker_sandbox.py` are deterministic fixture helpers
for local plumbing experiments; no tracked full-chain smoke is claimed.  They
are not a model provider, sandbox, or cache-image attestation and cannot satisfy
the real-execution gate.
