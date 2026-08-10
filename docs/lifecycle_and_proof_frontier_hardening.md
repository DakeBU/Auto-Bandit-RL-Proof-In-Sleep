# Lifecycle And Proof-Frontier Hardening

Status: `accepted`, shadow and repository gates passed, live autonomous
execution disabled.

This layer makes the active ABRL objective, one ready leaf, bounded memory, and
last verifier evidence explicit. It does not change any Lean theorem statement
and does not start a detached proof run.

## Audit Baseline

The hardening audit was run on branch `codex/abrl-proof-progress` at commit
`270ac124e72e1ed0d0d93c92a8e0af516f54149d`.

- No repository-root `AGENTS.md` exists. Role guidance lives in `.agents/skills/`
  and the harness documents.
- The current source worktree, task cards, conversion windows, proof
  obligations, blueprints, theorem indexes, and Lean build scripts are present.
- The supplied prompt's 47-row ETC/EXP3 baseline is historical. The live
  `runs/trials.jsonl` had 236 rows at the initial audit: 117 accepted, 110
  compiled, 5 running, 2 queued, 1 failed, and 1 rejected.
- Legacy trial rows do not contain `changed_files`, `statement_hash`,
  `parent_id`, `route_fingerprint`, or structured `verifier_evidence`. New
  `trial-log` and `run-cycle` rows carry these fields; old rows remain unchanged.
- The latest digest found under `runs/` names
  `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-REFINED-CORRUPTED-REWARD-LAW-REGRET`.
  At audit time the last terminal trial named
  `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-AE-FINITE-EVENTUAL-IMMEDIATE-STOPPING-AND-IN-MEASURE-CONSISTENCY`.
  The shadow analyzer therefore reports a real stale-memory/frontier mismatch.
- The newer compiled fixed-index integrable expected-upper-bound task existed
  in tasks, proof obligations, Lean, tests, docs, and indexes but was absent from
  trials. It is recorded append-only during lifecycle reconciliation rather
  than by rewriting historical rows.
- `docs/completion_gap_audit.md` still records broader unfinished bandit/RL
  routes. A theorem card or proof weapon remains evidence only until a local
  Lean declaration compiles.

## Authoritative Files

| File | Contract |
| --- | --- |
| `runs/active_frontier.json` | one root objective, current leaf, dependency DAG, statement hash, source status, last verifier, memory policy, and shadow gate |
| `runs/lifecycle_memory.jsonl` | append-only typed memory records |
| `runs/lifecycle_sessions.jsonl` | append-only session-tree events with stable entry and parent ids |
| `.abrl/lifecycle_state.json` | deterministic current pointer, branch summaries, transaction/tool state, and directive queue; not conversational memory |
| `runs/statement-fences/*.json` | immutable Lean declaration headers and explicit source assumptions |

`runs/active_frontier.json` is the only authoritative active-frontier record.
Conversation summaries and compacted context are advisory.

## Shadow Evidence

The read-only analyzer was run on a copied current log. It wrote no state and
reported the stale digest described above. A three-transition replay retained
the same selected frontier at every transition while changing prompt size as
follows:

| Transition | Whole-history characters | Bounded-memory characters |
| --- | ---: | ---: |
| reciprocal-threshold capped first passage | 165419 | 1587 |
| inverse-sqrt capped first passage | 167136 | 1865 |
| inverse-sqrt unbounded `hittingAfter` | 168735 | 1621 |

The bounded packet defaults to the last five task- and role-relevant active
records plus explicitly requested `verified_lemma` ids. Superseded records and
the complete history are excluded by default.

```powershell
python3 tools\bandit.py frontier-shadow --trials tmp\lifecycle-shadow\trials.jsonl
python3 tools\bandit.py frontier-replay --trials tmp\lifecycle-shadow\trials.jsonl --transitions 3
```

The historical ETC-digest versus EXP3-frontier mismatch from the supplied
prompt is retained as a unit-test fixture. The live analyzer never hard-codes
that obsolete result.

After the stale condition was recorded as `source_fact` memory, the bounded
packet was written to
`runs/lifecycle-proof-frontier-hardening-2026-08-06/memory_digest.md`. The final
live shadow report has the digest task, accepted trial, and active frontier all
at `HARNESS-LIFECYCLE-PROOF-FRONTIER-HARDENING`, with zero mismatches.

## Typed Memory

Allowed record types are:

- `verified_lemma`
- `partial_route`
- `failed_path`
- `source_fact`
- `decision`
- `checkpoint`

Every record has a stable content id, creation time, provenance, task,
assumptions, declaration/file, status, verifier evidence, roles, details, and
explicit supersession metadata. Explicit packet retrieval accepts only active
`verified_lemma` records with a verified/compiled/accepted status.

Local-first Mathlib retrieval is recorded with the query, ordered candidates,
rejection reasons, and any compiled scratch result:

```powershell
python3 tools\bandit.py retrieval-record `
  --task TASK `
  --query "condExpKernel map" `
  --candidate Local.Declaration `
  --rejection "Other.Candidate=wrong sigma-algebra" `
  --compiled-scratch "lake env lean tmp/Scratch.lean" `
  --provenance research-wiki/retrieval-index/local_lean_declarations.json
```

LeanAgent is not imported or trained by this harness.

## Dependency Dispatch

The frontier stores a small DAG. A leaf is ready only when every named
declaration or assumption has a satisfying status. A blocked result records
the exact missing dependency and a dependency fingerprint. The same blocked
leaf cannot be dispatched again until that fingerprint changes. A running leaf
also rejects duplicate dispatch.

`frontier-dispatch` additionally requires `shadow_gate.status = passed`.
Parallel lower dispatch defaults to one worker. More than one lower requires a
JSON proposal with at least two distinct route fingerprints, disjoint owned
files, and explicit expected information gain. The lower-to-reviewer gate is
otherwise unchanged.

## Statement Fence And SafeVerify

`statement-fence` captures the complete normalized declaration header,
including result `let` and `letI` assignments. `safe-verify` checks:

1. the current declaration header has the exact stored SHA-256 hash;
2. every named source assumption is still present;
3. scanned Lean files introduce no `sorry`, `admit`, custom `axiom`, or
   `postulate`.

The current fence covers
`selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold`
and preserves `(hhorizon : 4 < mdp.horizon)`. This is an immutable source
certificate for lifecycle checks, not a new theorem.

## Runtime Contracts

- Session history is append-only. Stable entry ids include session, sequence,
  parent, type, and payload. Forks preserve the common parent and record the
  abandoned reason and branch summary. Restore appends a new child to the
  stored branch head instead of overwriting history.
- Task state is separate from conversation. Compaction is disabled unless an
  exact measured provider-usage value reaches the configured threshold. When
  enabled it retains a complete recent tail plus exact declarations, paths,
  errors, source assumptions, read/modified files, hashes, DAG, and gate data.
- The canonical-path mutation queue uses in-process locks and repository-local
  cross-process lock files. Same-path writes serialize; disjoint paths can run
  concurrently.
- Only `TransientProviderError` receives a bounded retry budget. Mathematical,
  type, and Lean-gate failures propagate immediately without transport retry.
- Steering and follow-up directives persist while a transaction runs.
  Steering is released first and marks replanning required; follow-up is
  released only after transaction settlement.
- Skill records require stable name, version, provenance, allowed roles, and
  `model_visible`. Duplicate names fail unless an explicit provenance
  precedence rule selects the winner.
- No FunSearch population, mandatory attempt count, unconditional web search,
  whole-history injection, estimated-as-exact token accounting, or automatic
  current-history compaction is introduced.

## Harness Leaf Record

| Field | Value |
| --- | --- |
| leaf | `HARNESS-LIFECYCLE-PROOF-FRONTIER-HARDENING` |
| Lean-facing statement | no Lean theorem added or changed; the source theorem header is fenced exactly |
| local APIs/imports | standard-library `tools/abrl_lifecycle.py`; thin `tools/bandit.py` commands; existing trial/task/index files |
| proof route | audit, read-only shadow reconstruction, three-transition replay, deterministic state implementation, faux-provider tests, then authoritative record |
| regularity contracts | append-only logs; canonical paths; measured usage only; explicit dependencies; immutable source assumptions; transient-only retry |
| retrieval evidence | current trials/digest/task/obligation/blueprint/index inspection; existing local declaration lookup; no external theorem activation |
| status | `accepted`; shadow replay, focused Lean, root/Tests builds, SafeVerify, 16 lifecycle tests, and 35 combined harness tests pass |
| failure policy | do not dispatch on stale/blocked state, weaken theorem statements, retry Lean failures as transport errors, or enable detached autonomous execution |

## Commands

```powershell
python3 tools\bandit.py frontier-shadow
python3 tools\bandit.py frontier-replay --transitions 3
python3 tools\bandit.py memory-packet --task TASK --role lower
python3 tools\bandit.py statement-fence --declaration DECL --file FILE --output FENCE.json
python3 tools\bandit.py safe-verify --fence FENCE.json
python3 tools\bandit.py frontier-dispatch LEAF
python3 tools\bandit.py lifecycle-event --session SESSION --event EVENT --payload-json '{}'
```

No detached autonomous run is permitted until deterministic gates pass and the
user explicitly requests execution.

The active bounded reviewer packet selects verified lemma
`mem-0726e5b5a3e57c2d` plus active checkpoint
`mem-2a7eb77e3c8be819`. Retry tests record two retries before transient success,
one retry before exhaustion, and zero retries for a mathematical failure.
