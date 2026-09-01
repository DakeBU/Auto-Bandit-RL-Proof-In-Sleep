# Hierarchical Harness

ABRL currently retains the hierarchical upper/middle/lower/reviewer harness as
its default. A master–worker arm is now available for matched experiments with
disjoint routes, and `adaptive` chooses the least-sampled arm until sufficient
reviewed evidence exists. This is an experiment, not a claim that parallelism
is already better. See `docs/harness_self_comparison.md`.

## Roles

| Role | Output | Rejection criteria |
| --- | --- | --- |
| Upper director | theorem frontier, route decision, active proof leaves | vague theorem, hidden assumptions, no gate |
| Middle formalizer | conversion window, proof obligation ledger, memory refresh | Lean/prose mismatch, stale theorem card, missing cited result |
| Lower proof architect | small Mathlib-ready proof-DAG decomposition and local proof sketch | changes theorem, repeats stale route |
| Lower Lean worker | compiled leaf lemma or focused blocker | `sorry`, target weakening, unrelated refactor, frequent proof-route churn |
| Lower retrieval worker | theorem-card and cited-result packet | local path citation, unverified claim promoted |
| Reviewer | build gate, target-fidelity audit, status classification | uncompiled proof, hidden assumption, missing memory |

Middle decides whether a leaf should go directly to a Lean worker or first to a
natural-language prover.  The natural-language route is useful only when it
sharpens a statement, exposes a missing assumption, or provides a proof route
that can then become a Lean packet.  It is not certified memory.

## Cycle Contract

Each cycle should produce:

1. `runs/<run-id>/00_context.md`;
2. upper and middle prompt outputs;
3. one or more lower leaf attempts;
4. reviewer decision;
5. `runs/<run-id>/memory_digest.md`;
6. updated `proof-obligations/` and `research-wiki/retrieval-index/`.

Each active lower leaf must include the theorem statement, local APIs, intended
proof route, hidden regularity contracts, and Mathlib candidacy classification.
Persistent failure on a leaf should stop broad proof search and trigger a
statement/hypothesis/counterexample audit.

The current visual map for this rule is
[`docs/lemma_leaf_network.md`](lemma_leaf_network.md).  Agents should use it to
keep foundational Mathlib candidates, bandit wrappers, and final theorem
surfaces separated.

Upper and middle agents should also attach each theorem target to the broad
theory tree in `research-wiki/theory-tree/bandit-theory-tree.md`, with a
textbook/source card, a scenario card, LML cards when available, and Mathlib
retrieval cards for reusable leaves.

The fine-grained foundation map is
`research-wiki/theory-tree/mathlib-foundation-leaf-map.md`.  If a proof route
touches measure theory, kernels, conditioning, concentration, FTRL, Tsallis
entropy, or self-normalized inequalities, middle should decompose it against
that map before lower proof work.

The adaptive workflow and memory-card boundaries are documented in
`docs/adaptive_harness_design.md`.

Use the current default:

```bash
python3 tools/bandit.py run-cycle TASK_ID --lower-count 3
python3 tools/bandit.py memory-refresh TASK_ID --run-id latest
```

Use `--lower-count 1` unless multiple lower routes have distinct route
fingerprints, disjoint owned files, and explicit expected information gain.
For a matched master–worker arm, provide the same experiment id and target
fingerprint used by the hierarchical arm:

```bash
python3 tools/bandit.py run-cycle TASK_ID \
  --harness master-worker \
  --experiment-id AB-001 \
  --target-fingerprint SHA256_OF_FROZEN_TARGET \
  --lower-count 3 \
  --parallel-route-json run-presets/harness-comparison-routes.example.json
```

To execute prompts with an external CLI wrapper:

```bash
python3 tools/bandit.py sleep-run TASK_ID \
  --cycles 2 \
  --execute \
  --agent-cmd 'codex exec --cd {root} < {prompt}' \
  --check-each-cycle \
  --stop-on-error
```

The placeholder `agent-cmd` is intentionally generic.  Alternatively,
`--agent-profile agent-profiles/<name>.json` can route upper, middle, lower,
and reviewer prompts to different commands.

## Acceptance Rule

Only a local Lean declaration that passes:

```bash
lake build && lake build Tests
```

can enter certified memory.  External proofs, theorem cards, and prose sketches
remain in insight memory until they are imported or ported and build-tested.

General leaf lemmas should be written to Mathlib standards.  Project-local
wrappers may remain in ABRL, but the reusable mathematics should be packaged as
future Mathlib contribution material.
