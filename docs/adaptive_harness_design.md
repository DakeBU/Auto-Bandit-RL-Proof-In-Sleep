# Adaptive Harness Design

ABRL has two target workflows:

1. complete user-specified proof technology and paper LaTeX proofs;
2. explore new bandit/RL theorem targets and construct a complete Lean proof
   plan, then close leaves one by one.

This design keeps proof weapons as planning inspiration while keeping compiled
Lean and imported theorem cards as the only reusable proof material.

The execution architecture is itself evidence-gated. The established
hierarchical route and the experimental master–worker route can be run on the
same frozen target and compared with `harness-compare`. The comparison gives
priority to reviewer-validated mathematical progress, not worker count or
command success; GPT receives the deterministic report and structured logs as
an interpretation packet. Until at least two matched experiments exist, the
current default is retained and `adaptive` only selects the next arm to sample.

The deterministic lifecycle implementation is documented in
`docs/lifecycle_and_proof_frontier_hardening.md`. Its
`runs/active_frontier.json` record is authoritative for the current leaf,
dependency readiness, statement hash, bounded-memory policy, and last verifier
evidence. Run `frontier-shadow` and `frontier-replay` before refreshing or
dispatching that state.

## End-To-End Loop

```text
user theorem / paper proof / new topic
-> upper route population
-> middle source and memory grounding
-> proof-DAG decomposition
-> lower leaf packet
-> choose Lean-direct or NL-prover-assisted route
-> Lean proof attempt
-> reviewer gate
-> memory compression
-> Markdown and LaTeX export after compilation
```

## Role Responsibilities

| Role | Main decisions | Output |
| --- | --- | --- |
| Upper | choose theorem frontier; generate several possible route ideas; decide which proof weapon is only inspiration | route population, selected frontier, rejected route notes |
| Middle | ground route in source cards, Mathlib/LML/local declarations, hidden regularity, and proof-obligation leaves | conversion window, proof-obligation ledger, retrieval index |
| Lower retrieval | find reusable Mathlib/LML/local theorem cards before proof work | retrieval packet with declarations and imports |
| Lower natural-language prover | propose proof sketch for a single leaf when math structure is unclear | sketch, assumptions, possible counterexample, proof route |
| Lower Lean worker | prove exactly one leaf or write a precise blocker | compiled declaration or failed-attempt record |
| Reviewer | reject route drift, hidden assumptions, stale proof weapons, and uncompiled theorem claims | accepted/rejected status, memory update requirements |

## Route Population

Upper may keep a small set of candidate routes under `candidate-populations/`.
Each candidate route should contain:

- target theorem;
- source cards;
- scenario card;
- proof weapon ids considered, marked inspiration-only;
- direct reuse cards: Mathlib, LML, local declarations;
- first proof-DAG leaves;
- hidden regularity contracts;
- expected blocker;
- reason for selection or rejection.

The population is not an evolutionary free-for-all.  Every candidate remains
under the same Lean-checkable target unless reviewer records a mathematical
reason to pivot.

Routine tactic attempts do not use a FunSearch-style island population. A
second lower worker is allowed only for materially distinct route
fingerprints with disjoint file ownership and explicit expected information
gain; otherwise one lower leaf is dispatched.

The canonical route atlas lives in
`research-wiki/theory-tree/lean-route-roadmap.json`.  Agents should inspect it
with:

```bash
python3 tools/bandit.py list-routes
python3 tools/bandit.py route-plan ROUTE-UCB1-FINITE-STOCHASTIC --with-commands
```

Route entries are upper/middle planning objects.  They are not lower-agent
proof packets until middle has selected one exact leaf and written the local
APIs, contracts, and proof route.

## Middle Decomposition Rule

Middle must turn route ideas into leaf packets before lower work.  A valid leaf
packet contains:

| Field | Required content |
| --- | --- |
| Exact statement | Lean-facing theorem shape, not just prose |
| Local APIs | definitions, namespaces, existing declarations |
| Intended route | induction/import/tactic outline |
| Regularity contracts | measurability, integrability, continuity, nonempty, boundedness, positivity, summability, adaptedness |
| Retrieval evidence | `search-memory`, `list-lean-decls --statement`, Mathlib/LML cards |
| Mathlib status | imported, port candidate, Mathlib candidate, project-local, theorem-card-only |
| Failure policy | what repeated failure means and what to audit |

If this packet cannot be written, the task is still upper/middle work and
should not be sent to a lower Lean worker.

## Lean-Direct Versus Natural-Language Prover

Middle chooses the lower route per leaf:

| Leaf situation | Preferred route |
| --- | --- |
| local API and proof route are obvious | Lean-direct lower worker |
| exact theorem exists in Mathlib/LML | lower retrieval worker, then thin wrapper |
| proof shape is mathematical but not yet Lean-shaped | natural-language prover first, then Lean worker |
| repeated Lean failure with same goal | statement/hypothesis/counterexample audit |
| route needs a broad proof weapon | upper/middle decomposes weapon into concrete leaves first |

Natural-language proof is useful only if it sharpens the Lean statement,
assumptions, or proof route.  It is not accepted memory until translated into
compiled Lean or an explicit cited theorem card.

## Memory Card Types

| Card type | Purpose | May be used as proof dependency? |
| --- | --- | --- |
| Local Lean declaration | compiled result in this repository | yes |
| Mathlib retrieval card | import/search route to upstream theorem/API | yes only after imported or wrapped |
| LML theorem card | upstream Lean theorem route | yes only after imported/ported; otherwise theorem-card |
| Textbook card | broad proof source | no |
| Paper card | specific algorithm/source route | no |
| Scenario card | taxonomy and placement | no |
| Proof weapon card | route inspiration for upper planning | no |
| Mathlib candidate card | future upstream lemma proposal | no until compiled/imported |
| Cited result card | external theorem contract | no local proof; can be cited in prose with status |
| Failed-attempt card | mathematical signal and reusable debugging | no |

Lifecycle prompt memory is a separate compact typed stream in
`runs/lifecycle_memory.jsonl`. By default an agent receives at most the last
five active task/role records plus explicitly retrieved verified lemmas. The
complete trial history is never injected by default.

## Lean And LaTeX Synchronization

ABRL exports only after Lean closure:

```bash
python3 tools/bandit.py export-proof TASK_ID --title "Theorem title"
```

The export must:

- name compiled Lean declarations;
- state no stronger result than Lean proves;
- cite theorem cards and proof weapons only by status;
- include regularity assumptions explicitly;
- record any missing theorem-card dependency as not locally proved.

For a paper proof completion task, middle maintains a conversion window:

```text
paper theorem line
-> assumptions and notation
-> Lean definition/declaration
-> proof-DAG leaves
-> compiled theorem
-> Markdown/LaTeX paragraph
```

## Built-In Experience Rules

The harness encodes the following proof-engineering lessons:

- Decompose aggressively.
- Target small lemmas that fit one lower-agent context window.
- Specify more than the theorem: local APIs and intended proof route.
- Treat persistent failure as mathematical signal.
- Promote hidden regularity into reusable theorem contracts.
- Do not frequently change the proof route without a recorded reason.
- Every ordinary worker must deliver one substantive result: a compiled leaf,
  reusable retrieval, statement repair, or precise route-eliminating blocker.
- Parallel workers must own disjoint files; the master plans and synthesizes but
  does not silently repair their proofs or relabel their evidence.
- Measure the master bottleneck through critical-path time and context volume.

Reviewer should reject any cycle that violates these rules even if the text
looks plausible.

Frontier reconstruction must also accept `last_accepted_verifier: null` for a
new leaf that has not passed its first verifier yet. Treat that value as an
empty verifier record; `tools/test_bandit_cli.py` carries the regression test.

## Current Limitation

The plain-file design now has deterministic frontier, memory, DAG, fence,
session, mutation-queue, and retry primitives, but it is not a complete
automatic prover. Detached execution remains disabled without explicit user
direction. The missing mathematical work is the body of Mathlib-backed leaves listed in
`research-wiki/theory-tree/mathlib-foundation-leaf-map.md` and the completion
gap audit in `docs/completion_gap_audit.md`.
