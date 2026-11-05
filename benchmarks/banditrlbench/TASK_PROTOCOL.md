# BanditRLBench task protocol v1

BanditRLBench evaluates knowledge, mathematical reasoning and agentic formal work
in bandits and reinforcement learning. Natural-language and Lean are answer
formats. Ability, format, difficulty and permitted access are separate axes.

## Ability contracts

| Ability | Required mathematical work | Evidence |
| --- | --- | --- |
| Knowledge | State definitions, assumptions, guarantees and limits | Explicit criterion rubric and independent expert judgment |
| Reasoning | Derive, critique, reduce or construct a counterexample | Justified reference, substantive failure cases and semantic review |
| Agentic Lean | Inspect a library, discover dependencies, construct/repair a proof and compile | Fixed statement, kernel result, axiom closure and full tool trajectory |

A one-line application of a supplied lemma is a library-application warmup.
Do not count it as evidence of agentic capability. Existing BRB-001/003 remain
warmups; no agentic suite or model performance has been admitted.

## Package and intake

Use `python tools/bench_task_contract.py scaffold --id BRB-DRAFT-001 --ability agentic-lean --output _out/task-draft`.
The package separates `instruction.md`, `environment/`, `solution/` and `tests/`.
`task.json` freezes ability, format, source, family, graph anchors, access and
budgets, with hashes of the actual instruction/environment/reference/verifier
contract files. `validate` checks structural integrity and provenance bindings;
it never grants admission or establishes the meaning/correctness of a proof.
After intentional changes, recompute the seal with the Python `seal` API and
obtain fresh review. A changed question is an explicit successor, never a silent
repair that moves a proof ingredient into a hypothesis.

Candidates must supply immutable source versions, license/reuse scope, stable
declaration IDs and typed graph relations. Source correspondence and context
are overlays, not formal dependencies. Measured proof edges require compiled
type/value constants and their precise environment. Every family includes all
solution aliases and both format views in a single split.

## Verifier and environment

The agent sees instructions and its workspace. Reference solutions and verifier
internals stay outside that workspace and image layers. Pin Lean, dependency
locks, image digest, installed tools, network/filesystem policy and process-tree
CPU/memory/time limits. Record library commit and all task/prediction hashes.
Natural-language assessment needs an expert rubric; an automatic judge requires
separate calibration. Lean acceptance requires the unchanged target, real kernel
checking and audited axiom closure. Compilation does not certify source fidelity.

Require reference pass and no-op, wrong-answer and placeholder rejection **for
each task**, not only an aggregate failing exit code. Agentic admission additionally
tests statement/import mutation, axiom injection, verifier tampering, output
spoofing, timeout and solution leakage. Include necessary proof prerequisites
in the allowed environment; do not hide requirements from the instruction.

## Independent admission

Draft → candidate → independently reviewed release. Intake accepts only the first
two states. Candidate packets include hashed reference/control results, source
semantic review and family leakage review, with distinct author, blind decoder
and source reviewer identities. Review the seven semantic slots in the repository
protocol. Review reports must actually compare assumptions, normalization,
feedback/probability semantics and remaining boundaries; names and hashes alone
are not mathematical evidence. Maintainers verify those reports and executed
controls before a separately versioned suite manifest may admit the task.

## Trials, training and reporting

Keep knowledge, reasoning and agentic outcomes separate. Also separate closed-book,
text retrieval, graph retrieval and Lean-assisted access. Preserve model/agent
versions, prompts, decoding/seed settings, trajectories, artifacts, resource use
and failure classification. Report repeated trials, per-family denominators and
uncertainty; publish human agreement/calibration before relying on judge scores.
No-op failures do not establish task difficulty; real model trials and error
analysis must show meaningful mathematical work, not formatting puzzles.

All current data are public dev. Training exports require explicit solution
opt-in. Held-out release requires audited family/solution separation and access
enforcement; do not reuse dev scores as unseen-test performance. Maintain an
appeal/correction record and immutable prior versions when a task is repaired.

## Current boundary

Task intake/scaffolding, prompt preparation, expert-review packets and trusted
local fixed-target replay are available. Container isolation, an executed Harbor
adapter, independent gold admission and an agentic evaluation suite are not yet
released. This protocol specifies their admission gates; it does not claim they
have passed. Design references: [Harbor task anatomy](https://docs.harborframework.com/tasks/overview)
and [Terminal-Bench contribution guidance](https://github.com/harbor-framework/terminal-bench/blob/main/CONTRIBUTING.md).
