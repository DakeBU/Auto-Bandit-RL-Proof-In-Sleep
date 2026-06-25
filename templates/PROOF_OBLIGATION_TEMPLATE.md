# Proof Obligations: TASK_ID

| Node | Target | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `TASK_ID-ROOT` | root theorem | conversion window | upper | TBD | `lake build && lake build Tests` | planned |

## Failure Classification

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- invalid route;
- stale dynamic leaf;
- connected blocker.

## Reviewer Notes

- Do not promote theorem cards to local proofs.
- Do not weaken the theorem to close a proof.
- Store useful failed attempts under `proof-attempts/TASK_ID/`.
