# Conversion Window: TITLE

Task id: `TASK_ID`

## Natural-Language Statement

Write the theorem or proof fragment in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite arms | typed | task | no |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing theorem card:
- [ ] Missing concentration lemma:
- [ ] Missing proof export:
