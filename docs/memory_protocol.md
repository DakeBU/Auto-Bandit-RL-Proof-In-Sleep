# Memory Protocol

ABRL memory exists to prevent agents from rediscovering the same proof route,
forgetting failed assumptions, or overstating theorem-card status.

## Memory Classes

| Class | Directory | Rule |
| --- | --- | --- |
| theorem card | `research-wiki/lml/` | upstream result, not local proof |
| cited result | `research-wiki/cited-results/` | exact source and statement used |
| proof technique | `research-wiki/proof-techniques/` | reusable route or Lean pattern |
| open problem | `research-wiki/open-problems/` | unresolved proof technology |
| task-local ledger | `proof-obligations/` | active proof-DAG leaves |
| failed attempt | `proof-attempts/` | useful fragments and error class |
| retrieval index | `research-wiki/retrieval-index/` | compact JSON for prompt decks |

## Status Vocabulary

- `insight`: idea, theorem card, or prose sketch.
- `typedContract`: Lean-facing interface exists, theorem not proved.
- `proofObligation`: needed for closure, not yet proved.
- `leanCompiled`: local Lean declaration builds.
- `rejected`: route changed target, used invalid assumption, or failed review.

## Required Refreshes

Before long proof work:

```bash
python3 tools/bandit.py blueprint-refresh TASK_ID
python3 tools/bandit.py memory-refresh TASK_ID
```

After any failed proof attempt, write a concise file under
`proof-attempts/<task-id>/` with:

- target theorem;
- exact statement attempted;
- Lean error or remaining goal;
- useful lemmas discovered;
- failure class;
- next active leaf or reason to reject.

Do not leave reusable proof memory only in an agent transcript.
