# Memory Protocol

ABRL memory exists to prevent agents from rediscovering the same proof route,
forgetting failed assumptions, or overstating theorem-card status.

## Memory Classes

| Class | Directory | Rule |
| --- | --- | --- |
| theorem card | `research-wiki/lml/` | upstream result, not local proof |
| Mathlib retrieval card | `research-wiki/mathlib/` | import/search route for reusable Lean leaves |
| textbook card | `research-wiki/textbooks/` | source route for classical proof reproduction |
| paper card | `research-wiki/papers/` | algorithm or frontier-scenario source route |
| scenario card | `research-wiki/scenarios/` | bandit/RL setting taxonomy and frontier placement |
| proof weapon | `research-wiki/proof-weapons/` | upper-layer route inspiration, never a proof certificate |
| theory tree | `research-wiki/theory-tree/` | source-to-leaf proof architecture |
| completion audit | `docs/completion_gap_audit.md` | current compiled-versus-carded proof coverage |
| adaptive harness design | `docs/adaptive_harness_design.md` | route population, worker split, and memory rules |
| cited result | `research-wiki/cited-results/` | exact source and statement used |
| proof technique | `research-wiki/proof-techniques/` | reusable route or Lean pattern |
| open problem | `research-wiki/open-problems/` | unresolved proof technology |
| task-local ledger | `proof-obligations/` | active proof-DAG leaves |
| failed attempt | `proof-attempts/` | useful fragments and error class |
| retrieval index | `research-wiki/retrieval-index/` | compact JSON for prompt decks |
| Mathlib candidate | `research-wiki/mathlib-candidates/` | reusable leaf lemma proposed for upstreaming |

## Status Vocabulary

- `insight`: idea, theorem card, or prose sketch.
- `typedContract`: Lean-facing interface exists, theorem not proved.
- `proofObligation`: needed for closure, not yet proved.
- `leanCompiled`: local Lean declaration builds.
- `rejected`: route changed target, used invalid assumption, or failed review.
- `mathlibCandidate`: general leaf lemma should be prepared for upstream
  Mathlib contribution.

## Required Refreshes

Before long proof work:

```bash
python3 tools/bandit.py blueprint-refresh TASK_ID
python3 tools/bandit.py memory-refresh TASK_ID
python3 tools/bandit.py reference-index
python3 tools/bandit.py search-memory QUERY
python3 tools/bandit.py list-papers
python3 tools/bandit.py list-weapons
python3 tools/bandit.py list-lean-decls QUERY
python3 tools/bandit.py list-lean-decls QUERY --statement
```

After any failed proof attempt, write a concise file under
`proof-attempts/<task-id>/` with:

- target theorem;
- exact statement attempted;
- Lean error or remaining goal;
- useful lemmas discovered;
- failure class;
- whether repeated failure suggests false statement, missing assumption,
  counterexample, wrong abstraction, or API mismatch;
- next active leaf or reason to reject.

Do not leave reusable proof memory only in an agent transcript.

Hidden regularity hypotheses must be promoted to reusable contracts rather
than rediscovered in each proof.  Store integrability, measurability,
continuity, nonemptiness, boundedness, positivity, and summability facts as
named obligations or Mathlib candidates.

For `mathlibCandidate` entries, include the local APIs/imports, intended proof
route, current proof stability note, and whether repeated failure suggests a
missing assumption or counterexample.  Do not leave a candidate as only a
natural-language wish list.

For new theorem targets, include a textbook or paper source card and a scenario
card.
If a proof weapon suggests the route, record the weapon id only as planning
context and then decompose it into concrete source cards, Mathlib/LML cards,
local APIs, and proof obligations.
Every new route should also check the completion audit and the foundation leaf
map.  If the needed layer is marked as carded or missing, lower agents must
receive a one-leaf packet instead of a broad textbook theorem.
For each general leaf, include the Mathlib retrieval card searched before the
leaf was classified as imported, ported, project-local, or upstream candidate.
For each local leaf, include the compiled Lean declaration found by
`list-lean-decls` or explain why no local declaration exists.
