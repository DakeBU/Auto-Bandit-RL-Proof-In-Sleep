# TASK_TITLE

Task id: `TASK_ID`
Kind: `literaturePort | theoremFormalization | proofRepair | openProblemProposal | naturalLanguageExport`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or proof route to formalize.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Upstream Lean declaration:
- Current local Lean file:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- declaration names here
```

## Assumptions

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task | no |

## Proof Obligations

- [ ] Natural-language theorem is mapped to Lean symbols.
- [ ] Algorithm definition is explicit.
- [ ] Regret notion is explicit.
- [ ] Concentration or posterior theorem is recorded.
- [ ] Each active leaf names local APIs/imports and the intended proof route.
- [ ] Hidden regularity conditions are reusable contracts, not local clutter.
- [ ] General-purpose leaves are marked as Mathlib candidates.
- [ ] Persistent failure has triggered statement/hypothesis/counterexample review.
- [ ] Build gate passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | `mathlib-candidate`, `project-local`, or `theorem-card-only` |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Build Gate

```bash
lake build && lake build Tests
```
