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
- [ ] Build gate passes.

## Build Gate

```bash
lake build && lake build Tests
```
