# Orabona adaptive-energy sum with zero prefixes

Task id: `ONLINE-CH2-ADAPTIVE-ENERGY-20261010`
Kind: `theorem`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or literature-port target.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Existing Lean declaration:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- target declaration names here
```

Target file: `BanditRLProof/OnlineAdaptiveEnergy.lean`

## Proof Obligations

- [ ] Natural-language statement is mapped to Lean symbols.
- [ ] Required model assumptions are explicit.
- [ ] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [ ] Reusable theorem cards are identified before proof search.
- [ ] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [ ] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [ ] `lake build && lake build Tests` passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | project-local |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task ONLINE-CH2-ADAPTIVE-ENERGY-20261010 --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```

## Current draft contract

Source/terminal/quantifiers, first ready leaf, zero conventions, remaining adaptive-algorithm parent and exact edit scope are in docs/contracts/online-ch2-adaptive-energy-v1/contract-draft-v1.md. Pinned API/type probe actual0 elaborates complete types only; no BODY or compiled theorem yet. All existing35392trackedRAW remain immutable; wholeGoalACTIVE.
