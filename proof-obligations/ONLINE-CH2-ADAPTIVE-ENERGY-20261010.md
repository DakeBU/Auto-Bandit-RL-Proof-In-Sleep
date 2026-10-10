# Proof Obligations: Orabona adaptive-energy sum with zero prefixes

Task id: `ONLINE-CH2-ADAPTIVE-ENERGY-20261010`

Source card:
Scenario card:

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ONLINE-CH2-ADAPTIVE-ENERGY-20261010-ROOT` | root theorem or definition | conversion window | TBD | TBD | TBD | TBD | project-local | upper | TBD | `lake build && lake build Tests` | planned |

## Failure Classification

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- missing regularity contract;
- likely false statement or counterexample;
- invalid route;
- stale dynamic leaf;
- connected blocker.

## Reviewer Notes

- Keep failed attempts in `proof-attempts/ONLINE-CH2-ADAPTIVE-ENERGY-20261010/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.

## Current draft contract

Source/terminal/quantifiers, first ready leaf, zero conventions, remaining adaptive-algorithm parent and exact edit scope are in docs/contracts/online-ch2-adaptive-energy-v1/contract-draft-v1.md. Pinned API/type probe actual0 elaborates complete types only; no BODY or compiled theorem yet. All existing35392trackedRAW remain immutable; wholeGoalACTIVE.
