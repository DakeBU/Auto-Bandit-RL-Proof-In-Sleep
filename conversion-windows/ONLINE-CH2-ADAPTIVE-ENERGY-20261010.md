# Conversion Window: Orabona adaptive-energy sum with zero prefixes

Task id: `ONLINE-CH2-ADAPTIVE-ENERGY-20261010`

Source card:
Scenario card:

## Natural-Language Statement

Write the theorem, proof fragment, or paper equation in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task packet | no |
| sub-Gaussian rewards | obligation | cited result | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | theorem-card route plus local wrappers | pivot only after reviewer records a mathematical reason |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | this file | TBD | TBD | project-local | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing lemma:
- [ ] Missing regularity contract:
- [ ] Mathlib candidate to upstream:
- [ ] Missing cited-result entry:

## Current draft contract

Source/terminal/quantifiers, first ready leaf, zero conventions, remaining adaptive-algorithm parent and exact edit scope are in docs/contracts/online-ch2-adaptive-energy-v1/contract-draft-v1.md. Pinned API/type probe actual0 elaborates complete types only; no BODY or compiled theorem yet. All existing35392trackedRAW remain immutable; wholeGoalACTIVE.

## Operative deterministic conversion record

All stock action, sub-Gaussian and other bandit template tables above are INACTIVE SCAFFOLD, not hypotheses or obligations of this contract. Actual model: finite nonnegative real increments, inclusive cumulative prefixes, T>=0 and arbitrary normed additive groups; source-scaled endpoint uses D>=0. Source printed40 energy display maps source index1..T to Lean0..T-1; denominator includes current increment and 0/0=0 only at zero numerator. Exact headers/context/fingerprints and source/neutral mapping are in docs/contracts/online-ch2-adaptive-energy-v1; no algorithm conclusion. Source reviewer contract accepted; proof/gates not yet closed.
