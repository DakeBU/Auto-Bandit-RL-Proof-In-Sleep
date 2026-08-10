# Conversion Window: Generated EXP3 predictable-regret geometric all-time tail

Task id: `EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

## Natural-Language Statement

Fix one generated EXP3 process and one supported comparator. For prefix `n+1`,
use outer confidence share `delta/2/2^n`; inside the existing predictable-
regret budget, give half of that share to each of the pure-cross and comparator
events. The outer measure of samples where the resulting predictable-regret
budget is crossed at at least one positive prefix is at most
`ENNReal.ofReal delta`.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `delta_n` | outer confidence share `delta/2/2^n` | `Concentration.geometricConfidenceShare delta n` | compiled parent |
| `B_n` | fixed-horizon predictable-regret budget at horizon `n+1` and inner share `delta_n/2` | `sampledPredictableRegretGeometricAllTimeBudget arms eta gamma delta n` | compiled |
| `R_n` | exploration-mixed predictable loss minus comparator predictable loss on `range (n+1)` | existing finite sums | compiled parent |
| `E` | `union_n {B_n <= R_n}` | `sampledPredictableRegretGeometricAllTimeFailureSet` | compiled |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| one fixed prior, arms, eta, gamma, loss process, and comparator | statement scope | one-process requirement | no |
| comparator belongs to arms | explicit | fixed-horizon parent | no |
| probability prior and Standard Borel nonempty Env/Action | explicit terminal contract | generated trajectory parent | no |
| measurable action singletons and decidable nonempty arms | explicit | generated trajectory parent | no |
| `eta>0` and `0<gamma<1` | explicit | Hedge/exploration parent | no |
| positive outer `delta` | explicit | geometric schedule | no |
| event measurability, independence, stationarity, `delta<=1` | deliberately absent | outer-measure route | no |

## Proof DAG

| Node | Interface | Dependencies | Owner | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| N0 | exact scheduled predictable-regret budget | fixed parent budget; geometric share | lower | focused/Tests | compiled |
| N1 | named countable event and membership iff | N0; `Set.mem_iUnion` | lower | focused/Tests | compiled |
| root | all-positive-prefix outer measure `<=ofReal delta` | fixed-horizon total tail; `measure_iUnion_le`; exact geometric tsum | upper | full harness | accepted |

## Remaining Boundaries

- This theorem is predictable pseudo-regret, not realized selected-loss regret.
- Fixed `eta,gamma` can leave linear horizon terms; no tuned sublinear all-time
  algorithm is concluded.
- The next theorem should combine this event with the accepted pure realized-
  deviation all-time event on the same generated process.
- No Ville/Doob, mixture, optional stopping, self-normalization, general
  Freedman, horizon-varying tuning, or ideal EXP3.P conclusion is implied.
