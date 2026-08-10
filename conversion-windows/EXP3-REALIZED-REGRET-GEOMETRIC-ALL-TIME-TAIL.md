# Conversion Window: Generated EXP3 realized-regret geometric all-time tail

Task id: `EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

## Natural-Language Statement

Fix one generated EXP3 trajectory law and one supported comparator. Give half
of a positive total confidence budget to the accepted predictable-regret
all-time theorem and half to the accepted pure realized-deviation all-time
theorem. At every positive prefix, add their two scheduled thresholds. The
outer measure of samples where realized selected-loss regret crosses that sum
at at least one prefix is at most `ENNReal.ofReal delta`.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `P_n` | predictable regret at prefix `n+1` | existing finite sums | compiled parent |
| `D_n` | realized selected loss minus explored predictable loss | `sampledTrajectoryRealizedDeviationAt` sum | compiled parent |
| `R_n` | realized selected loss minus comparator predictable loss | existing finite sums | compiled parent |
| `B_n` | predictable budget plus deviation radius, each using total share `delta/2` | `sampledRealizedRegretGeometricAllTimeBudget` | compiled |
| `E` | `union_n {B_n <= R_n}` | `sampledRealizedRegretGeometricAllTimeFailureSet` | compiled |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| probability prior and generated trajectory law | typed parent contract | both accepted tails | no |
| Standard Borel nonempty Env/Action | typed parent contract | both accepted tails | no |
| measurable action singletons; decidable nonempty arms | typed parent contract | both accepted tails | no |
| one fixed `eta>0` and `0<gamma<1` | typed parent contract | predictable all-time tail | no |
| one predictable `[0,1]` loss process | structure contract | `PredictableLossVector` | no |
| one comparator in `arms` | typed premise | predictable all-time tail | no |
| `delta>0` | typed premise | half-budget positivity | no |
| event measurability or `delta<=1` | deliberately absent | outer-measure route | no |
| new conditional law, independence, stationarity, or integrability | not required | inherited generated-law parents | no |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| decomposition | deviation definition; finite-sum subtraction; ring | local fixed-horizon realized-regret proof | exact pointwise equality | pivot only if the deviation sign is inconsistent |
| event inclusion | both parent membership iff theorems | local accepted all-time parents | two by-cases, strict good bounds, decomposition, `linarith` | pivot only if weak/strict boundary makes the subset false |
| terminal | both parent outer-measure bounds; union/subset monotonicity; `ofReal_add` | Mathlib measure/order cards | add two half-confidence bounds | pivot only if parent measures are on different generated laws |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Regularity | Status |
| --- | --- | --- | --- | --- | --- |
| `DECOMPOSITION` | `R_n = P_n + D_n` | local finite sums | `sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation` | no probability assumptions | compiled |
| `BUDGET-EVENT` | named combined budget/event and exact membership | both scheduled definitions | three declarations | measurable spaces and decidable Action | compiled |
| `INCLUSION` | combined event subset of component union | decomposition and parent memberships | `sampledRealizedRegretGeometricAllTimeFailureSet_subset` | no measure assumptions | compiled |
| `ROOT` | outer measure `<= ofReal delta` | inclusion and both accepted tails | `measure_sampledRealizedRegretGeometricAllTimeFailureSet_le` | full generated-process ledger | compiled |

## Gaps

- [x] No missing definition beyond the planned named budget/event.
- [x] No missing law transport: both parent tails use the identical generated
  trajectory measure.
- [x] No general Mathlib candidate is needed; union/order algebra is already
  available.
- [x] Compile the project-local composition and statement/axiom/canary gates.
- [x] Complete independent review, lifecycle promotion, and full harness.
