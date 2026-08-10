# Generated EXP3 realized-regret geometric all-time tail

Task id: `EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

Fix one generated EXP3 process and one supported comparator. Split the total
confidence budget equally between the accepted predictable-regret and pure
realized-deviation all-time event families. Prove that, outside an outer-
measure set of mass at most `ENNReal.ofReal delta`, every positive prefix
`n+1` has realized selected-loss regret below the sum of their scheduled
budgets.

## Source

- Paper-guided order: the paper places EXP3 after importance-weighted moments
  and potential/stability/comparator analysis; this target closes their
  realized selected-loss composition before any sharper tuning route.
- Paper card: `PPR-AUER-CFS-2002-EXP3` (placement only).
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (route placement).
- Scenario card: `SCN-ADVERSARIAL-FINITE`.
- Local parents:
  `measure_sampledPredictableRegretGeometricAllTimeFailureSet_le` and
  `measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le`.
- `WEAPON-EXP3-POTENTIAL` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.

## Lean Target

```lean
Exp3.sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation
Exp3.sampledRealizedRegretGeometricAllTimeBudget
Exp3.sampledRealizedRegretGeometricAllTimeFailureSet
Exp3.mem_sampledRealizedRegretGeometricAllTimeFailureSet_iff
Exp3.sampledRealizedRegretGeometricAllTimeFailureSet_subset
Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le
```

Target file: `BanditRLProof/Exp3RealizedRegretAllTime.lean`

## Proof Obligations

- [x] One-process, one-comparator, and positive-prefix semantics fixed.
- [x] The outer confidence budget is split as `delta/2` between the two
  accepted all-time event families.
- [x] Local, Mathlib, source, scenario, and weapon evidence recorded.
- [x] Regularity and failure boundaries recorded before tactic work.
- [x] Finite-prefix decomposition, budget, event, membership, inclusion, and
  terminal theorem compile.
- [x] Root/Tests, statement, and axiom gates pass.
- [x] Independent review, lifecycle, and full harness gates pass.

## Local APIs, Route, And Contracts

| Node | APIs/imports | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- |
| finite-prefix decomposition | `sampledTrajectoryRealizedDeviationAt`; `Finset.sum_sub_distrib`; ring normalization | expose realized loss as explored predictable loss plus deviation and cancel the comparator sum | measurable Env/Action and decidable Action only | compiled |
| scheduled budget/event | accepted predictable all-time budget and realized-deviation radius | evaluate both at total share `delta/2`; use `Finset.range (n+1)` | definitions only beyond local measurable-space instances | compiled |
| event inclusion | both exact membership theorems; finite-prefix decomposition | if neither component crosses, strict component bounds add to contradict the combined weak crossing | no measure assumptions | compiled |
| terminal outer-measure theorem | both accepted measure bounds; `measure_mono`; `measure_union_le`; `ENNReal.ofReal_add` | bound the combined event by the union, assign each family `delta/2`, and normalize the two half budgets | probability prior; Standard Borel nonempty Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`; predictable unit losses; supported comparator; `delta>0` | compiled |

## Retrieval Evidence

- Local: `LOCAL-LEAF-EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`,
  `LOCAL-LEAF-EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`, and the
  fixed-horizon `sampledPredictable_realizedHighProbabilityRegret_tail_delta`
  decomposition precedent.
- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
  `MLIB-ORDER-ALGEBRA`, `MeasureTheory.measure_union_le`, and
  `ENNReal.ofReal_add`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-AUER-CFS-2002-EXP3`, `SCN-ADVERSARIAL-FINITE`.
- Search before implementation found no matching local declaration or typed
  memory record for this exact geometric same-process realized-regret event.

## Failure Policy

If compilation fails, classify the first blocker as decomposition
normalization, event-membership inclusion, confidence-half normalization,
parent-law mismatch, or false statement. Preserve one fixed process and
comparator, every `Finset.range (n+1)`, and the exact two-family `delta/2`
split. Do not weaken to one horizon or claim tuned sublinear all-time regret,
horizon-varying `eta`/`gamma`, best-arm minimization, Ville/Doob, mixture,
optional stopping, self-normalization, general Freedman, horizon-free tuned
EXP3, or ideal EXP3.P.

## Verification

- Focused module, project root, and `Tests.Basic` compile.
- Five external canaries cover the finite-prefix decomposition, exact
  `delta/2` budget, `n+1` membership, event inclusion, and terminal statement.
- SafeVerify statement hash is
  `34d6b6dd7518f9b531186f8db39ab7f52a67b685605a43cc8c5871d3fa295702`.
- All six declarations report only `propext`, `Classical.choice`, and
  `Quot.sound` in the axiom audit.
- Independent review found no P0/P1/P2/P3.
- Lifecycle records are accepted; verified memory is
  `mem-2a0ffec376992850`; frontier shadow has zero mismatches; and the full
  harness passes with 36 tests and one expected skip.
