# Generated EXP3 realized-deviation geometric all-time tail

Task id: `EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

On one generated EXP3 trajectory law with fixed `eta`, `gamma`, and predictable
loss process, bound the countable union over every positive prefix `n+1` where
realized selected loss minus predictable selected loss crosses the geometric-
share quadratic radius with deterministic variance budget `n+1`. Eliminate
the variance-good conjunct by proving the exact selected-loss conditional
variance is at most one at every generated time.

## Source

- Paper-guided order: strengthen the compiled concentration layer into a
  canonical adversarial-bandit consumer before broader regret assembly.
- Paper card: `PPR-AUER-CFS-2002-EXP3` (algorithm placement only).
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (concentration spine).
- Scenario card: `SCN-ADVERSARIAL-FINITE`.
- Local parents:
  `selectedLossCenteredSecondMoment`,
  `sampledTrajectoryPredictableRealizedVarianceAt`, and
  `measure_sampledPredictableRealizedDeviationAllTimeFailureSet_le`.
- `WEAPON-TAIL-INEQUALITIES` is inspiration only.

## Lean Target

```lean
Exp3.selectedLossCenteredSecondMoment_le_one
Exp3.sampledTrajectoryPredictableRealizedVarianceAt_le_one
Exp3.sampledPredictableRealizedVariance_sum_le_horizon
Exp3.sampledRealizedPredictableVarianceLinearBudget
Exp3.sampledRealizedPredictableVarianceLinearBudget_pos
Exp3.sampledRealizedDeviationGeometricAllTimeRadius
Exp3.sampledRealizedDeviationGeometricAllTimeFailureSet
Exp3.mem_sampledRealizedDeviationGeometricAllTimeFailureSet_iff
Exp3.sampledPredictableRealizedDeviationAllTimeFailureSet_linearBudget_eq
Exp3.measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le
```

Supporting file: `BanditRLProof/Exp3RealizedPredictableVariance.lean`

Target file: `BanditRLProof/Exp3RealizedDeviationAllTime.lean`

## Proof Obligations

- [x] Natural-language statement is mapped to Lean symbols.
- [x] The single-process and positive-prefix semantics are explicit.
- [x] Local and Mathlib retrieval evidence is recorded before tactic work.
- [x] Regularity and source-card authority are explicit.
- [x] Supporting variance-bound, event-transport, and terminal nodes are fixed.
- [x] Focused/root/Tests, statement, and axiom gates pass.
- [x] Independent review, lifecycle, and full harness gates pass.

## Local APIs, Route, And Contracts

| Node | APIs/imports | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- |
| centered variance `<=1` | `FiniteActionDistribution.nonneg/sum_eq_one`; finite sums; `[0,1]` loss bounds | prove the weighted mean is in `[0,1]`; each centered loss is in `[-1,1]`; sum `p(a)*(loss(a)-mean)^2 <= sum p(a)=1` | finite action distribution; supported losses in `[0,1]`; no measurability | compiled |
| generated pointwise/cumulative budget | generated probability source; predictable loss bounds; `Finset.sum_le_sum` | instantiate the generic bound at each time, then sum ones over `range horizon` | measurable Env; measurable-singleton Action; decidable nonempty arms; `0<=gamma<=1`; predictable loss vector | compiled |
| named pure failure event | prior geometric all-time radius and finite-prefix deviation | choose budget `n+1`; define the pure countable union and membership iff | definitions only | compiled |
| event equality and terminal | cumulative budget theorem; compiled joint all-time tail | prove both membership directions; the reverse adds the deterministic variance inequality; rewrite the prior measure theorem | full generated EXP3 probability/Standard-Borel contracts; fixed process; `0<gamma<=1`; `delta>0` | compiled |

## Retrieval Evidence

- Local:
  `LOCAL-LEAF-EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL`,
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`,
  `LOCAL-LEAF-CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`, and
  the generated exact selected-loss predictable-variance declarations.
- Mathlib: `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-PROBABILITY-VARIANCE`, `MLIB-PROBABILITY-MGF`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-AUER-CFS-2002-EXP3`, `SCN-ADVERSARIAL-FINITE`.

## Failure Policy

If compilation fails, classify the first blocker as finite-law variance
algebra, generated-law instantiation, cumulative cast/sum normalization,
named-event equality, or terminal elaboration. Preserve one fixed process,
all prefixes `n+1`, exact geometric shares, and deterministic budget `n+1`.
Do not weaken to a finite horizon, reintroduce a caller-supplied variance-good
event, vary process parameters with `n`, or claim a Ville/Doob maximal theorem,
mixture boundary, optional stopping, self-normalization, general Freedman,
full EXP3 regret, horizon-free tuned algorithm, or ideal EXP3.P theorem.

## Verification

- Focused module and `Tests.Basic` compile; the project root imports the target.
- Six external canaries cover the generic variance bound, generated pointwise
  and cumulative budgets, pure-event membership, event equality, and terminal.
- SafeVerify statement hash is
  `5479f3349aeab1d757ac8a80547ab40fbe1adde83e05eadb33b9773eb0dce870`.
- The ten new declarations report only `propext`, `Classical.choice`, and
  `Quot.sound` in the axiom audit.
- Independent review found no P0/P1; its direct-canary, API-contract, and
  outer-measure wording findings are closed.
- Lifecycle build/review records are accepted; verified memory is
  `mem-7ceab55257453017`; frontier shadow reports zero mismatches; and
  `python3 tools/bandit.py check` passes with 36 tests and one expected skip.
