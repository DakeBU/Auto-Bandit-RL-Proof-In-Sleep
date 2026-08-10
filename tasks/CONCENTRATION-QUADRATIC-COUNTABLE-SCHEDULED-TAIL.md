# Countable scheduled quadratic fixed-MGF tail

Task id: `CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

Lift the compiled one-event quadratic fixed-MGF delta theorem to a countable
family with time-varying variance scales, variance budgets, tilt caps, and
positive confidence shares. Bound the countable union by the `ENNReal` sum of
the scheduled shares, and expose an outer-budget corollary.

## Source

- Paper-guided project choice: the paper prioritizes recurring probability and
  stopping-time contracts before broader algorithm compositions. This leaf
  instantiates that general dependency order with countable confidence
  summability; the paper does not name this theorem.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (concentration spine).
- Paper card: `PPR-AUER-CFS-2002-EXP3` (downstream placement only).
- Scenario card: `SCN-ADVERSARIAL-FINITE`.
- Existing local parent:
  `Concentration.measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`.
- `WEAPON-TAIL-INEQUALITIES` is inspiration only.

## Lean Target

```lean
Concentration.quadraticFixedMGFScheduledRadius
Concentration.measure_iUnion_scheduled_deviation_ge_inter_variance_le_tsum_of_fixedTilt_quadratic_tail
Concentration.measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
```

Target file: `BanditRLProof/ConcentrationQuadraticScheduled.lean`

## Proof Obligations

- [x] Natural-language statement is mapped to Lean symbols.
- [x] Required positivity assumptions are explicit and time-indexed.
- [x] The outer-measure/countable-union contract is recorded.
- [x] Local and Mathlib retrieval evidence is recorded before tactic work.
- [x] The proof route is fixed to pointwise optimization plus `measure_iUnion_le`.
- [x] The leaf is classified as a Mathlib-candidate project-local wrapper.
- [x] Focused source and external `Tests.Basic` canary compile.
- [x] Placeholder, statement-fence, axiom, lifecycle, index, root, and full harness gates pass.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| scheduled radius | `quadraticFixedMGFRadius` | evaluate the parent radius at the four time-indexed parameter families | no assumptions in the definition | project-local |
| tsum tail | parent quadratic delta theorem; `MeasureTheory.measure_iUnion_le`; `ENNReal.tsum_le_tsum` | prove every indexed event at `deltaAt n`, take the countable outer-measure union, compare termwise | measurable ambient space; every scale/budget/cap/share strictly positive; fixed-tilt tail family at every index | mathlib-candidate wrapper |
| outer-budget tail | tsum tail | transitivity through a caller-supplied `tsum <= ofReal delta` budget | no positivity or probability assumption on the outer budget beyond the displayed ENNReal inequality | project-local corollary |

## Retrieval Cards

- Local: `LOCAL-LEAF-CONCENTRATION-PREDICTABLE-COMPENSATED-QUADRATIC-DELTA-TAIL`,
  `LOCAL-LEAF-CONCENTRATION-QUADRATIC-FINITE-MAXIMAL-TAIL`.
- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-MGF`,
  `MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
  `MLIB-ORDER-ALGEBRA`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-AUER-CFS-2002-EXP3`, `SCN-ADVERSARIAL-FINITE`.

## Failure Policy

If compilation fails, first classify it as event elaboration, pointwise parent
specialization, `iUnion` syntax, or ENNReal `tsum` monotonicity. Preserve the
time-varying schedules and the caller-supplied outer budget. Do not replace the
countable union by a finite horizon, add event measurability or a probability
measure, impose `deltaAt n <= 1`, or claim a Ville/Doob maximal inequality,
mixture boundary, optional stopping, self-normalization, general Freedman, or
ideal EXP3.P theorem.

## Verification

- Focused module, project root, and `Tests.Basic` builds pass.
- The external canary instantiates the full outer-budget theorem with distinct
  `deltaAt`, `delta`, and `hbudget` arguments.
- SafeVerify statement hash:
  `0e782bcda45091c55081430d14c97cadf7d6446aae9869ca280cd0043ab3a1df`.
- Placeholder scan is empty; all three declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent review found no Lean defect; its lifecycle, paper-attribution,
  measure-terminology, and retrieval-ledger findings are closed.
- Verified memory: `mem-26c1f8ea632bb05f`; authoritative frontier shadow has
  zero drift; the full repository gate passes with 36 CLI tests and one
  expected skip.
