# Generated EXP3 predictable-variance geometric all-time tail

Task id: `EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

On one generated EXP3 trajectory law with fixed `eta`, `gamma`, and predictable
loss process, control the countable union over every positive prefix `n+1` of
the event that realized-minus-predictable selected loss crosses its optimized
quadratic radius while cumulative predictable variance stays below a positive
time-varying budget. Use the explicit confidence schedule
`delta / 2 / 2^n`, whose ENNReal mass sums exactly to `ofReal delta`.

## Source

- Paper-guided project choice: instantiate the paper's shared-concentration
  before algorithm-wrapper order with one concrete adversarial consumer; the
  paper does not state this exact theorem.
- Paper card: `PPR-AUER-CFS-2002-EXP3` (algorithm placement only).
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (concentration spine).
- Scenario card: `SCN-ADVERSARIAL-FINITE`.
- Existing local parents:
  `Concentration.measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`
  and
  `Exp3.sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt`.
- `WEAPON-TAIL-INEQUALITIES` is inspiration only.

## Lean Target

```lean
Concentration.geometricConfidenceShare
Concentration.geometricConfidenceShare_pos
Concentration.tsum_ofReal_geometricConfidenceShare
Exp3.sampledRealizedPredictableVarianceGeometricRadius
Exp3.sampledPredictableRealizedDeviationAllTimeFailureSet
Exp3.mem_sampledPredictableRealizedDeviationAllTimeFailureSet_iff
Exp3.measure_sampledPredictableRealizedDeviationAllTimeFailureSet_le
```

Supporting file: `BanditRLProof/ConcentrationConfidenceSchedule.lean`

Target file: `BanditRLProof/Exp3RealizedPredictableVarianceAllTime.lean`

## Proof Obligations

- [x] Natural-language statement is mapped to Lean symbols.
- [x] The single-process and positive-prefix semantics are explicit.
- [x] Model and regularity assumptions are explicit.
- [x] Local and Mathlib retrieval evidence is recorded before tactic work.
- [x] Supporting schedule, named-event, and pointwise-tail leaves are fixed.
- [x] General schedule lemmas are classified as project-local Mathlib candidates.
- [x] Focused/root/Tests, statement, axiom, review, lifecycle, and full gates pass.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| geometric share | `Mathlib.Analysis.SpecificLimits.Basic`; `hasSum_geometric_two'`; ENNReal coe/ofReal APIs | scale the real geometric series by `delta`, transport nonnegative terms through `toNNReal` and ENNReal coercion | `0 <= delta` only for the ENNReal sum theorem | Mathlib-candidate wrapper |
| named all-time event | finite-prefix deviation/variance sums; existing sampled radius | define the countable union and normalize membership with `Set.mem_iUnion` | no measure assumptions | project-local |
| pointwise fixed-tilt family | generated fixed-tilt predictable-variance theorem | specialize horizon to `n+1`, variance budget to `varianceBudget n`, cap to one, and threshold to the scheduled quadratic radius | generated EXP3 probability law; positive gamma; `gamma <= 1`; predictable measurable unit losses inherited by `PredictableLossVector` | project-local parent reuse |
| root all-time tail | scheduled quadratic countable theorem; geometric ENNReal sum | instantiate constant scale/cap, time-varying budget/share, discharge pointwise tails, rewrite exact sum | Standard Borel/nonempty Env and Action; measurable action singletons; decidable Action; probability prior; nonempty arms; fixed eta/gamma/loss; positive budget schedule and outer delta | project-local algorithm consumer |

## Retrieval Cards

- Local:
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`,
  `LOCAL-LEAF-CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`,
  `LOCAL-LEAF-CONCENTRATION-PREDICTABLE-COMPENSATED-FIXED-TILT-TAIL`,
  `LOCAL-LEAF-CONCENTRATION-PREDICTABLE-COMPENSATED-QUADRATIC-DELTA-TAIL`,
  `LOCAL-LEAF-OFUL-ALL-TIME-TELESCOPING-SCALAR-RIDGE-CONFIDENCE`
  (exact-budget transport precedent only).
- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-MGF`,
  `MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
  `MLIB-ORDER-ALGEBRA`, `Mathlib.Analysis.SpecificLimits.Basic`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-AUER-CFS-2002-EXP3`, `SCN-ADVERSARIAL-FINITE`.

## Failure Policy

If compilation fails, classify the first blocker as geometric-series ENNReal
transport, event/radius normalization, pointwise fixed-tilt specialization,
or countable-consumer elaboration. Preserve one common generated law, all
positive prefixes, time-varying variance budgets, and exact total confidence
budget. Do not replace the countable union by a finite horizon, change the
process parameters with `n`, assume event measurability or independence, or
claim a variance-budget law, full regret theorem, Ville/Doob maximal theorem,
mixture boundary, optional stopping, self-normalization, general Freedman,
horizon-free tuned EXP3 algorithm, or ideal EXP3.P theorem.

## Verification

- Focused modules, root import, and `Tests.Basic` compile.
- External canaries cover the exact geometric `tsum`, full `n+1` membership
  semantics, and terminal measure theorem.
- SafeVerify statement fence:
  `be643bca7d9a7f9ddf16cb98c5fcab0d74ee624eaeed4cfe4a4af530b84073b2`.
- All seven public declarations use only baseline axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
- Independent read-only review found no Lean or mathematical defect; its
  schedule-ownership, semantic-canary, OFUL-retrieval, and stale-status
  findings are incorporated.
- Verified memory is `mem-1d262929553ef1ca`; authoritative frontier shadow
  reports 307 trial rows and zero mismatches.
- The exact next blocker is a same-process predictable-variance budget
  producer, followed by pathwise potential/comparator regret assembly.
