# Generated EXP3 predictable-regret geometric all-time tail

Task id: `EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

On one generated EXP3 trajectory law with fixed `prior`, arms, `eta`, `gamma`,
predictable loss process, and supported comparator, control every positive
prefix `n+1` simultaneously. At prefix `n+1`, allocate geometric outer share
`delta/2/2^n`; the compiled fixed-horizon predictable-regret theorem splits
that share equally between its pure-cross and comparator-estimator events.

## Source

- Paper-guided order: after importance-weighted moments, assemble the EXP3
  potential, exploration, and comparator terms before realized-regret closure.
- Paper card: `PPR-AUER-CFS-2002-EXP3` (placement only).
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (route placement).
- Scenario card: `SCN-ADVERSARIAL-FINITE`.
- Local parents:
  `sampledPredictable_highProbabilityRegret_tail_total_delta`,
  `Concentration.geometricConfidenceShare_pos`, and
  `Concentration.tsum_ofReal_geometricConfidenceShare`.
- `WEAPON-EXP3-POTENTIAL` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.

## Lean Target

```lean
Exp3.sampledPredictableRegretGeometricAllTimeBudget
Exp3.sampledPredictableRegretGeometricAllTimeFailureSet
Exp3.mem_sampledPredictableRegretGeometricAllTimeFailureSet_iff
Exp3.measure_sampledPredictableRegretGeometricAllTimeFailureSet_le
```

Target file: `BanditRLProof/Exp3PredictableRegretAllTime.lean`

## Proof Obligations

- [x] One-process, supported-comparator, and positive-prefix semantics fixed.
- [x] The outer geometric share and inner two-event split are explicit.
- [x] Local, Mathlib, source, scenario, and weapon evidence recorded.
- [x] Regularity and failure boundaries recorded before tactic work.
- [x] Named budget/event/membership and terminal theorem compile.
- [x] Root/Tests, statement, axiom, review, lifecycle, and full gates pass.

## Local APIs, Route, And Contracts

| Node | APIs/imports | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- |
| scheduled budget | fixed-horizon predictable regret budget; geometric share | evaluate the parent budget at horizon `n+1` and confidence `share delta n / 2` | definitions only | compiled |
| named all-time event | `Finset.range (n+1)` predictable regret against one comparator | countable union; expose exact existential membership | measurable Env/Action and decidable Action only | compiled |
| pointwise scheduled tail | fixed-horizon total-delta theorem | specialize horizon to `n+1`, prove positivity, retain all fixed process parameters | probability prior; Standard Borel nonempty Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`; predictable unit losses; supported comparator; positive share | compiled parent |
| countable terminal | `MeasureTheory.measure_iUnion_le`; `ENNReal.tsum_le_tsum`; exact geometric tsum | bound every event by its share, compare tsums, rewrite exact outer budget | same generated-process ledger; `delta>0`; no event measurability | compiled |

## Retrieval Evidence

- Local: `LOCAL-LEAF-EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET`,
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`,
  `LOCAL-LEAF-EXP3-PREDICTABLE-HEDGE-AE`,
  `LOCAL-LEAF-EXP3-EXPLORATION-BIAS`, pure-cross and comparator-confidence
  leaves.
- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
  `MLIB-ORDER-ALGEBRA`, `MeasureTheory.measure_iUnion_le`,
  `ENNReal.tsum_le_tsum`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-AUER-CFS-2002-EXP3`, `SCN-ADVERSARIAL-FINITE`.
- Before implementation, no matching all-time predictable-regret local
  declaration or memory hit was found. The four declarations listed under
  `Lean Target` are now compiled local output evidence; the stale broad route
  plan remains non-proof metadata.

## Failure Policy

If compilation fails, classify the first blocker as parent-budget
normalization, positive-prefix specialization, countable-union elaboration,
ENNReal tsum comparison, or false statement. Preserve one fixed process and
comparator, every `Finset.range (n+1)`, exact outer shares, and the parent's
inner two-event split. Do not weaken to a finite horizon, vary `eta` or `gamma`
with `n`, or claim realized selected-loss regret, a tuned sublinear all-time
rate, Ville/Doob, mixture, optional stopping, self-normalization, general
Freedman, horizon-free tuned EXP3, or ideal EXP3.P.

## Verification

- Focused module, project root, and `Tests.Basic` compile.
- Three external canaries fix the inner `/2` budget normalization, exact
  `n+1` membership semantics, and full terminal statement.
- SafeVerify statement hash is
  `dc280a8f2beb7ccffc95195b4a6b69cc9161585aa8d4d608b3278c89b7bb13a5`.
- All four declarations report only `propext`, `Classical.choice`, and
  `Quot.sound` in the axiom audit.
- Independent review found no P0/P1/P2; its P3 retrieval-timing ambiguity is
  closed.
- Lifecycle review/build records are accepted; verified memory is
  `mem-b8cfa9865d91f12a`; frontier shadow reports zero mismatches; and
  `python3 tools/bandit.py check` passes with 36 tests and one expected skip.
