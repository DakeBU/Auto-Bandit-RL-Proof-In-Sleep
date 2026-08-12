# Finite-index geometric all-time confidence union

Task id: `CONCENTRATION-FINTYPE-GEOMETRIC-ALL-TIME-UNION`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

Compose the compiled finite equal-share outer-measure union bound with the
compiled geometric confidence schedule. For a nonempty finite index type,
give every index budget `geometricConfidenceShare delta n / card` at time
`n`, then bound the union over every time and index by `ENNReal.ofReal delta`.

## Source

- Book Map placement: Chapter 2 probability/concentration, supporting the
  simultaneous confidence interfaces used by Chapters 3 and 4.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` (concentration spine).
- Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-CONTEXTUAL-FINITE`.
- Local parents: `LOCAL-LEAF-TAIL-UNION-FINITE` and
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`.
- `WEAPON-TAIL-INEQUALITIES` is route inspiration only.

## Lean Target

```lean
Concentration.measure_iUnion_iUnion_fintype_le_tsum_of_uniform
Concentration.measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare
```

Target file: `BanditRLProof/ConcentrationFintypeGeometricAllTime.lean`

## Proof Obligations

- [x] Exact finite-index/countable-time statement and index order are fixed.
- [x] Nonempty finite-index normalization is explicit.
- [x] Local and Mathlib retrieval evidence is recorded.
- [x] Focused source compiles.
- [x] Root import and external canaries are present.
- [x] Statement fence and SafeVerify pass.
- [x] Both public declarations use only baseline axioms.
- [x] Independent read-only review has no P0/P1; its four P2 harness findings
  are repaired and regression-tested.
- [x] Website source/build/check is synchronized.
- [x] Verified memory, accepted frontier, zero-mismatch shadow, and the full
  harness gate pass.

## Local APIs, Route, And Contracts

| Node | APIs/imports | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- |
| finite union at time `n` | `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`; `Finset.univ_nonempty` | specialize the equal-share theorem to all indices | measurable ambient space; `Fintype Idx`; `Nonempty Idx` | compiled |
| countable time union | `MeasureTheory.measure_iUnion_le`; `ENNReal.tsum_le_tsum` | outer-measure subadditivity then pointwise finite union | no event measurability or finite/probability measure | compiled |
| geometric terminal | `tsum_ofReal_geometricConfidenceShare` | rewrite the exact scheduled total | `0 <= delta` only | compiled |

## Retrieval Evidence

- Local: `LOCAL-LEAF-TAIL-UNION-FINITE`,
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`, and the
  countable-scheduled concentration precedent.
- Mathlib: `MeasureTheory.measure_iUnion_le`,
  `MeasureTheory.measure_biUnion_finset_le`, `ENNReal.tsum_le_tsum`, and
  finite-sum/card normalization APIs; indexed under `MLIB-MEASURE-INTEGRAL`,
  `MLIB-FINSET-SUMS`, and `MLIB-ORDER-ALGEBRA`.
- Source/scenario: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `SCN-STOCHASTIC-FINITE`, `SCN-CONTEXTUAL-FINITE`.

## Failure Policy

If compilation or review fails, classify the first blocker as finite-card
normalization, nested `iUnion` elaboration, countable outer-measure
subadditivity, geometric `tsum` rewriting, or a false statement. Preserve the
finite-index and all-time quantifiers. Do not add event measurability,
probability normalization, independence, filtration, `delta <= 1`, a concrete
tail producer, or claims of Ville/Doob, mixture, optional stopping,
self-normalization, general Freedman, ETC regret, or UCB regret.

## Verification

- Focused module, project root, `Tests`, and external root-import canary: passed.
- SafeVerify statement hash:
  `4df3691cb62b7389a0d544c661127aaca4ec3a81981d0474430dad1f5ca2c179`.
- Both declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
- Website build/check passes with zero placeholders. The paper harness rebuilds
  to 25 pages.
- Independent review has no P0/P1; all four P2 harness findings are repaired,
  with 41 focused Python tests passing and one expected skip.
- Verified lemma: `mem-99363842cb89e027`; accepted frontier DAG and current
  memory digest reconstruct with zero mismatches.
- Full `python3 tools/bandit.py check`: passed with 41 Python tests and one
  expected skip.
