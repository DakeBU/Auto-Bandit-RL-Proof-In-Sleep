# Conversion Window: Countable scheduled quadratic fixed-MGF tail

Task id: `CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`; `PPR-AUER-CFS-2002-EXP3`
is downstream placement only.
Scenario card: `SCN-ADVERSARIAL-FINITE`

## Natural-Language Statement

For every natural index `n`, suppose the same quadratic fixed-tilt route gives
the scheduled deviation/variance event mass at most `deltaAt n`.
Then the mass of at least one scheduled failure is at most
`sum' n, ENNReal.ofReal (deltaAt n)`. If this sum fits an outer confidence
budget, the countable failure event fits that budget as well.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `r_n` | time-indexed optimized quadratic radius | `quadraticFixedMGFScheduledRadius` | compiled |
| `E_n` | `r_n <= deviation n` and `predictableVariance n <= varianceBudget n` | set-builder in the terminal | compiled |
| `delta_n` | positive scheduled confidence share | `deltaAt n` | explicit assumption |
| `union_n E_n` | countable scheduled failure event | `Set.iUnion` | Mathlib-backed |
| `sum_n delta_n` | total ENNReal confidence budget | `sum' n, ENNReal.ofReal (deltaAt n)` | Mathlib-backed |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| measurable ambient space | typeclass | Mathlib measure API | no |
| positive scale, variance budget, tilt cap, and share at each index | explicit families | parent quadratic theorem | no |
| fixed-tilt quadratic tail family at each index | explicit higher-order premise | local parent route | no |
| event measurability | deliberately absent | outer measure union bound | no |
| finite/probability measure | deliberately absent | theorem is outer-measure monotonicity | no |
| independence, filtration, bounded increments | deliberately absent | supplied by downstream fixed-tail producers | no |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Intended route | Pivot rule |
| --- | --- | --- | --- |
| N0 radius | `ConcentrationQuadraticFixedMGF.quadraticFixedMGFRadius` | specialize all four parameter families at `n` | keep time-varying families |
| N1 pointwise tail | `measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail` | invoke at each `n`, rewriting only N0 | do not add regularity |
| N2 countable union | `MeasureTheory.measure_iUnion_le`; `ENNReal.tsum_le_tsum` | countable outer-measure union then termwise N1 | do not require measurable events |
| N3 outer budget | N2 and `le_trans` | compose with caller's ENNReal budget | do not choose a schedule in this leaf |

## Proof DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| N0 | scheduled radius | quadratic parent definition | lower | `quadraticFixedMGFScheduledRadius` | none | focused | compiled |
| N1 | pointwise scheduled delta tail | N0 and quadratic parent theorem | lower | internal specialization | four positive families | focused | compiled |
| N2 | countable tsum tail | N1 and countable outer union | lower | `measure_iUnion_scheduled_deviation_ge_inter_variance_le_tsum_of_fixedTilt_quadratic_tail` | measurable ambient space | focused/Tests | compiled |
| root | outer-budget tail | N2 and caller budget | lower | `measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail` | displayed ENNReal budget | full harness | accepted |

## Gaps

- [x] No existing local countable scheduled quadratic wrapper was found.
- [x] Single-event and finite-index parent routes compile.
- [x] Mathlib supplies countable outer-measure subadditivity and ENNReal tsum monotonicity.
- [x] Lean source and external canary compile.
- [x] Evidence/index/status synchronization and full harness pass.
