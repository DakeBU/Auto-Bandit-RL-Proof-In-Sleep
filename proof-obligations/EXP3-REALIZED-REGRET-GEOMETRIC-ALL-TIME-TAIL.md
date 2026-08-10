# Proof Obligations: Generated EXP3 realized-regret geometric all-time tail

Task id: `EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

| Node | Target | Local APIs/imports | Retrieval | Proof route | Regularity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `DECOMPOSITION` | exact finite-prefix `realized regret = predictable regret + realized deviation` | deviation definition; `Finset.sum_sub_distrib`; ring | fixed-horizon local precedent; finite-sum/order cards | unfold, distribute sum subtraction, normalize ring | measurable Env/Action; decidable Action | compiled |
| `BUDGET-EVENT` | sum of accepted schedules at `delta/2`; named positive-prefix union and membership | both accepted all-time modules | local parent cards | definitions and `Set.mem_iUnion` simplification | definitions plus local instances | compiled |
| `INCLUSION` | combined failure subset of predictable/deviation failure union | both parent membership theorems; decomposition | local accepted parents | assume neither component crossing, obtain strict bounds, add and contradict | no measure assumptions | compiled |
| `ROOT` | combined event outer measure `<= ENNReal.ofReal delta` | both accepted outer-measure tails; `measure_mono`; `measure_union_le`; `ENNReal.ofReal_add` | local parents; Mathlib measure/order cards | half-budget specialization, union bound, exact half normalization | probability/Standard-Borel generated process; supported comparator; `eta>0`; `0<gamma<1`; `delta>0` | accepted |

## Reviewer Checklist

- `prior`, arms, `eta`, `gamma`, loss, and comparator remain outside the index.
- Every event uses exactly `Finset.range (n+1)`.
- Each component family receives total confidence `delta/2`.
- The realized-regret sign is selected loss minus comparator loss.
- The conclusion is outer measure and assumes no event measurability.
- No tuned all-time rate, best-arm union, Freedman, or EXP3.P claim is made.

## Failure Classification

Record exactly one first blocker: decomposition normalization, event inclusion,
confidence-half normalization, parent-law mismatch, or false statement. Do not
weaken to a fixed horizon or vary process parameters with the countable index.
