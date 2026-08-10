# Proof Obligations: Generated EXP3 predictable-regret geometric all-time tail

Task id: `EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

| Node | Target | Local APIs/imports | Retrieval | Proof route | Regularity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `SCHEDULED-BUDGET` | parent predictable-regret budget at horizon `n+1` and confidence `geometricShare delta n / 2` | `sampledPredictableHighProbabilityRegretBudget`; `Concentration.geometricConfidenceShare` | fixed-horizon predictable-regret card; geometric schedule card | definitional specialization preserving the parent's inner two-event split | definitions only | compiled |
| `ALL-TIME-EVENT` | named union of all scheduled predictable-regret crossings with exact membership | finite prefix sums; `Set.mem_iUnion` | local event precedents | define union and simplify membership | measurable Env/Action; decidable Action | compiled |
| `ALL-TIME-ROOT` | event outer measure `<= ENNReal.ofReal delta` | fixed-horizon total tail; `measure_iUnion_le`; `ENNReal.tsum_le_tsum`; exact geometric tsum | local parents; `MLIB-MEASURE-INTEGRAL`; order/finite-sum cards | specialize every `n+1`; compare tsums; rewrite exact total | probability/Standard-Borel generated process; supported comparator; `eta>0`; `0<gamma<1`; `delta>0` | accepted |

## Reviewer Checklist

- `prior`, arms, `eta`, `gamma`, loss, and comparator are outside the index.
- Every event uses exactly `Finset.range (n+1)`.
- The scheduled event budget uses `geometricConfidenceShare delta n / 2`.
- The outer summand is `ofReal (geometricConfidenceShare delta n)`.
- The conclusion is outer measure and does not assume event measurability.
- No realized-regret, tuning, Ville/Doob, Freedman, or EXP3.P claim is made.

## Failure Classification

Record exactly one first blocker: parent-budget mismatch, countable union,
ENNReal tsum, false statement, or downstream realized-regret assembly. Do not
weaken the target to a fixed horizon or allow process parameters to vary with
the countable index.
