# Proof Obligations: Countable scheduled quadratic fixed-MGF tail

Task id: `CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`; downstream placement
`PPR-AUER-CFS-2002-EXP3`
Scenario card: `SCN-ADVERSARIAL-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `SCHEDULED-RADIUS` | time-indexed quadratic radius | fixed-MGF delta parent | `ConcentrationQuadraticFixedMGF` | local parent; real log/sqrt cards | pointwise definition | none | compiled |
| `POINTWISE-TAIL` | each scheduled event has mass at most `ofReal (deltaAt n)` | scheduled radius; fixed-tilt family | parent quadratic delta theorem | local-first | specialize parent at `n` | all four parameter families positive | compiled |
| `COUNTABLE-TSUM` | countable union mass is at most the sum of scheduled ENNReal shares | pointwise tail | `measure_iUnion_le`; `ENNReal.tsum_le_tsum` | `MLIB-MEASURE-INTEGRAL` | outer subadditivity then termwise comparison | measurable ambient space only | compiled |
| `OUTER-BUDGET` | countable union mass is at most `ofReal delta` under a supplied total budget | countable-tsum theorem | order transitivity | `MLIB-ORDER-ALGEBRA` | compose with budget inequality | no extra positivity/measurability | accepted |

## Failure Classification

Record exactly one first failure: scheduled-radius elaboration, pointwise
quadratic-parent specialization, countable-union elaboration, ENNReal tsum
monotonicity, or false statement. Do not add event measurability, probability,
independence, `deltaAt n <= 1`, finite-horizon truncation, Ville/Doob,
optional stopping, self-normalization, general Freedman, or ideal EXP3.P.

## Reviewer Checklist

- Every index may use different scale, variance budget, tilt cap, and share.
- Positivity is required exactly where the parent optimizer requires it.
- The theorem uses outer-measure countable subadditivity, so events need not be measurable.
- The second terminal only consumes a caller-supplied ENNReal total budget.
- No theorem card or proof weapon is treated as local proof evidence.
