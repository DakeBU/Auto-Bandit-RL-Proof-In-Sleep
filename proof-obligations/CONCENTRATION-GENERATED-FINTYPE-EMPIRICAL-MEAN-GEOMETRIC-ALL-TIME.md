# Proof Obligations: Generated finite-arm empirical-mean geometric all-time confidence

Task id: `CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-GEOMETRIC-ALL-TIME`

| Node | Target | Local APIs/imports | Retrieval | Regularity | Status |
| --- | --- | --- | --- | --- | --- |
| `ONE-ARM-TIME` | one random-count empirical-mean tail at horizon `n+1` | canonical partial-trajectory masked-law theorem | conditional MGF, predictable variance, exact-count peeling cards | global variance ceiling specialized to the prefix; stationary arm mean; positive share | compiled |
| `FINITE-ARMS` | all arms at time `n` receive equal geometric shares | `Fintype.card_pos`; finite-index union parent | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL` | finite nonempty action | compiled |
| `ALL-TIME-ROOT` | nested time/arm failure union `<= ofReal delta` | geometric all-time adapter | accepted local parent | same canonical measure; `delta>0` | accepted |

## Reviewer Checklist

- The same `Kernel.trajMeasure` is used for every time and arm.
- The time index `n` denotes successor horizon `n+1`.
- Each arm gets exactly `geometricConfidenceShare delta n / card(Action)`.
- The random-count parent retains its internal positive-count fiber peeling.
- Global variance and stationary-mean premises really specialize to every
  prefix/arm without changing quantifier order.
- No theorem card or proof weapon is used as a Lean certificate.
- The conclusion remains an empirical-mean confidence event, not UCB regret.

## Failure Classification

Record exactly one first failure: generated-let alignment, finite-card
positivity, prefix variance specialization, confidence-share elaboration,
nested union normalization, public canary, or false target.
