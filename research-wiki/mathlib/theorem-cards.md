# Mathlib Retrieval Cards For Bandit/RL Leaves

These cards record Mathlib APIs that ABRL agents should search before creating
new general-purpose lemmas.  A card is not a local proof certificate.  It is an
import/search route for future Mathlib-backed tasks.

Refresh the compact JSON index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-mathlib
python3 tools/bandit.py search-memory Finset.sum
```

## Cards

| Card | Mathlib modules | Search terms | Bandit/RL use |
| --- | --- | --- | --- |
| `MLIB-FINSET-SUMS` | `Mathlib.Data.Finset.Basic`, `Mathlib.Algebra.BigOperators.Fin` | `Finset.sum`, `Finset.range`, `sum_filter`, `sum_congr`, `card_filter` | pull-count decomposition, finite action sums, indicator partitions |
| `MLIB-FINTYPE-FIN` | `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Fin.Basic` | `Fintype.card`, `Fin`, `Finite`, `Nonempty`, `Fin.cast` | finite arms, nonempty action sets, finite policies |
| `MLIB-ORDER-ALGEBRA` | `Mathlib.Algebra.Order.Field.Basic`, `Mathlib.Data.Real.Basic` | `div_le_iff`, `mul_le_mul`, `Nat.cast_pos`, `linarith`, `nlinarith` | gap positivity, UCB radius algebra, denominator side conditions |
| `MLIB-REAL-LOG-SQRT` | `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Data.Real.Sqrt` | `Real.log`, `Real.sqrt`, `sq_sqrt`, `log_nonneg`, `sqrt_le_sqrt` | UCB confidence widths and logarithmic regret |
| `MLIB-MEASURE-INTEGRAL` | `Mathlib.MeasureTheory.Integral.Bochner.Basic` | `Integrable`, `integral`, `lintegral`, `AEStronglyMeasurable`, `AEMeasurable` | expectations, Bayesian regret, integrability contracts |
| `MLIB-PROBABILITY-INDEPENDENCE` | `Mathlib.Probability.Independence.Basic` | `IndepFun`, `iIndepFun`, `IndepSet`, `IdentDistrib` | IID rewards, product events, concentration theorem assumptions |
| `MLIB-CONDITIONAL-EXPECTATION` | `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic` | `condexp`, `filtration`, `adapted`, `martingale`, `stoppingTime` | adaptive rewards, posterior identities, martingale concentration |
| `MLIB-PROBABILITY-KERNEL` | `Mathlib.Probability.Kernel.Basic` | `Kernel`, `bind`, `comp`, `prod` | reward kernels, posterior kernels, finite-horizon MDP policies |
| `MLIB-ASYMPTOTICS` | `Mathlib.Analysis.Asymptotics.Asymptotics` | `Asymptotics.IsBigO`, `IsTheta`, `Eventually`, `Filter.atTop` | logarithmic regret, minimax rates, asymptotic theorem exports |
| `MLIB-CONVEX-LINALG` | `Mathlib.Analysis.Convex.Basic`, `Mathlib.LinearAlgebra.Matrix` | `Convex`, `Matrix`, `inner`, `norm`, `IsBounded` | linear bandits, confidence ellipsoids, least-squares design |

## Retrieval Rule

Before opening a `mathlib-candidate` proof leaf, middle agents should record:

- the card id;
- the exact module/import candidates;
- search terms already tried;
- local APIs that should bridge ABRL definitions to Mathlib names;
- whether the result should be imported, ported, or proposed upstream.

Lower agents should not invent generic finite-sum, order, measurability,
integrability, or asymptotic lemmas before checking this index.
