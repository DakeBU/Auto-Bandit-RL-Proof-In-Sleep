# Mathlib Retrieval Cards For Bandit/RL Leaves

These cards record Mathlib APIs that ABRL agents should search before creating
new general-purpose lemmas.  A card is not a local proof certificate.  It is an
import/search route for future Mathlib-backed tasks.

Refresh the compact JSON index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-mathlib
python3 tools/bandit.py search-memory Finset.sum
python3 tools/bandit.py list-lean-decls pullCount
```

## Cards

| Card | Mathlib modules | Search terms | Bandit/RL use |
| --- | --- | --- | --- |
| `MLIB-FINSET-SUMS` | `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Card`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Field.Rat` | `Finset.sum`, `Finset.range`, `Finset.card`, `Finset.sum_range_succ`, `Finset.filter_insert`, `sum_filter`, `sum_congr`, `card_filter` | pull-count decomposition, finite action sums, indicator partitions |
| `MLIB-NAT-LOG-POW` | `Mathlib.Data.Nat.Log` | `Nat.le_log2`, `Nat.log2_eq_log_two`, `Nat.log_pow`, `Nat.pow_le_pow_iff_right`, `Nat.pow_pos` | logarithmic forcing schedules, doubling epochs, power-of-two prefix counts |
| `MLIB-FINTYPE-FIN` | `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Fin.Basic` | `Fintype.card`, `Fin`, `Finite`, `Nonempty`, `Fin.cast` | finite arms, nonempty action sets, finite policies |
| `MLIB-ORDER-ALGEBRA` | `Mathlib.Algebra.Order.Field.Basic`, `Mathlib.Data.Real.Basic` | `div_le_iff`, `mul_le_mul`, `Nat.cast_pos`, `linarith`, `nlinarith` | gap positivity, UCB radius algebra, denominator side conditions |
| `MLIB-REAL-LOG-SQRT` | `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Data.Real.Sqrt` | `Real.log`, `Real.sqrt`, `sq_sqrt`, `log_nonneg`, `sqrt_le_sqrt` | UCB confidence widths and logarithmic regret |
| `MLIB-EXP-LOG-INEQUALITIES` | `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `Real.exp`, `Real.log`, `exp_le_exp`, `log_le_iff_le_exp`, `rpow` | exponential weights, Chernoff routes, KL-UCB algebra |
| `MLIB-MEASURE-INTEGRAL` | `Mathlib.MeasureTheory.MeasurableSpace.Basic`; `Mathlib.MeasureTheory.Integral.Bochner.Basic`; `Mathlib.MeasureTheory.Integral.Lebesgue.Markov` | `Measurable`, `MeasurableSet`, `MeasurableSingletonClass`, `MeasurableSet.singleton`, `Measurable.indicator`, `Integrable`, `integral`, `lintegral`, `AEStronglyMeasurable`, `AEMeasurable`, `meas_ge_le_lintegral_div`, `mul_meas_ge_le_lintegral` | measurable action-event and indicator canaries, expectations, Bayesian regret, integrability contracts, Markov overflow tails |
| `MLIB-PROBABILITY-INDEPENDENCE` | `Mathlib.Probability.Independence.Basic` | `IndepFun`, `iIndepFun`, `IndepSet`, `IdentDistrib` | IID rewards, product events, concentration theorem assumptions |
| `MLIB-CONDITIONAL-EXPECTATION` | `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic` | `condexp`, `filtration`, `adapted`, `martingale`, `stoppingTime` | adaptive rewards, posterior identities, martingale concentration |
| `MLIB-MARTINGALE-STOCHASTIC` | `Mathlib.Probability.Martingale.Basic`, `Mathlib.Probability.Notation` | `Martingale`, `Submartingale`, `Supermartingale`, `filtration`, `stoppingTime` | self-normalized processes, delayed feedback, finite-horizon RL regret |
| `MLIB-PROBABILITY-KERNEL` | `Mathlib.Probability.Kernel.Basic` | `Kernel`, `bind`, `comp`, `prod` | reward kernels, posterior kernels, finite-horizon MDP policies |
| `MLIB-PROBABILITY-POSTERIOR` | `Mathlib.Probability.Kernel.Posterior`, `Mathlib.Probability.Kernel.CondDistrib` | `ProbabilityTheory.posterior`, `compProd_posterior_eq_map_swap`, `condDistrib_ae_eq_iff_measure_eq_compProd`, `Measure.snd_compProd` | canonical prior-likelihood posterior kernels and environment-given-history conditional-law identification |
| `MLIB-ASYMPTOTICS` | `Mathlib.Analysis.Asymptotics.Lemmas`; `Mathlib.Analysis.SpecialFunctions.Log.Base`; `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics` | `Asymptotics.IsBigO`, `Asymptotics.IsLittleO`, `IsTheta`, `IsBigO.sqrt`, `isLittleO_log_rpow_atTop`, `IsBigO.trans_isLittleO`, `IsLittleO.tendsto_div_nhds_zero`, `Eventually`, `Filter.atTop` | logarithmic regret, average-regret consistency, minimax rates, asymptotic theorem exports |
| `MLIB-CH16-DINF-ASYMPTOTICS` | `Mathlib.Order.ConditionallyCompleteLattice.Basic`; `Mathlib.Data.ENNReal.Operations`; `Mathlib.Analysis.SpecialFunctions.Pow.Real`; `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `sInf`, `sInf_le`, `le_sInf`, `Tendsto.add`, `Filter.eventually_atTop`, `Tendsto.eventually_lt_const`, `Real.rpow_pos_of_pos`, `Real.log_le_log`, `Real.log_rpow` | Chapter 16 extended-real `d_inf` candidate bounds, exact consistency closure, eventual every-power domination, and the logarithmic pre-limsup adapter; it does not supply the bandit history information constraint |
| `MLIB-CONVEX-LINALG` | `Mathlib.Analysis.Convex.Basic`, `Mathlib.LinearAlgebra.Matrix` | `Convex`, `Matrix`, `inner`, `norm`, `IsBounded` | linear bandits, confidence ellipsoids, least-squares design |
| `MLIB-PROBABILITY-SUBGAUSSIAN` | `Mathlib.Probability.Moments.SubGaussian` | `measure_sum_ge_le_of_iIndepFun`, `HasSubgaussianMGF`, `measure_sum_ge_le_of_HasCondSubgaussianMGF` | Hoeffding-style tails, sub-Gaussian reward sums, UCB/ETC concentration |
| `MLIB-GAUSSIAN-REAL-TAIL` | `Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence`, `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` | `gaussianReal`, `charFun_map_sum_pi_eq_prod`, `charFun_gaussianReal`, `gaussianReal_map_div_const`, `mgf_id_gaussianReal`, `HasSubgaussianMGF.measure_ge_le`, `integral_gaussian_Ioi` | Chapter 13 canonical finite-iid empirical-mean law and two-hypothesis Chernoff upper tail compile from these APIs; no exact Mills-ratio upper/lower theorem was found at pinned Mathlib `5e932f9`, so Eq. (13.1)/(13.4) remains a separate candidate |
| `MLIB-PROBABILITY-MGF` | `Mathlib.Probability.Moments.Basic`, `Mathlib.Probability.Moments.Tilted` | `mgf`, `cgf`, `IndepFun.mgf_add`, `IndepFun.cgf_add` | Chernoff routes, exponential weights, MGF algebra |
| `MLIB-PROBABILITY-VARIANCE` | `Mathlib.Probability.Moments.Variance` | `variance`, `chebyshev`, `IndepFun.variance_add`, `MemLp` | variance tails, robust/heavy-tailed baselines, second-moment contracts |
| `MLIB-REAL-RPOW-TSALLIS` | `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` | `Real.rpow`, `NNReal.rpow`, `rpow_le_rpow`, `rpow_pos_of_pos` | Tsallis entropy regularizers, FTRL/OMD power potentials |
| `MLIB-METRIC-TOPOLOGY` | `Mathlib.Topology.MetricSpace.Basic` | `Metric.ball`, `Metric.closedBall`, `LipschitzWith`, `TotallyBounded`, `diam` | Lipschitz/continuum bandits, covering arguments, metric action spaces |

## Retrieval Rule

Before opening a `mathlib-candidate` proof leaf, middle agents should record:

- the card id;
- the exact module/import candidates;
- search terms already tried;
- local APIs that should bridge ABRL definitions to Mathlib names;
- whether the result should be imported, ported, or proposed upstream.

Lower agents should not invent generic finite-sum, order, measurability,
integrability, or asymptotic lemmas before checking this index.
