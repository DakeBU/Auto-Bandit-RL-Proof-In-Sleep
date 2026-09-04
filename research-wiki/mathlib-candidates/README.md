# Mathlib Candidate Leaves

This directory records proof-DAG leaves that are general enough to prepare for
future Mathlib contribution.  A candidate is not accepted as local certified
memory until it compiles in this repository or is imported from an upstream
library.

## Candidate Record

Use one section per candidate:

```text
## CANDIDATE-ID

- Proposed name:
- Mathematical area:
- Intended Mathlib namespace:
- Exact statement:
- Required imports:
- Local APIs:
- Intended proof route:
- Regularity contracts:
- Current ABRL task:
- Status: proposed | in-progress | locally-compiled | upstreamed | rejected
- Failure signal:
```

## Seed Areas For Bandit/RL Proofs

| Area | Typical leaf | Why it should be reusable |
| --- | --- | --- |
| Finite sums | pull-count decompositions, indicator sums, finite support rewrites | common across bandit, online learning, and probability proofs |
| Order and algebra | gap nonnegativity, monotone confidence radii, denominator positivity | not bandit-specific when stated cleanly |
| Regularity | integrability, measurability, continuity, nonemptiness, boundedness | hidden assumptions should become theorem contracts |
| Concentration infrastructure | union bounds, tail-event monotonicity, sub-Gaussian closure | useful beyond a single regret proof |
| Asymptotics | logarithmic and square-root regret simplifications | should not be buried inside algorithm proofs |

## HAS-SUBGAUSSIAN-MGF-INTEGRAL-SQ

- Proposed name: `HasSubgaussianMGF.integral_sq_le_four_mul_proxy_mul_exp_half`.
- Mathematical area: probability moments and sub-Gaussian MGFs.
- Intended Mathlib namespace: `ProbabilityTheory.HasSubgaussianMGF`.
- Exact statement: on a probability measure, a real random variable with
  sub-Gaussian proxy `c` satisfies
  `integral mu (fun omega => X omega ^ 2) <= 4 * c * exp (1/2)`.
- Required imports: `Mathlib.Probability.Moments.SubGaussian` and Bochner
  integral basics.
- Local APIs: `HasSubgaussianMGF.memLp`, `integrable_exp_mul`, `mgf_le`,
  `Real.quadratic_le_exp_of_nonneg`, `Real.exp_abs_le`, and `integral_mono`.
- Intended proof route: split `c=0`; otherwise evaluate positive and negative
  MGFs at `1/sqrt c`, use `y^2 <= 2 exp |y|`, and rescale.
- Regularity contracts: probability measure and global sub-Gaussian MGF; no
  independence or explicit mean premise.
- Current ABRL task:
  `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-DETERMINISTIC-MOMENT-EXPECTED-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Status: locally-compiled in
  `BanditRLProof.Concentration.integral_sq_le_four_mul_proxy_mul_exp_half_of_hasSubgaussianMGF`.
- Failure signal: do not substitute the sharper `E[X^2] <= c` without a
  compiled derivative/variance bridge; the conservative exponential constant
  is the frozen route.

## KL-DATA-PROCESSING-MEASURABLE-MAP

- Proposed name: `InformationTheory.klDiv_map_le`.
- Mathematical area: finite measures, relative entropy, measurable maps, and
  conditional expectation.
- Intended Mathlib namespace: `InformationTheory`.
- Exact statement: for finite measures `mu, nu` and measurable `observe`,
  `klDiv (mu.map observe) (nu.map observe) <= klDiv mu nu`.
- Required imports:
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen` and
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym`.
- Local APIs: `MeasureTheory.toReal_rnDeriv_map`,
  `InformationTheory.convexOn_klFun.map_condExp_le`,
  `InformationTheory.integrable_klFun_rnDeriv_iff`,
  `InformationTheory.toReal_klDiv_eq_integral_klFun`, and
  `integral_condExp`.
- Intended proof route: keep infinite source KL as a direct top branch; in the
  finite branch use absolute continuity, identify the mapped density with a
  conditional expectation, establish mapped `klFun` integrability, apply
  conditional Jensen, and compare the two real KL integrals.
- Regularity contracts: arbitrary measurable source and target spaces, finite
  source laws, and a measurable map. No injectivity, probability
  normalization, standard-Borel hypothesis, or finite-KL premise is required.
- Current ABRL task:
  `TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE`.
- Status: locally-compiled as `BanditRLProof.LowerBounds.klDiv_map_le`, with a
  deterministic bandit-history consumer for the first leaf of Exercise 15.7.
- Failure signal: this data-processing theorem does not construct a stopped
  history, truncate the Lemma 15.1 information sum at a random time, or factor
  an arbitrary `F_tau`-measurable observation.

## Review Rule

Before adding tactic work, the candidate must name local APIs and an intended
proof route.  If repeated attempts fail, record whether the likely issue is a
false statement, missing assumption, wrong abstraction, unavailable API, or
counterexample.  Do not repeatedly rewrite the proof route without that audit.

## STOPPING-FIBER-SQRT-SUM-SECOND-MOMENT

- Proposed name:
  `tsum_sqrt_stoppingFiberRealMeasure_le_half_mul_integral_rounds_sq_add_tsum_inverse_natSuccSquare_of_memLp_two`.
- Mathematical area: probability moments and countable stopping-time fibers.
- Intended Mathlib namespace: `MeasureTheory` or `ProbabilityTheory`.
- Exact statement: for a finite measure and a measurable a.e.-finite
  `tau : Omega -> WithTop Nat` whose real successor-round count belongs to
  `MemLp 2`, the sum of square roots of the real equality-fiber masses is at
  most one half of the successor-round second moment plus
  `∑' n, 1 / (n+1)^2`.
- Required imports: Bochner/Lebesgue integration, ENNReal infinite sums,
  `Mathlib.Analysis.PSeries`, and `MemLp` moment APIs.
- Local APIs:
  `tsum_natSuccSquare_mul_stoppingFiberMeasure_eq_lintegral_rounds_sq`,
  `ENNReal.tsum_toReal_eq`, `integral_eq_lintegral_of_nonneg_ae`,
  `Real.summable_one_div_nat_pow`, and `Summable.tsum_add`.
- Intended proof route: decompose the squared successor round into equality
  fibers in ENNReal, take `toReal` using L2 finiteness, identify the Bochner
  second moment, and sum
  `sqrt p <= ((n+1)^2*p + (n+1)^-2)/2` from a completed square.
- Regularity contracts: finite measure; measurable and a.e.-finite stopping
  map; `MemLp 2` successor-round count. No stopping-time filtration,
  independence, or optional-stopping premise is needed.
- Current ABRL task:
  `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPING-ROUND-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Status: locally-compiled in
  `BanditRLProof.UnboundedStoppingTimeL2CoordinateIntegrability`.
- Failure signal: do not apply `ENNReal.toReal` without a finite weighted sum;
  retain `MemLp 2` or replace it with an explicit finite-second-moment
  contract. The theorem is fixed-stop quantitative transport, not a uniform
  family or optional-stopping result.

## TENDSTO-NAT-POSITIVE-WEIGHTED-AVERAGE-ZERO

- Proposed name: `tendsto_natWeightedAverage_zero`
- Mathematical area: asymptotics and finite weighted averages
- Intended Mathlib namespace: `Filter`
- Exact statement: for `weight : Nat -> Nat` with `0 < weight t` and
  `value : Nat -> Real` tending to zero at `atTop`, the quotient of
  `sum_{t<n} weight(t) * value(t)` by `sum_{t<n} weight(t)` tends to zero.
- Required imports: `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`
- Local APIs: `Asymptotics.isLittleO_one_iff`,
  `Asymptotics.IsLittleO.mul_isBigO`,
  `Asymptotics.IsLittleO.sum_range`,
  `Asymptotics.IsLittleO.tendsto_div_nhds_zero`,
  `tendsto_atTop_mono`, and `tendsto_natCast_atTop_atTop`.
- Intended proof route: convert `value -> 0` to `value =o 1`; multiply by
  the nonnegative real-cast weights; use positivity to lower-bound the
  denominator sum by `n`; apply `sum_range`; divide the summed little-o
  relation by its denominator.
- Regularity contracts: strictly positive natural weights and real-valued
  values; positivity supplies both nonnegative summands and denominator
  divergence. No monotonicity or upper bound on weights is required.
- Current ABRL task:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EXPLICIT-WEIGHTED-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
- Status: locally-compiled
- Failure signal: nonnegative weights alone do not force denominator
  divergence; retain strict positivity or replace it with an explicit
  denominator-atTop assumption. This candidate proves a deterministic limit,
  not a probabilistic or Cesaro-rate theorem.

## KERNEL-HAS-SUBGAUSSIAN-MGF-OF-AE-FIBERS

- Proposed name: `Kernel.HasSubgaussianMGF.of_ae_fibers`
- Mathematical area: probability kernels and sub-Gaussian MGFs
- Intended Mathlib namespace: `ProbabilityTheory.Kernel.HasSubgaussianMGF`
- Exact statement: for a finite base measure `mu`, measurable `X`, a kernel
  `kernel`, and common proxy `c`, if
  `∀ᵐ alpha ∂mu, HasSubgaussianMGF X c (kernel alpha)`, then
  `Kernel.HasSubgaussianMGF X c kernel mu`. A companion Dirac specialization
  recovers the selected fiber when the base has measurable singletons.
- Required imports: `Mathlib.Probability.Moments.SubGaussian` and
  `Mathlib.Probability.Kernel.Composition.IntegralCompProd`
- Local APIs: `Measure.integrable_comp_iff`,
  `StronglyMeasurable.integral_kernel`, `Integrable.of_bound`,
  `Kernel.HasSubgaussianMGF.of_rat`, and
  `Measure.ae_integrable_of_integrable_comp`.
- Intended proof route: prove composed exponential integrability fiberwise;
  bound the measurable inner norm integral by the common exponential MGF
  envelope under the finite base measure; pass rational MGF bounds directly
  to `of_rat`. For the companion, extract integrability and MGF inequalities
  from the Dirac-a.e. kernel statement.
- Regularity contracts: finite base measure and measurable random variable;
  no Markov-kernel premise is needed by the compiled statement. The Dirac
  companion additionally needs `MeasurableSingletonClass` on the base.
- Current ABRL task:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-CUMULATIVE-DEVIATION-SUBGAUSSIAN-TAIL`
- Status: locally-compiled
- Failure signal: a pointwise MGF bound alone is insufficient unless the
  composed exponential is integrable; retain the common proxy and finite-base
  envelope rather than dropping the integrability branch.

## MEASURE-MAP-COMPPROD-COMAP-HISTORY

- Proposed name: `Measure.map_compProd_comap`
- Mathematical area: probability kernels and composition-product measures
- Intended Mathlib namespace: `MeasureTheory.Measure`
- Exact statement: for a finite measure `mu`, measurable
  `history : Omega -> History`, and Markov kernel `policy : Kernel History Action`,
  `(mu ⊗ₘ policy.comap history hhistory).map
  (fun sample => (history sample.1, sample.2)) = mu.map history ⊗ₘ policy`.
- Required imports: `Mathlib.Probability.Kernel.Composition.Lemmas`
- Local APIs: `Measure.ext_prod`, `Measure.compProd_apply_prod`,
  `Kernel.comap_apply`, and `MeasureTheory.setLIntegral_map`.
- Intended proof route: use finite product-measure extensionality; rewrite the
  preimage of a measurable rectangle; expand both composition products; move
  the policy event-probability integral across `Measure.map history`.
- Regularity contracts: finite base measure; measurable source, history, and
  action spaces; measurable history map; Markov policy kernel.
- Current ABRL task:
  `LOCAL-LEAF-TS-REFERENCE-POSTERIOR-POLICY-SAMPLER`
- Status: locally-compiled
- Failure signal: `Measure.ext_prod` needs a finite base measure in this route;
  do not assume the projected history/action law when the `compProd`
  construction can prove it.

## MEASURE-COMPPROD-WITHDENSITY-LEFT

- Proposed name: `Measure.compProd_withDensity_left`
- Mathematical area: probability kernels and density-weighted measures
- Intended Mathlib namespace: `MeasureTheory.Measure`
- Exact statement: for an s-finite history law `nu`, Markov kernel
  `posterior`, measurable `density : History -> ENNReal`, and finite weighted
  base measure,
  `(nu.withDensity density) ⊗ₘ posterior =
  (nu ⊗ₘ posterior).withDensity (density ∘ Prod.fst)`.
- Required imports: `Mathlib.Probability.Kernel.CompProdEqIff`
- Local APIs: `Measure.ext_prod`, `Measure.compProd_apply_prod`,
  `Measure.setLIntegral_compProd`,
  `setLIntegral_withDensity_eq_setLIntegral_mul`, and
  `Measure.withDensity_apply`.
- Intended proof route: compare measurable rectangles; expand the left
  composition product into a set integral under the weighted base; move the
  density into the integrand; expand the right weighted composition product;
  integrate the history-only density over the kernel coordinate.
- Regularity contracts: measurable history/environment spaces; s-finite base
  measure; Markov kernel; measurable density; finite weighted base measure for
  product-measure extensionality.
- Current ABRL task:
  `LOCAL-LEAF-TS-ALGORITHM-DENSITY-POSTERIOR-INVARIANCE`
- Status: locally-compiled
- Failure signal: do not assume posterior invariance directly; first verify
  that the same density weights both the history marginal and joint law. For
  non-finite weighted bases, replace finite rectangle extensionality with an
  appropriate s-finite uniqueness route before proposing this exact statement
  upstream.

## MEASURE-COMP-WITHDENSITY-HISTORY

- Proposed name: `Measure.comp_withDensity_of_right_constant`
- Mathematical area: kernel composition and density-weighted measures
- Intended Mathlib namespace: `MeasureTheory.Measure`
- Exact statement: composing `kernel.withDensity (fun _ y => density y)` over
  any base measure equals `(kernel ∘ₘ base).withDensity density` when the
  kernel is s-finite and the density is measurable.
- Required imports: `Mathlib.Probability.Kernel.WithDensity` and kernel/measure
  composition integrals.
- Local APIs: `Measure.bind_apply`, `Kernel.withDensity_apply'`,
  `Measure.lintegral_bind`, `MeasureTheory.withDensity_apply`, and
  `MeasureTheory.lintegral_indicator`.
- Intended proof route: extensionality on measurable sets, expand bind and
  with-density evaluations, then commute the indicator-weighted lintegral
  through bind.
- Regularity contracts: measurable spaces, s-finite kernel, measurable output
  density; no finiteness assumption on the base measure.
- Current ABRL task: `LOCAL-LEAF-TS-CONDITIONAL-HISTORY-DENSITY-SOURCE`
- Status: locally-compiled as `Thompson.comp_withDensity_history`.
- Failure signal: keep the density independent of the kernel input; the fully
  input-dependent statement is `Measure.compProd_withDensity`, not this lemma.

## MEASURE-MAP-SWAP-WITHDENSITY-SND

- Proposed name: `Measure.map_swap_withDensity_snd`
- Mathematical area: measure maps and density-weighted product measures
- Intended Mathlib namespace: `MeasureTheory.Measure`
- Exact statement: mapping a joint measure weighted by `density ∘ Prod.snd`
  through `Prod.swap` equals the swapped measure weighted by
  `density ∘ Prod.fst`.
- Required imports: `Mathlib.MeasureTheory.Integral.Lebesgue.Map`.
- Local APIs: `Measure.map_apply`, `MeasureTheory.withDensity_apply`, and
  `MeasureTheory.setLIntegral_map`.
- Intended proof route: extensionality on measurable sets, expand map and both
  density evaluations, then use the set-lintegral map theorem.
- Regularity contracts: measurable product spaces and measurable density.
- Current ABRL task: `LOCAL-LEAF-TS-CONDITIONAL-HISTORY-DENSITY-SOURCE`
- Status: locally-compiled as `Thompson.map_swap_withDensity_snd`.
- Failure signal: audit coordinate order and use `Prod.swap`; do not rewrite the
  joint law by an unproved pair-map identity.

## CONDDISTRIB-CONDEXPKERNEL-MAP-TRIM-COUNTABLE

- Proposed name: `condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim`
- Mathematical area: probability kernels and conditional distributions
- Intended Mathlib namespace: `ProbabilityTheory`
- Exact statement: for measurable `X : Omega -> Target` and
  `Y : Omega -> Condition`, with countable measurable-singleton standard-Borel
  `Target`, if `condDistrib X Y mu = kernel` almost everywhere under
  `mu.map Y`, then `Measure.map X (condExpKernel mu (comap Y) omega) =
  kernel (Y omega)` almost everywhere under `mu.trim hY.comap_le`.
- Required imports: `Mathlib.Probability.Kernel.Condexp`,
  `Mathlib.Probability.Kernel.CondDistrib`, and
  `Mathlib.MeasureTheory.Measure.Trim`
- Local APIs: `condExpKernel_map_eq_of_condDistrib_ae_eq_countable`,
  `ProbabilityTheory.measurable_condExpKernel`, `Kernel.measurable_coe`,
  `Kernel.map_apply`, `Measure.ext_of_singleton`, and
  `MeasureTheory.ae_eq_trim_of_measurable`
- Intended proof route: obtain ordinary a.e. singleton equalities from the
  existing countable-target bridge; prove both singleton probability functions
  measurable in `mCondition.comap Y`; transfer those scalar equalities to the
  trim with `ae_eq_trim_of_measurable`; reconstruct measure equality by
  countable singleton extensionality.
- Regularity contracts: finite `mu`; standard Borel and nonempty `Omega`;
  countable, measurable-singleton, standard-Borel and nonempty `Target`;
  measurable `X` and `Y`.
- Current ABRL task:
  `LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-TRIM-SELECTED-SOURCE`
- Status: locally-compiled
- Failure signal: do not replace the measurable-scalar transfer with a generic
  converse to `ae_of_ae_trim`; such a converse is unavailable and unsound for
  arbitrary predicates.

## CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER

- Proposed name: `hasCondSubgaussianMGF_of_condExpKernel_map_eq`
- Mathematical area: conditional probability kernels and sub-Gaussian moments
- Intended Mathlib namespace: `ProbabilityTheory`
- Exact statement: if measurable `X : Omega -> Real` pushes each conditional
  kernel `condExpKernel mu mcond omega` to a target law trim-a.e., and the
  target identity variable is sub-Gaussian with a common proxy `c` trim-a.e.,
  then `HasCondSubgaussianMGF mcond hm X c mu`, with no separate ambient
  exponential-integrability premise.
- Required imports: `Mathlib.Probability.Moments.SubGaussian`,
  `Mathlib.Probability.Kernel.Condexp`, and kernel composition integrals
- Local APIs: `Measure.integrable_comp_iff`,
  `StronglyMeasurable.integral_kernel`, `Integrable.of_bound`,
  `HasSubgaussianMGF.id_map_iff`, `Kernel.HasSubgaussianMGF.of_rat`, and
  `mgf_nonneg`
- Intended proof route: transfer each target witness back through `Measure.map`;
  use its local exponential integrability for the first Fubini condition; bound
  the measurable inner norm integral by the common MGF ceiling over the finite
  trim measure; construct the kernel MGF witness with `of_rat`.
- Regularity contracts: finite ambient measure, standard Borel sample space,
  `mcond <= mOmega`, measurable `X`, trim-a.e. pushforward equality, and a
  common target sub-Gaussian proxy.
- Current ABRL task:
  `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER`
- Status: locally-compiled
- Failure signal: do not use the implicit `Measure.integrable_comp_iff`
  elaboration when source and target share the same carrier with different
  measurable spaces; instantiate `mcond` and `mOmega` explicitly.  Pointwise
  integrability without the common MGF bound is insufficient.

## FIXED-MGF-DETERMINISTIC-COMPENSATION

- Proposed name: `HasMGFUpperBoundAt.compensated`.
- Mathematical area: exponential moments and supermartingale increments.
- Intended namespace: a future Mathlib fixed-tilt MGF namespace; the current
  structure is ABRL-local.
- Exact statement: from `HasMGFUpperBoundAt X t psi mu`, derive
  `HasMGFUpperBoundAt (fun omega => t * X omega - psi) 1 0 mu`.
- Required import: `Mathlib.Probability.Moments.SubGaussian` through the local
  fixed-MGF layer.
- Local APIs: exponential add/sub identities, constant-multiple integrability,
  `integral_mul_const`, and the existing MGF upper bound.
- Proof route: factor every exponential integrability target into the constant
  `exp(-s*psi)` times the original exponential at tilt `s*t`; for the MGF,
  multiply `mgf X mu t <= exp psi` by `exp(-psi)`.
- Regularity contracts: exactly those stored by `HasMGFUpperBoundAt`; no new
  finite-measure, boundedness, measurability, or sign premise.
- Current ABRL task:
  `LOCAL-LEAF-EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-TAIL`.
- Status: locally compiled; project-local candidate because Mathlib has no
  corresponding fixed-tilt structure in this checkout.
- Failure signal: this lemma compensates only a deterministic scalar budget.
  A random predictable budget must first be frozen inside each conditional
  kernel, as done by the generated mixed-square transport; do not apply the
  scalar lemma directly to a random function.

## TRAJMEASURE-MAP-EVAL-ZERO

- Proposed name: `Kernel.trajMeasure_map_eval_zero`
- Mathematical area: Ionescu-Tulcea trajectory measures
- Intended Mathlib namespace: `ProbabilityTheory.Kernel`
- Exact statement: pushing `Kernel.trajMeasure mu0 kernel` forward by the
  zeroth coordinate evaluation returns `mu0`.
- Required imports: `Mathlib.Probability.Kernel.IonescuTulcea.Traj` and
  `Mathlib.Probability.Kernel.Composition.MapComap`.
- Local APIs: `Kernel.traj_map_frestrictLe`, `Kernel.partialTraj_self`,
  `Kernel.id_map`, `Measure.deterministic_comp_eq_map`, `Measure.map_map`, and
  `MeasurableEquiv.piUnique`.
- Intended proof route: factor coordinate-zero evaluation through
  `frestrictLe 0`, reduce the trajectory kernel to `partialTraj 0 0 = id`, and
  cancel the `piUnique` initial-history equivalence.
- Regularity contracts: measurable coordinate family, initial probability
  measure, and a Markov kernel family.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: do not replace the coordinate marginal proof by an assumed
  definitional equality; `trajMeasure` starts from a mapped singleton prefix
  and requires the explicit `piUnique` cancellation.

## TRAJMEASURE-FINITE-PREFIX-CONGR

- Proposed names: `Kernel.partialTraj_zero_congr` and
  `Kernel.trajMeasure_map_frestrictLe_congr`.
- Mathematical area: Ionescu-Tulcea trajectory kernels and finite-dimensional
  laws.
- Intended Mathlib namespace: `ProbabilityTheory.Kernel`.
- Exact statement: `partialTraj kappa 0 n = partialTraj eta 0 n` whenever
  `kappa k = eta k` for every `k < n`; consequently, equal initial measures
  and step kernels through `n - 1` give equal `frestrictLe n` marginals of the
  two `trajMeasure` laws.
- Required imports: `Mathlib.Probability.Kernel.IonescuTulcea.Traj`.
- Local APIs: `Kernel.partialTraj_succ_of_le`,
  `Kernel.traj_map_frestrictLe`, and `Measure.map_comp`.
- Intended proof route: induct on the endpoint using the recursive
  `partialTraj_succ_of_le` equation, then unfold `trajMeasure`, push
  `frestrictLe` through measure-kernel composition, and rewrite both infinite
  trajectory kernels to the equal partial trajectories.
- Regularity contracts: a measurable coordinate family, probability initial
  measures, and two Markov step-kernel families.  Only step equalities with
  indices strictly below the requested endpoint are used.
- Current ABRL task: `LOCAL-LEAF-TSALLIS-SCHEDULED-IID-MEAN-GAP-REGRET`.
- Status: locally-compiled in `BanditRLProof.KernelTrajectoryPrefix`;
  Mathlib-candidate.
- Failure signal: do not require equality of all future kernels or equality of
  complete infinite trajectory laws.  The finite marginal is deliberately
  insensitive to steps at and after the endpoint.

## REWARDTRACE-PREFIX-MAP-EQ-TRAJMEASURE-OF-CONDDISTRIB

- Proposed name: `Kernel.trajMeasure_prefix_map_eq_of_condDistrib`
- Mathematical area: regular conditional distributions and Ionescu-Tulcea
  finite-dimensional laws
- Intended Mathlib namespace: `ProbabilityTheory.Kernel`
- Exact statement: for a coordinate-measurable external sequence, if the
  zeroth marginal equals `mu0` and the conditional distribution of coordinate
  `i+1` given `frestrictLe i` equals `kernel i` for every `i < n`, then its
  pushforward by `frestrictLe n` equals the corresponding pushforward of
  `Kernel.trajMeasure mu0 kernel`.
- Required imports: `Mathlib.Probability.Kernel.CondDistrib` and
  `Mathlib.Probability.Kernel.IonescuTulcea.Traj`.
- Local APIs: `ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd`,
  `ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`,
  `RewardKernel.trajMeasure_map_eval_zero`, `IicProdIoc`,
  `MeasurableEquiv.piSingleton`, and `Measure.map_map`.
- Intended proof route: induct on `n`; convert the successor conditional law
  to the joint `(prefix,next)` law; rewrite the canonical joint law by the
  trajMeasure compProd recurrence; measurably glue the singleton next
  coordinate onto the existing prefix.
- Regularity contracts: finite external measure, probability initial measure,
  coordinate measurability, nonempty standard Borel coordinate target, and a
  Markov kernel family. Only conditional laws with `i < n` are used.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: do not infer a prefix law from one-step marginals alone.
  The induction needs conditional laws a.e. under the actual prefix
  pushforward, and the canonical side must use the explicit trajMeasure
  compProd recurrence rather than an assumed full-trajectory equality.

## REWARDTRACE-MAP-EQ-TRAJMEASURE-OF-CONDDISTRIB

- Proposed name: `Kernel.trajMeasure_map_eq_of_condDistrib`
- Mathematical area: regular conditional distributions, finite-dimensional
  laws, and Ionescu-Tulcea uniqueness
- Intended Mathlib namespace: `ProbabilityTheory.Kernel`
- Exact statement: a coordinate-measurable external sequence with initial law
  `mu0` and successor conditional kernels `kernel i` has complete pushforward
  law `Kernel.trajMeasure mu0 kernel`; two such processes are therefore
  `IdentDistrib`.
- Required imports: `Mathlib.Probability.Process.FiniteDimensionalLaws` and
  `Mathlib.Probability.Kernel.IonescuTulcea.Traj`.
- Local APIs: `RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`,
  `Finset.sup`, `Finset.measurable_restrict`,
  `MeasureTheory.IsProjectiveLimit.unique`, and `Measure.map_map`.
- Intended proof route: for each finite coordinate set `I`, map the law of the
  enclosing prefix `Finset.Iic (I.sup id)` through the measurable restriction
  to `I`; both complete measures are then projective limits of the same finite
  marginals, so uniqueness identifies them.
- Regularity contracts: finite external measure, probability initial measure,
  coordinate measurability, nonempty standard-Borel coordinate target, and a
  Markov successor-kernel family.
- Current ABRL task:
  `LOCAL-LEAF-UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: equality of one-dimensional marginals is insufficient. The
  proof requires all finite-prefix laws or equivalent successor conditional
  laws, and full-law equality must be discharged through projective-limit
  uniqueness rather than assumed from prefix notation.

## CONDDISTRIB-CONST-OF-COMPOSITION

- Proposed names: `condDistrib_ae_eq_const_of_comp` and
  `map_eq_of_condDistrib_ae_eq_const`
- Mathematical area: regular conditional distributions and independence
- Intended Mathlib namespace: `ProbabilityTheory`
- Exact statements: a constant conditional target law given `fine` remains
  constant given `project ∘ fine`; under a probability source, a constant
  conditional target law also determines the target marginal.
- Required imports: `Mathlib.Probability.Kernel.CondDistrib`,
  `Mathlib.Probability.Kernel.Composition.MeasureCompProd`, and
  `Mathlib.MeasureTheory.Measure.Prod`.
- Local APIs: `condDistrib_ae_eq_iff_measure_eq_compProd`,
  `Measure.compProd_const`, `Measure.map_prod_map`,
  `Measure.snd_map_prodMk`, and `Measure.snd_prod`.
- Intended proof route: rewrite the fine conditional law as a product joint
  law and map by `(project, id)`; for the marginal result, take the `snd`
  pushforward of the defining joint-law equality.
- Regularity contracts: finite source measure for coarsening, probability
  source for marginal extraction, probability constant target law, measurable
  fine/target/project maps, and a nonempty standard Borel target. No injective
  projection is required.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: the kernel must be constant at the fine-conditioning level;
  an action-dependent kernel cannot be coarsened by this lemma without a prior
  a.e. kernel reduction.

## CONDDISTRIB-CONST-OF-AE-EQ-SELECTED

- Proposed name: `condDistrib_ae_eq_const_of_ae_eq_selected`
- Mathematical area: regular conditional distributions and measurable kernels
- Intended Mathlib namespace: `ProbabilityTheory`
- Exact statement: if a conditional kernel is pointwise selected by a
  measurable function of the conditioning value, and that selector is almost
  surely constant under the source process, then the conditional distribution
  is a.e. the corresponding constant kernel.
- Required imports: `Mathlib.Probability.Kernel.CondDistrib` and
  `Mathlib.MeasureTheory.Measure.Map`.
- Local APIs: `ae_map_iff`, `measurableSet_eq_fun`, `Filter.EventuallyEq`, and
  `Kernel.const_apply`.
- Intended proof route: push the selector equality through `Measure.map fine`,
  then combine it pointwise with the given conditional-kernel equality and
  selector-kernel identity.
- Regularity contracts: finite source measure, measurable fine variable and
  selector, measurable equality on the selector target, and nonempty standard
  Borel conditional target. No probability or injectivity assumption is used.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: an unconditional selector marginal is insufficient; the
  selector itself must be a.e. constant on the source process.

## HASCONDSUBGAUSSIANMGF-MEASURABLESPACE-EQ

- Proposed name: `HasCondSubgaussianMGF.of_measurableSpace_eq`
- Mathematical area: conditional sub-Gaussian moments
- Intended Mathlib namespace: `ProbabilityTheory.HasCondSubgaussianMGF`
- Exact statement: if two conditioning measurable spaces are equal, a
  `HasCondSubgaussianMGF` witness for one transports to the other, independently
  of the chosen proofs that each is below the ambient measurable space.
- Required import: `Mathlib.Probability.Moments.SubGaussian`.
- Local APIs: equality elimination and proof irrelevance for the two
  sub-sigma-algebra witnesses.
- Intended proof route: substitute the second measurable space and close the
  residual proof argument by `simpa only`.
- Regularity contracts: standard Borel ambient sample space, finite measure,
  both conditioning spaces below the ambient measurable space.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT`
- Status: locally-compiled; Mathlib-candidate
- Failure signal: ordinary `rw` is insufficient because
  `HasCondSubgaussianMGF` depends on the proof `m <= mOmega`; use the explicit
  transport theorem rather than unfolding conditional kernels.

## HISTORYFILTRATIONSUCC-ACTION-PREFIX-EQ

- Proposed name: project-local `historyFiltrationSucc_eq_of_action_eq_on_prefix`
- Mathematical area: generated filtrations and finite histories
- Intended namespace: `BanditRLProof.History`; upstream candidacy depends on a
  Mathlib finite-history filtration abstraction matching this local definition.
- Exact statement: shifted action/reward history filtrations at time `n` agree
  when the reward process is shared and both action processes agree at every
  coordinate through `n`.
- Required imports: `Mathlib.Probability.Process.Filtration` and the local
  finite-pair-history comap characterization.
- Local APIs: `historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`,
  `finitePairHistoryOfTrace_apply`, and `Finset.mem_Iic`.
- Intended proof route: rewrite both filtrations as comaps of finite pair
  histories, prove the two prefix maps equal coordinatewise, then use comap
  congruence.
- Regularity contracts: countable action and reward spaces with measurable
  singletons, measurable action and reward coordinates, and pointwise action
  equality through the requested index.
- Current ABRL task:
  `LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT`
- Status: locally-compiled; project-local
- Failure signal: equality only after the exploration horizon is insufficient;
  every action coordinate in `Finset.Iic n` must be identified.
## CONDDISTRIB-SPLIT-COMPPROD

- Proposed names: `pair_map_eq_compProd_of_map_eq_of_condDistrib` and
  `condDistrib_pair_ae_eq_compProd_of_split`.
- Mathematical area: regular conditional distributions and kernel products.
- Intended namespace: `ProbabilityTheory`; currently local under
  `BanditRLProof.RewardKernel`.
- Exact statement: an action marginal plus feedback conditional law determine
  the pair pushforward; action conditional law given history plus feedback law
  given `(history, action)` determine the pair conditional law via
  `Kernel.compProd`.
- Required imports: Mathlib `Probability.Kernel.CondDistrib` and
  `Probability.Kernel.Composition.CompProd`.
- Proof route: apply `condDistrib_ae_eq_iff_measure_eq_compProd` to each split
  law and use `Measure.compProd_assoc'` after mapping by `prodAssoc`.
- Regularity: finite source measure, measurable coordinates, standard-Borel
  nonempty action/feedback targets, finite/Markov kernels as appropriate.
- Current ABRL task: `LOCAL-LEAF-UCB-ISALGENVSEQ-SPLIT-LAWS-LML-REGRET`.
- Status: locally compiled; Mathlib-candidate.
- Failure signal: if triple-law reassociation fails, audit the orientation of
  `MeasurableEquiv.prodAssoc`; do not add independence.

## CONDDISTRIB-ID-FST-COMPPROD

- Proposed name: `condDistrib_id_fst_compProd_ae_eq_kernelWithInput`.
- Mathematical area: regular conditional distributions and composition-product
  measures.
- Intended namespace: `ProbabilityTheory`; currently local under
  `BanditRLProof.Thompson`.
- Exact statement: for a finite input measure and a Markov kernel, the regular
  conditional law of the full `(input, output)` sample given its first
  coordinate under `prior compProd kernel` is almost everywhere the kernel
  value with that input retained.
- Required imports: Mathlib `Probability.Kernel.CondDistrib` and
  `Probability.Kernel.Composition.MeasureCompProd`.
- Local APIs: `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`,
  `Measure.compProd_assoc`, `Measure.map_compProd`, and `Kernel.fst_compProd`.
- Proof route: define the retained-input kernel, prove its pointwise apply
  formula, reassociate the prior/kernel/Dirac joint law, and invoke conditional
  distribution uniqueness.
- Regularity: finite input measure; Standard Borel nonempty input and output;
  Markov kernel. No probability normalization or independence is needed.
- Current ABRL task:
  `LOCAL-LEAF-TS-CANONICAL-TRAJECTORY-KERNEL-PROB-MATCH`.
- Status: locally compiled; Mathlib-candidate.
- Failure signal: this theorem disintegrates a supplied measurable kernel; it
  does not prove that a parameterized family of trajectory measures forms a
  kernel. ABRL now handles that construction locally with Mathlib `Kernel.traj`;
  the remaining candidate is the observable shifted conditional-law transport
  described below.

## TRAJ-PROJECTED-SHIFTED-CONDDISTRIB

- Proposed shape: identify the conditional law of the next coordinate of a
  measurable projection of `Kernel.traj`, conditioned on the projected finite
  prefix, when an auxiliary retained coordinate is deterministic from that
  prefix.
- Mathematical area: Ionescu-Tulcea kernels, regular conditional
  distributions, measurable maps, and conditioning coarsening.
- Intended namespace: `ProbabilityTheory.Kernel`; the ABRL specialization now
  compiles, while extraction of a generic theorem remains optional.
- Required imports: Mathlib Ionescu-Tulcea `Traj`, `CondDistrib`, kernel
  map/comap, and finite-prefix restriction measurability.
- Local APIs: `Thompson.retainEnvironmentKernel`,
  `Thompson.canonicalMeasurableEnvironmentStepKernel`,
  `Thompson.measurableEnvironmentPairTrace`, and
  `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`.
- Proof route used locally: prove fixed-environment support with
  `traj_map_updateFinset`; reconstruct the projected prefix/next joint law using
  `partialTraj_compProd_eq_map_traj`, `Measure.compProd_map/congr`, and
  `map_compProd_comap_history`; then apply `condDistrib` uniqueness. This avoids
  a standalone conditioning-coarsening theorem.
- Regularity: Standard Borel nonempty state/observable spaces, Markov step
  kernels, measurable projection, and deterministic recoverability of the
  retained coordinate under a fixed input kernel value.
- Current ABRL task:
  `LOCAL-LEAF-TS-MEASURABLE-ENVIRONMENT-TRAJECTORY-KERNEL`.
- Status: fixed-input ABRL specialization compiled as
  `Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ`;
  generic Mathlib extraction not attempted.
- Failure signal: a generic submission should preserve the joint-law proof and
  state explicit recoverability/support hypotheses; do not add independence or
  assume full trajectory equality.

## TRAJECTORY-MIXTURE-COMMON-CONDDISTRIB

- Proposed shape: if every value of an environment-indexed Markov trajectory
  kernel has history/action joint law `trajectory(env).map history compProd
  policy` for one common history-indexed policy, then mixing those trajectories
  against any finite prior has the same policy as the conditional action law
  given history.
- Mathematical area: kernel mixtures, composition products, regular
  conditional distributions, and measurable pushforwards.
- Intended namespace: `ProbabilityTheory`; the ABRL specialization is
  `Thompson.trajectoryMixture_map_history_action_eq_compProd` together with
  `Thompson.trajectoryMixture_condDistrib_action`.
- Required imports: Mathlib MeasureCompProd and CondDistrib.
- Proof route used locally: extensionality on measurable rectangles; expand
  both composition products; apply the pointwise joint law; use
  `setLIntegral_map` inside each kernel value and
  `Measure.setLIntegral_compProd` to exchange the prior mixture with the common
  policy integral; invoke CondDistrib uniqueness.
- Regularity: finite prior, Markov trajectory and policy kernels, measurable
  history/action maps, and Standard Borel nonempty action for the conditional
  distribution form. No independence assumption is used.
- Current ABRL task:
  `LOCAL-LEAF-TS-GLOBAL-RECURSIVE-SAMPLER-COUPLING`.
- Status: project-local generic theorem and actual-trajectory Thompson consumer
  compile; upstream Mathlib extraction remains optional.
- Failure signal: the policy must be common across mixture inputs. If it depends
  on the latent environment, conditioning only on visible history generally
  changes the kernel; do not hide that dependency or assert a false mixture
  law.

## CONDDISTRIB-HISTORY-ACTION-SCORE-INTEGRAL

- Proposed shape: if two action variables have the same regular conditional
  distribution given one history variable, then every measurable real-valued
  history/action score has the same integral under the two history/action joint
  laws.
- Mathematical area: regular conditional distributions, composition-product
  measures, measurable pushforwards, and Bochner integration.
- Intended namespace: `ProbabilityTheory`; the current project-local theorem is
  `Thompson.integral_historyAction_eq_of_condDistrib_ae_eq`.
- Required imports: Mathlib CondDistrib, MeasureCompProd, and Bochner integral
  map APIs.
- Local APIs: `compProd_map_condDistrib`, `Measure.compProd_congr`,
  `integral_map`, and `Thompson.integral_comp_eq_of_map_eq`.
- Proof route used locally: express each history/action pushforward as the
  history marginal composed with its conditional-action kernel; use the a.e.
  kernel equality to identify the composition products; map both joint laws by
  the measurable score and conclude equality of integrals.
- Regularity: finite source measure; measurable history and both action maps;
  Standard Borel nonempty action; measurable real-valued score. No
  integrability assumption is needed for equality of the extended Bochner
  integrals as used by this wrapper.
- Current ABRL task: `LOCAL-LEAF-TS-BAYES-REGRET-DECOMPOSITION`.
- Status: project-local generic theorem and actual recursive Thompson consumer
  compile; upstream Mathlib extraction remains optional.
- Failure signal: equality must be for conditional action laws given the same
  history marginal and the score must depend only on visible history and the
  candidate action. Do not smuggle the latent environment into the score or
  infer an unconditional joint-law equality that the conditioning hypothesis
  does not support.

## CONDEXPKERNEL-MAP-MEASURABLE-DIRAC

- Proposed name: `condExpKernel_map_eq_deterministic_of_measurable`
- Mathematical area: conditional expectation kernels
- Intended Mathlib namespace: `ProbabilityTheory`
- Exact statement: if `m <= mOmega` and `X : Omega -> Target` is measurable
  from `m`, then `(condExpKernel mu m).map X` is `mu.trim hm`-a.e.
  `Kernel.deterministic X hX`; equivalently each pushforward is
  `Measure.dirac (X omega)`.
- Required imports: `Mathlib.Probability.Kernel.Condexp` and
  `Mathlib.Probability.Kernel.CompProdEqIff`.
- Proof route: map `compProd_trim_condExpKernel` through `X`, rewrite the
  deterministic composition-product and both iterated maps, then apply
  `Kernel.ae_eq_of_compProd_eq`.
- Regularity: finite `mu`, Standard Borel ambient space, countably generated
  target, and conditioning-space measurability of `X`; no target countability
  or singleton measurability.
- Current ABRL task:
  `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE`.
- Status: locally compiled with kernel and Dirac canaries.
- Failure signal: this is a frozen-visible-state law only; it does not identify
  any next-step conditional distribution or imply a conditional MGF.

## FINITE-ARM-IID-REWARD-VECTOR-MEAN

- Proposed name: no new upstream theorem; keep the ABRL wrapper
  `iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap` project-local.
- Mathematical area: finite product probability measures and Bochner means.
- Intended Mathlib namespace: existing `MeasureTheory` APIs are sufficient.
- Exact statement: for probability laws indexed by `Fin K`, rewards supported
  a.e. in `[0,1]`, and supplied coordinate means, the clipped selected-loss
  difference under `Measure.pi` equals the corresponding finite-bandit gap.
- Required imports: `Mathlib.MeasureTheory.Integral.Pi`.
- Local APIs: `Measure.pi`, `MeasureTheory.integral_comp_eval`,
  `Integrable.of_bound`, `FiniteBanditModel.bestMean`, and
  `FiniteBanditModel.gap`.
- Intended proof route: use pointwise clipping for global boundedness, remove
  clipping by a.e. congruence, apply the existing coordinate-integral theorem,
  and finish by the model-gap definition.
- Regularity contracts: probability coordinate laws, a.e. unit-interval
  support, exact coordinate integrals, and finite arm index. No new generic
  Pi-measure lemma is required.
- Current ABRL task:
  `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-REWARD-LAW-REGRET`.
- Status: locally compiled as a thin project-specific wrapper; not proposed
  upstream because Mathlib already provides the generic product-integral API.
- Failure signal: do not use an a.e. support assumption to claim the raw
  evaluator is pointwise bounded on the entire product state space; clipping
  or a bounded subtype is required by the abstract loss-vector constructor.

## STATIONARY-IID-CLIPPED-GAP-DEVIATION

- Proposed name: no new upstream theorem; keep
  `abs_iidLossStateMeanGap_stationaryCorrupted_sub_modelGap_le` project-local.
- Mathematical area: clipped probability means and finite-arm gap transport.
- Intended Mathlib namespace: existing `Set` and `MeasureTheory` APIs suffice.
- Exact statement: adding a fixed real shift to each `[0,1]` reward and
  projecting back to `[0,1]` changes the arm-versus-best mean loss gap by at
  most `abs shift_arm + abs shift_best`.
- Required imports: `Mathlib.Topology.UnitInterval` and the Bochner integral
  basics already imported by the IID reward-law module.
- Local APIs: `Set.projIcc`, `Set.abs_projIcc_sub_projIcc`,
  `norm_integral_le_of_norm_le_const`, `integral_sub`, and the uncorrupted
  finite-arm IID model-gap theorem.
- Intended proof route: apply projection contraction pointwise, use the
  triangle inequality for the two affected arms, and integrate the bounded
  loss-gap difference under the product probability law.
- Regularity contracts: probability arm laws, raw rewards a.e. in `[0,1]`, and
  exact baseline means. The shift is fixed and arm-dependent.
- Current ABRL task:
  `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-STATIONARY-CORRUPTED-REWARD-LAW-REGRET`.
- Status: locally compiled as a project-specific model bridge; no missing
  generic Mathlib result was found.
- Failure signal: this contraction does not establish a prefix law for
  time-varying or history-adaptive shifts; those require a separate process
  and conditional-mean transport rather than a stronger projection lemma.

## TIME-VARYING-IID-LOSS-STATE-PREFIX-LAW

- Proposed name: no new upstream theorem; keep the time-indexed trajectory
  wrappers project-local.
- Mathematical area: infinite-product independence and finite Ionescu-Tulcea
  prefix laws.
- Exact statement: a deterministic evaluator `value t state action` on fresh
  IID state coordinates induces a generated trajectory whose visible prefix
  through `n` depends only on state coordinates through `n`; the current loss
  gap is independent of the pre-action trace and has its coordinate-law mean.
- Existing Mathlib/local APIs are sufficient:
  `iIndepFun_rewardTrace_infinitePi`, `Measure.compProd_map`,
  `Measure.fst_compProd`, `Measure.infinitePi_map_eval`, and the local
  `KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr`.
- Regularity: Standard Borel state/action, measurable action singletons,
  probability coordinate law, and per-time jointly measurable bounded
  evaluators.
- Current ABRL tasks:
  `LOCAL-LEAF-TSALLIS-SCHEDULED-IID-TIME-VARYING-MEAN-GAP` and
  `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-TIME-VARYING-CORRUPTED-REWARD-LAW-REGRET`.
- Status: locally compiled; no missing generic Mathlib lemma was found.
- Failure signal: the theorem assumes a deterministic time index and common
  coordinate law. History-dependent shifts require conditional-kernel
  measurability and cannot be obtained by strengthening product independence.

## HISTORY-ADAPTIVE-IID-STATE-PREFIX-LAW

- Proposed name: keep `HasIIDStateCoordinateLocality` and its scheduled
  trajectory wrappers project-local.
- Mathematical area: Ionescu-Tulcea finite-prefix laws for predictable
  history-dependent evaluators on IID state streams.
- Exact statement: if initial loss reads state coordinate `0` and successor
  `n` reads state coordinate `n+1` while depending measurably on the supplied
  pre-action finite history, then the visible trajectory through `n` depends
  only on state coordinates through `n`.
- Existing APIs are sufficient: local trajectory-prefix congruence,
  `Kernel.map`, `Kernel.comap`, `Preorder.frestrictLe`, and finite prefix
  extension.
- Regularity: Standard Borel state/action, measurable singletons, bounded
  measurable predictable loss, explicit coordinate locality.
- Current ABRL tasks:
  `LOCAL-LEAF-TSALLIS-SCHEDULED-IID-HISTORY-ADAPTIVE-PREFIX` and its
  finite-arm history-adaptive corruption consumer.
- Status: locally compiled; no missing generic Mathlib theorem found. The
  abstraction is tied to ABRL's trajectory API and is not currently an
  upstream candidate.
- Failure signal: future-state dependence invalidates prefix locality;
  conditional reward-law questions are separate from pathwise factorization.

## TSALLIS-TERMINAL-SELF-BOUNDING-INTERPOLATION

- Proposed name: keep `regret_le_selfBoundingInterpolation` project-local.
- Mathematical area: ordered real algebra for self-bounding online regret.
- Exact statement: for `lambda in [0,1]`, `regret <= upper` and
  `gapMass-C <= regret` imply
  `regret <= (1+lambda)*upper-lambda*gapMass+lambda*C`.
- Existing Mathlib APIs are sufficient: `mul_le_mul_of_nonneg_left`,
  `sub_le_sub`, `Set.Icc`, `linarith`, and `ring`.
- Local consumer: the generated scheduled half-Tsallis expected-probability
  upper bound in `TsallisScheduledSuboptimalExpectedBound`.
- Regularity: only `0 <= lambda` is algebraically needed; the local public
  theorem retains `lambda <= 1` to match the paper route.
- Status: locally compiled and not an upstream candidate because it is a
  short domain-specific composition lemma.
- Failure signal: this lemma does not prove the simplex-constrained quadratic
  maximization or any optimized logarithmic/square-root corruption bound.

## TSALLIS-CONSTRAINED-QUADRATIC-OPTIMIZATION

- Proposed names: keep `sum_linear_sub_quadratic_le_unconstrained` and
  `sum_linear_sub_quadratic_le_of_sum_le` project-local.
- Mathematical area: finite ordered-field quadratic optimization and simplex
  square-root mass.
- Exact route: complete squares coordinatewise; for the active branch shift
  the common linear coefficient to `2*M/sum(1/c_i)`; use
  `Real.sum_sqrt_mul_sqrt_le` to obtain the finite-simplex mass constraint.
- Existing Mathlib APIs are sufficient: finite-sum distributivity,
  `Real.sq_sqrt`, positivity/order lemmas, `field_simp`, `ring`, and
  `Real.sum_sqrt_mul_sqrt_le`.
- Regularity: every quadratic coefficient is strictly positive. The Tsallis
  specialization exposes this as `0<lambda` and positive suboptimal gaps; the
  active reciprocal sum additionally uses a nonempty suboptimal set.
- Status: locally compiled, root imported, and externally canaried. This is
  domain-specific route glue rather than a current upstream candidate.
- Failure signal: no across-time threshold sum or joint `lambda` optimization
  is proved here; the final square-root corruption endpoint remains open.

## TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-OPTIMIZATION

- Proposed names: keep the generated-regret and schedule-specific wrappers
  project-local; the generic shifted inverse-square-root and harmonic-tail
  inequalities may be reusable but are not proposed upstream in this batch.
- Mathematical area: finite sums, monotone integral comparison, real square
  roots and logarithms, and constrained quadratic online-learning bounds.
- Exact route: split finite times at the active quadratic threshold; obtain a
  prefix from one cutoff certificate; use `sum 1/sqrt(t+1)<=2*sqrt(n)` and
  `sum_(t=m)^(n-1) 1/(t+1)<=log(n/m)`; substitute into the refined generated
  half-Tsallis self-bound.
- Existing Mathlib APIs are sufficient: `Finset.filter`, `Finset.range`,
  `Finset.Ico`, `AntitoneOn.sum_le_integral_Ico`, `integral_inv`,
  `Real.sq_sqrt`, ordered-field algebra, and finite-sum distributivity.
- Regularity: the logarithmic tail needs `0<m<=n`; the generated endpoint
  additionally requires positive gaps, `lambda in (0,1]`, a nonempty
  suboptimal set, a positive cutoff bounded by the horizon, its explicit
  threshold, and the terminal self-bound.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried. The paper card is retrieval evidence only.
- Failure signal: no theorem yet constructs the discrete near-optimal cutoff
  or performs the joint `lambda`/corruption optimization; the final
  Masoudian--Seldin square-root corruption bound remains open.

## TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-FLOOR-TUNING

- Proposed names: the natural-floor sandwich may remain project-local; the
  generated tuning theorems are domain-specific and are not upstream
  candidates.
- Mathematical area: floor semirings, finite sums, real square roots and logs,
  and scalar online-learning optimization.
- Exact route: for `q>=1`, prove `0<floor(q)` and
  `floor(q)<=q<=2*floor(q)`; instantiate
  `q=(A*R/(2*sqrt(K-1)))^2`; transport the factor-two loss into the logarithmic
  tail; specialize `lambda=1` and prove `q=25*S^2/(K-1)`.
- Existing Mathlib APIs are sufficient for the discrete branch:
  `Nat.floor_pos`, `Nat.floor_le`, `Nat.lt_floor_add_one`,
  `Real.sqrt_sq_eq_abs`, `Real.log_le_log`, and ordered-field tactics.
- Regularity: a nonempty suboptimal arm set, positive gaps, the generated
  terminal self-bound, and `1<=q<=T+1`; the generic fixed-lambda theorem also
  requires `lambda in (0,1]`.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried. The `lambda=1` general corruption theorem is closed.
- Failure signal: pinned Mathlib has no Lambert W implementation. The refined
  `sqrt(C)` theorem needs either a formal `W_-1` branch plus the paper's bounds,
  or an equivalent convex-root existence/estimate theorem over the stated
  corruption interval.

## TSALLIS-SELF-BOUNDING-BETA-ROOT

- Proposed names: the beta equation and its bandit-specific root wrapper remain
  project-local; the underlying IVT is already in Mathlib.
- Mathematical area: real logarithms, ordered fields, continuity, and the
  intermediate value theorem.
- Exact route: prove `g(1)<=0` and `0<=g(scale/S^2)` from the two corruption
  inequalities, restrict `Real.continuousOn_log` to `[1,scale/S^2]`, and apply
  `intermediate_value_Icc`.
- Regularity: `0<scale`, `0<S`, `1<=scale/S^2`, `C*S<=scale`, and
  `S*(log(scale/S^2)+1)<=C`.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried. No new generic Mathlib theorem was needed.
- Downstream status: the coefficient-aware local route now supplies the needed
  quantitative estimate and alpha/lambda transport in a separate leaf. The
  paper equation remains useful retrieval evidence and is not silently changed.

## TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-TUNING

- Proposed names: the corrected beta equation, alpha/lambda change of variables,
  and bandit regret wrappers remain project-local; no new generic Mathlib API is
  proposed.
- Mathematical area: real logarithms and square roots, IVT, ordered-field
  algebra, finite reciprocal-gap sums, and generated measure-kernel regret.
- Exact route: derive `g(beta)=C*S/scale*beta-log(beta)-2` from the compiled
  coefficient-five floor theorem, find beta in `[2,scale/(25*S^2)]`, prove
  `(sqrt(w)-1)^2<=w-log(w)-1`, transport through alpha/lambda, rewrite the
  threshold as `2*(T+1)/beta`, and compose the generated regret bound.
- Regularity: positive scale, reciprocal-gap sum, and corruption; explicit
  scalar-window inequalities; finite supported arms with positive suboptimal
  gaps; generated Standard Borel/probability contracts; terminal self-bound.
- Retrieval evidence: the paper beta-root card, Mathlib IVT/log/sqrt/order APIs,
  the compiled floor-tuning leaf, and the Masoudian--Seldin paper route.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; generated explicit local `sqrt(C*S)` endpoint closed.
- Downstream consumer: the finite-arm IID history-adaptive corruption model now
  discharges the terminal self-bound and trajectory-law transport using its
  deterministic envelope budget.
- Failure policy: do not identify this coefficient-aware endpoint with the
  paper's ideal constants or infer complementary regimes, stronger corruption
  models, nonuniform concrete-envelope proofs, or the complete Tsallis-INF
  theorem; one uniform downstream family is recorded separately below.

## TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-WINDOW

- Proposed names: `RefinedLocalCorruptionWindow` and its bandit scalar
  conversion remain project-local; they are not generic Mathlib candidates.
- Mathematical area: positive division, finite-sum order, real logarithms,
  squares, and elementary ordered-field inequalities.
- Exact route: use `25*S^2<=k*(T+1)` for the beta lower endpoint, derive
  `k<=25*S^2` from `1<=k<=S`, use `C*S<=k*(T+1)` for the corruption upper
  bound, and derive `C>0` from the logarithmic lower bound.
- Regularity: `1<=k`, positive horizon mass and reciprocal-gap sum, `k<=S`,
  and the named three-part window; no probability contract is involved.
- Retrieval evidence: refined tuning, Mathlib log/division/order APIs, and the
  Masoudian--Seldin route.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; all four low-level contracts and positivity are derived.
- Failure policy: one uniform suboptimal-arm boost now proves this window
  downstream; its complement and other concrete envelopes remain open.

## TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-REFINED-CORRUPTED-REWARD-LAW-REGRET

- Proposed names: both public theorems are ABRL model/algorithm compositions;
  no generic Mathlib candidate is introduced.
- Mathematical area: product measures, Ionescu-Tulcea trajectory kernels,
  independence/expected-gap transport, finite sums, and real log/sqrt tuning.
- Exact route: expose the concrete history-adaptive envelope self-bound, then
  instantiate the compiled coefficient-aware generated theorem with the model
  gap sum and source-derived corruption budget.
- Regularity: probability arm laws, a.e. unit reward support, exact means,
  nonempty suboptimal arms, gaps in `(0,1]`, measurable shifts with a
  deterministic envelope, finite horizon, and the compact corruption window.
- Retrieval evidence: the two parent local leaves, Mathlib measure/kernel/
  independence APIs, and the two Tsallis-INF paper routes.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried. Law transport and model-level refined composition are closed.
- Failure policy: uniform, arm-dependent stationary, and deterministic
  time-varying suboptimal-arm boosts now compile downstream; genuinely random
  history-adaptive envelopes, current-action or latent-law corruption,
  expectation-only budgets, and the complete paper theorem remain outside this
  statement.

## TSALLIS-FINITE-ARM-IID-UNIFORM-SUBOPTIMAL-BOOST-REFINED-REGRET

- Proposed names: the source, exact-budget theorem, concrete-window producer,
  and final regret theorem are ABRL-specific; no generic Mathlib candidate is
  introduced.
- Mathematical area: finite/countable measurability, erased finite-arm sums,
  deterministic envelope budgets, and ordered-field transport.
- Exact route: leave the best arm unchanged, boost every other arm by
  nonnegative `epsilon`, prove the envelope sum is exactly
  `(T+1)*k*epsilon`, derive the compact upper clause from `epsilon*S<=1`, and
  invoke the compiled history-adaptive `_of_window` theorem.
- Regularity: probability arm laws, a.e. unit reward support, exact means,
  nonempty suboptimal arms, gaps in `(0,1]`, nonnegative `epsilon`, finite
  horizon, and the three explicit refined-window clauses.
- Retrieval evidence: the refined history-adaptive and scalar-window local
  leaves, Mathlib `measurable_of_countable`, finite-sum/order and
  measure/kernel/independence APIs, and both Tsallis-INF paper routes.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; exact budget, refined branch, and all-regimes endpoint are closed.
- All-regimes route: a named scalar regime selects the refined bound; its
  complement automatically reuses the logarithmic `+C` theorem, so no window
  proof is required by the total theorem and zero/small corruption is covered.
- Failure policy: arm-dependent stationary and deterministic time-varying
  boosts compile downstream; random history-adaptive envelopes, current-action
  or latent-law corruption, expectation-only budgets, paper-sharp constants,
  and the complete Tsallis-INF theorem remain outside this statement.

## TSALLIS-FINITE-ARM-IID-ARM-DEPENDENT-SUBOPTIMAL-BOOST-ALL-REGIMES

- Proposed names: the arm-dependent source, exact-budget theorem, named regime,
  compact-window transport, total bound, and final regret theorem are
  ABRL-specific; no generic Mathlib candidate is introduced.
- Mathematical area: countable measurability, erased finite-arm sums, constant
  finite time sums, deterministic corruption budgets, and ordered-field
  transport.
- Exact route: force the best-arm shift to zero, assign each other arm its own
  nonnegative `boost`, prove the exact budget
  `(T+1) * sum_(a != best) boost(a)`, transport the named scalar regime to the
  compact refined window, and split internally between the refined `_of_window`
  theorem and the logarithmic `+C` theorem.
- Regularity: probability arm laws, a.e. unit reward support, exact means,
  nonempty suboptimal arms, gaps in `(0,1]`, pointwise nonnegative boost, finite
  horizon, and no caller-supplied window proof.
- Retrieval evidence: compiled history-adaptive logarithmic/refined leaves, the
  uniform consumer's finite-sum route, Mathlib `measurable_of_countable`, finite
  sum/order and measure/kernel/independence APIs, and both Tsallis-INF paper
  cards.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; exact budget and the all-regimes endpoint are closed.
- Failure policy: deterministic time-varying, previous-action-gated, and
  general measurable history-arm-gated sources compile downstream;
  current-action or latent-law corruption, expectation-only budgets,
  paper-sharp constants, and the complete Tsallis-INF theorem remain outside
  this statement.

## TSALLIS-FINITE-ARM-IID-TIME-VARYING-SUBOPTIMAL-BOOST-ALL-REGIMES

- Proposed names: the time-varying source, exact double-sum budget, named
  regime, compact-window transport, total bound, and final regret theorem are
  ABRL-specific; no generic Mathlib candidate is introduced.
- Mathematical area: countable measurability, erased finite-arm sums, finite
  time sums, deterministic corruption budgets, and ordered-real transport.
- Exact route: use `boost 0` initially and `boost (n+1)` after a length-`n`
  pre-action history, force the best-arm shift to zero, prove
  `C=sum_(t<T+1)sum_(a!=best) boost(t,a)`, transport the named regime to the
  compact window, and split internally between the refined `_of_window` and
  logarithmic `+C` theorems.
- Regularity: probability arm laws, a.e. unit reward support, exact means,
  nonempty suboptimal arms, gaps in `(0,1]`, pointwise nonnegative deterministic
  schedule, finite horizon, and no caller-supplied window proof.
- Retrieval evidence: the compiled history-adaptive logarithmic/refined route,
  the stationary arm-dependent consumer, Mathlib `measurable_of_countable`,
  finite sum/order and measure/kernel/independence APIs, and both Tsallis-INF
  paper cards.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; the exact double-sum budget and all-regimes endpoint are closed.
- Failure policy: previous-action and general measurable history-arm-gated
  adaptive sources compile downstream; current-action or latent-law corruption,
  expectation-only budgets, paper-sharp constants, and the complete Tsallis-INF
  theorem remain outside this statement.

## TSALLIS-FINITE-ARM-IID-PREVIOUS-ACTION-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES

- Proposed names: the previous-action-gated source, exact source-budget theorem,
  refined-window transport, and final regret theorem are ABRL-specific; no
  generic Mathlib candidate is introduced.
- Mathematical area: finite-product measurability, measurable equality events,
  piecewise measurable functions, deterministic finite-sum envelopes, and
  model-level regret composition.
- Exact route: at successor time `n+1`, evaluate action coordinate `n` of the
  finite pair history, activate `boost(n+1,a)` exactly on equality with a fixed
  trigger arm, force the best-arm shift to zero, prove domination by the full
  deterministic schedule, rewrite its exact double finite-sum budget, and split
  between the refined and logarithmic parent theorems.
- Regularity: fixed trigger arm, pointwise nonnegative deterministic schedule,
  probability arm laws, a.e. unit reward support, exact means, nonempty
  suboptimal arms, gaps in `(0,1]`, finite horizon, and no caller measurability
  or window proof.
- Retrieval evidence: the compiled time-varying all-regimes consumer and
  history-adaptive refined/logarithmic route; Mathlib `measurable_pi_apply`,
  `measurableSet_eq_fun`, `Measurable.ite`, finite sums, measure/kernel and
  independence APIs; both Tsallis-INF paper cards.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; action-history dependence, exact envelope budget, and the
  all-regimes endpoint are closed for this source.
- Failure policy: arbitrary measurable finite-history-and-arm gates compile
  downstream; current-action or latent-law corruption, expectation-only
  budgets, paper-sharp constants, and the complete Tsallis-INF theorem remain
  outside this statement.

## TSALLIS-FINITE-ARM-IID-MEASURABLE-HISTORY-ARM-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES

- Proposed names: the measurable history-arm-gated source, exact source-budget
  theorem, refined-window transport, and final regret theorem are ABRL-specific;
  no generic Mathlib candidate is introduced.
- Mathematical area: measurable sets on finite dependent products, piecewise
  measurable functions, countable finite-arm functions, deterministic
  finite-sum envelopes, and model-level regret composition.
- Exact route: accept an arbitrary `initialGate : Set (Fin K)` plus
  `gate n : Set (History.FinitePairHistory (Fin K) Real n × Fin K)` with
  `MeasurableSet (gate n)`; gate time zero and each successor source; force the
  best-arm shift to zero; prove domination by the full deterministic schedule;
  rewrite the exact double finite-sum budget; and split between the refined and
  logarithmic parent theorems.
- Regularity: arbitrary initial arm gate, all-time jointly measurable successor
  history-arm gates, all-time pointwise nonnegative deterministic schedule,
  probability arm laws, a.e. unit reward support, exact means, nonempty
  suboptimal arms, gaps in `(0,1]`, finite horizon, and no caller source-
  measurability or window proof. Classical membership decision is local to the
  noncomputable source definition; the finite initial arm gate needs no extra
  measurability premise.
- Retrieval evidence: the compiled previous-action and time-varying all-regimes
  consumers and history-adaptive refined/logarithmic route; Mathlib
  `MeasurableSet`, `Measurable.ite`, `measurableSet_eq_fun`,
  `measurable_of_countable`, finite sums, measure/kernel and independence APIs;
  both Tsallis-INF paper cards.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried; arbitrary initial arm gates and measurable predictable action or
  past observed clipped-feedback/loss-coordinate successor gates, exact
  deterministic envelope budget, and all-regimes regret are closed. Current,
  raw, and latent reward-vector coordinates are not exposed by this history.
- Failure policy: the budget is the full deterministic envelope, not realized
  or expected gate-open mass. Horizon-local-only contracts and `K=1` are not
  covered. Current-action/nonpredictable gates, random or expectation-only
  envelopes, raw/latent-law corruption, paper-sharp constants, and the complete
  Tsallis-INF theorem remain outside this statement.

## FIXED-ARM-LATENT-FINITE-PREFIX-PRODUCT

- Proposed name: keep
  `UCB.armStreamMeasure_map_fixedArmFinitePrefix_eq_pi` and its trajectory
  wrapper project-local.
- Mathematical area: infinite product measures, finite coordinate products,
  and latent reward streams.
- Exact statement: mapping the stationary arm-stream measure to the first `m`
  coordinates of one fixed arm gives `Measure.pi (fun _ : Fin m => nu arm)`;
  the same equality holds after lifting through the exact stream marginal of
  the latent arm-stream trajectory coupling.
- Existing APIs are sufficient:
  `ProbabilityTheory.iIndepFun.precomp`,
  `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`,
  `UCB.iIndepFun_armStreamMeasure_coordinate`,
  `UCB.armStreamMeasure_map_coord`, and
  `Thompson.identDistrib_fst_latentArmStreamTrajectoryMeasure`.
- Regularity contracts: a Markov arm kernel; a nonzero finite arm count for the
  trajectory lift; and only ordinary measurable-space structure on the frozen
  environment.  No boundedness, moment, stopping-time, or action-policy premise
  is used.
- Current ABRL task:
  `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`.
- Status: locally compiled, root imported, declaration-indexed, and externally
  canaried.  The source-specific consumer identifies each finite nth optimal
  pull with its corresponding latent coordinate almost surely.
- Failure signal: this finite product law concerns latent coordinates.  It does
  not identify the coupling's visible trajectory marginal with the native
  fixed-IID SGB trajectory, and it does not imply that totalized stopped values
  or values conditioned on all requested pulls occurring are IID.

## COUNTABLE-BRANCH-SELECTED-REWARD-FRESHNESS

- Proposed names: keep the SGB branch aggregation and selected-reward
  conditional laws project-local; no new upstream Mathlib candidate is needed.
- Mathematical area: countable measurable partitions, restricted measures,
  semidirect products, measure-valued kernels, and regular conditional laws.
- Exact statement: under the latent arm-stream trajectory coupling, the joint
  law of the visible history through `n`, the selected action at `n+1`, and the
  actual reward at `n+1` factors as the visible history/action marginal followed
  by `nu` at that selected arm.  The same statement holds after projecting to
  the visible-trajectory marginal.
- Existing APIs are sufficient: the compiled branchwise complement-coordinate
  product law, `Measure.compProd_restrict_prod`, `Measure.restrict_map`,
  `Measure.map_sum`, `Measure.compProd_sum_left`,
  `Measure.compProd_sum_right`, `Measure.compProd_congr`,
  `Measure.compProd_const`, `Measure.compProd_map`, and
  `condDistrib_ae_eq_iff_measure_eq_compProd`.
- Regularity contracts: a Standard Borel frozen environment, a nonzero finite
  arm count, and a Markov arm kernel.  The countable branch type is
  `Nat × Fin K`; restricted branch kernels are finite/sub-Markov and are not
  normalized probability kernels.
- Current ABRL task:
  `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`.
- Status: locally compiled and canaried.  The main endpoints are
  `latentArmStreamVisibleNextReward_joint_eq_compProd` and
  `latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu`.
- Failure signal: deterministic-time one-step conditional freshness does not
  identify the visible marginal with the native fixed-IID trajectory, prove a
  stopped or pull-ordered selected-IID law, or establish a future/no-return
  cylinder probability.
