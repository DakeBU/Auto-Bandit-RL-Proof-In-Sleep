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

## Review Rule

Before adding tactic work, the candidate must name local APIs and an intended
proof route.  If repeated attempts fail, record whether the likely issue is a
false statement, missing assumption, wrong abstraction, unavailable API, or
counterexample.  Do not repeatedly rewrite the proof route without that audit.

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
