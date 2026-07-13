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
