# Stage Thompson sampling Bayesian regret

Task id: `BRL-TS-BAYES-001`
Kind: `theoremFormalization`
Status: `activePort`
Harness: `hierarchical`

## Goal

Maintain a proof-DAG and memory route for Thompson sampling posterior action
identity and Bayesian regret, with LML theorem cards as the first source.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declarations: `Bandits.TS.hasCondDistrib_action`, `Bandits.integral_regret_le`
- Local surfaces: `BanditRLProof/Algorithms/Thompson.lean`,
  `BanditRLProof/Algorithms/ThompsonCanonicalSampler.lean`,
  `BanditRLProof/Algorithms/ThompsonReferencePolicy.lean`,
  `BanditRLProof/Algorithms/ThompsonAlgorithmDensity.lean`,
  `BanditRLProof/Algorithms/ThompsonAlgorithmDensityProcess.lean`,
  `BanditRLProof/Algorithms/ThompsonCanonicalTrajectory.lean`,
  `BanditRLProof/Algorithms/ThompsonMeasurableTrajectory.lean`,
  `BanditRLProof/Algorithms/ThompsonRecursiveSampler.lean`,
  `BanditRLProof/Algorithms/ThompsonBayesRegretDecomposition.lean`,
  `BanditRLProof/Algorithms/ThompsonClippedUCBScore.lean`,
  `BanditRLProof/Algorithms/ThompsonStationaryReward.lean`
- Textbook/source cards: `TXT-SLIVKINS-2019-2024`, `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-POSTERIOR`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.Thompson.obligationNames
-- BanditRLProof.Thompson.BayesianPosteriorActionSource
-- BanditRLProof.Thompson.condDistrib_action_ae_eq_bestAction_of_posteriorMap
-- BanditRLProof.PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq
-- BanditRLProof.Thompson.condDistrib_action_ae_eq_bestAction_of_bayesianPairMap
-- BanditRLProof.Thompson.canonicalSampler_condDistrib_action_ae_eq_bestAction
-- BanditRLProof.Thompson.referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
-- BanditRLProof.Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
-- BanditRLProof.Thompson.referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource
-- BanditRLProof.Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_algorithmDensitySource
-- BanditRLProof.Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_canonicalTrajectoryKernels
-- BanditRLProof.Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_measurableEnvironment_stepCondDistrib
-- BanditRLProof.Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_measurableEnvironment
-- BanditRLProof.Thompson.referencePosteriorHistoryAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
-- BanditRLProof.Thompson.uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
-- BanditRLProof.Thompson.uniformReferenceThompsonAlgorithm_integral_historyScore_eq_bestAction
-- BanditRLProof.Thompson.integral_trajectoryBayesMeanRegret_eq_add_historyScore
-- BanditRLProof.Thompson.integral_trajectoryBayesMeanRegret_eq_add_clippedUCB
-- BanditRLProof.Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le
```

## Proof Obligations

- [x] Record posterior best-action distribution assumptions and the measurable
  posterior pushforward action kernel.
- [x] Compile the Mathlib `condDistrib` posterior-action transport interface.
- [x] Compile the pinned-LML-shaped clipped-UCB score, finite-history/trace
  transport, measurable `[l,u]` bounds, and concrete decomposition with all
  four integrability families discharged.
- [x] Record bounded/sub-Gaussian stationary environment assumptions in the
  compiled theorem signatures and local retrieval cards.
- [x] Keep the pinned LML declaration as a theorem card while porting its
  conditional-law transport route locally.
- [x] Construct a concrete canonical prior-likelihood posterior identity
  producer from an environment/history pair pushforward law.
- [x] Construct the reference-posterior action policy and the actual one-step
  sampler, including its action conditional law and posterior preservation.
- [x] Prove reference-versus-actual posterior invariance from matching
  history-marginal and history/environment-joint density laws, and consume it
  in the finite-pair reference-policy sampler.
- [x] Construct both density pushforward laws from equal environment marginals
  plus one conditional-history density law, and expose a finite-pair consumer.
- [x] Assemble the conditional process source from the four initial/successor
  action/feedback split-law families and expose its finite-prefix consumer.
- [x] Prove those four split-law families for the canonical fixed-environment
  recursive TS/reference trajectory laws, transport them through supplied
  measurable environment-indexed trajectory kernels, and expose the
  finite-prefix probability-matching endpoint.
- [x] Construct the measurable environment-indexed actual/reference trajectory
  kernel families from measurable feedback-environment data.
- [x] Identify the shifted successor pair conditional laws of those generated
  kernels from Mathlib `Kernel.traj` after dropping the retained environment and
  dummy initial state.
- [x] Construct the next-action conditional law and probability-matching theorem
  for the canonical one-step Thompson sampler.
- [x] Couple the finite-pair per-time posterior policies into one non-circular
  recursive TS trace, using a fixed uniform reference trajectory; prove
  probability matching for that same trace's successor action coordinate and
  discharge finite-action policy absolute continuity internally.
- [x] Lift actual-trajectory probability matching, including the initial
  action, to arbitrary measurable finite-history action scores and compile the
  LML-shaped finite-horizon Bayesian mean-regret decomposition with explicit
  integrability contracts.
- [x] Prove deterministic latent-stream support for the canonical trajectory
  and fixed-environment upper/lower fixed-arm adaptive-count tails on the
  actual augmented trajectory.
- [x] Mix those pointwise tails through the augmented prior, remove the
  zero-pull fiber, and derive fixed-arm lower/upper clipped empirical-mean
  confidence failures on the decomposition-facing canonical measure.
- [x] Convert the compiled fixed-arm failures into exact count-collapsed
  horizon events and both clipped-score expectation bounds.
- [x] Join the decomposition and both expectation bounds, then specialize
  `delta = 1 / n^2` to the pinned stationary Bayesian-regret constant.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-TS-BAYES-001.md`.  Generic integral, measurability,
conditional-distribution, and algebra leaves should be Mathlib candidates when
stated cleanly. The project-local posterior-action `condDistrib` transport and
canonical Mathlib posterior producer, canonical one-step sampler, and
reference-posterior finite-prefix policy sampler, the measure-theoretic
algorithm-density posterior-invariance consumer, and the conditional-history
density source constructor now compile, while the actual LML declaration
remains theorem-card-only. The recursive finite-history process theorem now
also compiles from split initial/successor laws and pointwise policy absolute
continuity. Its environment-parameterized transport through regular
conditional sample laws and the resulting finite-prefix Thompson
probability-matching consumer now compile as well. The split-source layer now
also compiles: it gathers the four `IsAlgEnvSeq`-shaped law families with
`ae_all_iff`, assembles each conditional process, and invokes that consumer.
The canonical fixed-environment `trajMeasure` producer, its combined and split
process laws, the `prior compProd trajectoryKernel` full-sample disintegration,
and the finite-prefix probability-matching endpoint now compile. A jointly
measurable feedback-environment contract and Mathlib `Kernel.traj` now also
construct the actual/reference `Env -> PairTrace` Markov kernels. The initial
pair laws, projected shifted successor `condDistrib` laws, pointwise canonical
trajectory equalities, and finite-prefix probability matching all compile
without supplied trajectory kernels or process-law premises. The global
coupling now also compiles: a generic mixture theorem transports the common
history/action policy through the prior, the Thompson `HistoryAlgorithm` is
defined from one fixed uniform-reference posterior, and uniform full support
discharges every finite-action density obligation. The actual successor action
of the same canonical trajectory satisfies probability matching. `TS-DECOMP`
now also compiles: the initial and successor score laws are unified, arbitrary
measurable finite-history scores have matching selected/best-action
expectations, and finite-horizon Bayesian mean regret splits into the two
upstream confidence terms. `TS-CLIPPED-UCB-SCORE` is now compiled downstream:
the exact pinned score is measurable on inclusive finite histories, lies in
`[l,u]`, agrees with the trace score at `n+1`, and yields
`integral_trajectoryBayesMeanRegret_eq_add_clippedUCB` with no explicit
integrability premises. `TS-STATIONARY-ARM-STREAM-ADAPTER` now also compiles:
it constructs the stationary feedback adapter, represents each fixed
environment by the canonical independent arm-stream law, proves upper/lower
  adaptive-count tails for arbitrary action traces, and exposes the same table
  through measurable next-unused deterministic feedback.
  `TS-LATENT-ARM-STREAM-DETERMINISTIC-TRAJECTORY-SUPPORT` now compiles too: the
  canonical trajectory reward trace equals `rewardFromArmStream` almost
  everywhere, generic `IdentDistrib` wrappers admit independent algorithmic
  randomness, and the stationary environment-indexed augmented trajectory
  kernel satisfies fixed-arm upper/lower reward-sum tails. The augmented prior
  mixture, exact count-collapsed horizon events, both clipped-UCB expectations,
  and their decomposition join now compile. The final stationary theorem
  specializes `delta = 1 / n^2` and proves
  `(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)`. `TS-FINAL` is therefore closed
  for this stationary Markov reward-kernel model. Literal LML symbol import,
  nonstationary/contextual Thompson models, and RL routes remain separate;
  future failures must be isolated in explicit model adapters rather than
  weakening or relabeling this theorem.

## Build Gate

```bash
python3 tools/bandit.py check
```
