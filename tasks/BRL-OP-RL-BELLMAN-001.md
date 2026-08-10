# Define a finite-horizon RL Bellman and regret interface

Task id: `BRL-OP-RL-BELLMAN-001`
Kind: `openProblemProposal`
Status: `partial`
Harness: `hierarchical`

## Goal

Create a small Lean-facing interface for finite-horizon reinforcement learning:
finite states, finite actions, transition kernel surface, reward model, value
function, Bellman recursion, occupancy, and regret.

## Source

- Literature source: standard finite-horizon MDP/RL notation.
- Local surfaces: `BanditRLProof/RL/FiniteHorizonMDP.lean`,
  `BanditRLProof/RL/FiniteHorizonPolicy.lean`,
  `BanditRLProof/RL/FiniteHorizonTrajectory.lean`,
  `BanditRLProof/OpenProblems.lean`
- Textbook/source card: `TXT-SLIVKINS-2019-2024`
- Scenario card: `SCN-RL-MDP`
- Mathlib cards: `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION`

## Lean Target

```lean
-- compiled first layer:
-- BanditRLProof.FiniteHorizonRL.MDP
-- BanditRLProof.FiniteHorizonRL.MDP.transitionValue
-- BanditRLProof.FiniteHorizonRL.MDP.bellmanQ
-- BanditRLProof.FiniteHorizonRL.MarkovPolicy.valueAt_bellman
-- BanditRLProof.FiniteHorizonRL.MarkovPolicy.trajectoryMeasure
-- BanditRLProof.FiniteHorizonRL.MarkovPolicy.integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero
-- BanditRLProof.FiniteHorizonRL.MDP.optimalValueAt_dominates_and_is_attained
-- future occupancy/regret layer
```

## Proof Obligations

- [x] Decide dependency-light or Mathlib probability layer: use Mathlib Markov
  kernels and Bochner integration.
- [x] Define finite MDP data and its one-step Bellman action-value surface.
- [x] Define a stage-indexed Markov policy, its induced state kernel, and the
  measurable policy Bellman operator.
- [x] Define the finite-horizon policy value and prove its terminal condition
  and chronological Bellman recursion.
- [x] Define the policy trajectory surface and prove its expected cumulative
  reward equals the stage-zero policy value.
- [x] Define optimal value and finite-action Bellman optimality.
- [x] Define regret relative to an optimal policy.

## Compiled Theorem Route: Actual-Sampled Self-Consistent-Budget Realized Successor Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Lean-facing statement: with
  `q=card(State)*uniformFloorTransitionCoordinateRadius*horizon<1`, define
  `T=q*(rewardBound+2*rewardBudget)/(1-q)`. The exact identity
  `q*(rewardBound+2*rewardBudget+T)=T` supplies transition confidence for every
  selected model. Outside one count/reward/return union, all actual sampled
  plans are optimistic and realized successor-average regret is bounded by
  `2*horizon*(rewardBudget+T)+explorationCharge` plus the globally centered
  return radius divided by `episodes*rounds`.
- Local APIs/imports: arbitrary-budget stochastic iid all-coordinate terminal;
  `selfConsistentTransitionBudget`; uniform-floor contraction and fixed-point
  wrappers; finite transition cover; exploratory path-support floor; adaptive
  batch-event transport; sampled cumulative successor exploratory regret;
  exact occupancy evaluator; generic two-budget expected-to-realized transport.
- Proof route: solve the scalar fixed point under `q<1`; dominate the finite
  transition envelope by `q` times its value bound; invoke fixed-policy
  confidence; transport the exact selected-policy iid fibers to all rounds;
  sum recommendation and exploration charges; close the occupancy average;
  combine model and global-return events with three preserved shares.
- Regularity contracts: finite measurable nonempty Standard Borel State/Action
  with equality/singletons; probability initial law; positive rounds, episodes,
  model proxy and return proxy; mean-compatible uniform sub-Gaussian selected
  rewards; valid three shares and exploration; bounded true means; exploratory
  path support/uniform visit floor; strict count margin and strict `q<1`;
  composite stochastic batch/trajectory Standard Borel instances. Actual
  sampled rewards may be unbounded and no adaptive-round independence is used.
- Retrieval evidence: exact route/declaration no-hits; compiled arbitrary-
  budget fixed-policy, adaptive confidence/cumulative, occupancy, and realized
  transport parents; Mathlib finite-sum, measure, kernel, conditional-
  expectation, sub-Gaussian, integral and ordered-field APIs. Scenario/paper
  cards are placement evidence and proof weapons are inspiration only.
- Status: `leanCompiled`; focused foundation/module and root-imported
  `Tests.Basic` builds pass, with scalar fixed-point, occupancy-average, and
  public terminal canaries.
- Failure policy: preserve actual samples, `n -> n+1`, initial exclusion, three
  shares, global centering, and `episodes*rounds`. The route removes the coarse
  fixed budget's forced reward-bound term but does not prove a vanishing rate.
  Next compile one explicit schedule controlling `q`, reward radius, `T`,
  exploration charge, and normalized return radius; do not infer reachability,
  anytime/minimax control, or complete UCB-VI.

## Compiled Theorem Route: Actual-Sampled Explicit-Budget Realized Successor Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-EXPLICIT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Lean-facing statement: each actual sampled plan selects the fixed radius
  `rewardBudget + transitionBudget`; its occupancy cost and the complete
  finite-round sum evaluate exactly. With the current uniform-floor transition
  budget, the same three-share event yields optimism and realized successor-
  average regret at most
  `2*horizon*(rewardBound+3*rewardBudget)+explorationCharge` plus the globally
  centered return radius divided by `episodes*rounds`.
- Local APIs/imports: the compiled actual-sampled realized successor parent;
  `MDP.stochasticAllCoordinateEmpiricalFiniteBatchModel`;
  `FiniteBatchModel.plan`; `EstimatedModelPlan.selectedRadiusRemaining`;
  `MarkovPolicy.occupancySumRemaining_const`;
  `adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum`;
  `uniformFloorStochasticTransitionBudget`; finite sums and ordered-field
  division.
- Proof route: unfold the two fixed radii; replace every selected-radius cost
  by a constant function; evaluate probability occupancy as horizon times that
  constant; sum over `Fin rounds`; use positive rounds to cancel the average;
  expand `transitionBudget=rewardBound+2*rewardBudget`; rewrite the unchanged
  realized theorem by congruence on its planning summand.
- Regularity contracts: the algebraic helpers use finite measurable
  State/Action with equality/singletons, `Nonempty Action`, and a probability
  initial law, while deliberately omitting unnecessary `Nonempty State`. The
  terminal inherits exactly the parent's finite nonempty Standard Borel,
  probability, sub-Gaussian, positivity/share, exploration, bounded-mean,
  path-support, strict-margin, half-contraction and stochastic composite-space
  contracts. Sampled rewards remain unbounded.
- Retrieval evidence: exact route search no-hit; compiled actual-sampled
  realized parent, constant occupancy theorem and fixed-radius stochastic
  empirical model; `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, and `MLIB-ORDER-ALGEBRA`;
  `SCN-RL-MDP`/UCB-VI are placement evidence and proof weapons remain
  inspiration only.
- Status: `leanCompiled`; focused module and root-imported `Tests.Basic`
  compile. External Unit/Bool canaries instantiate the cumulative occupancy
  and positive-round planning-average identities, and expose the full terminal.
- Failure policy: preserve actual samples, sampled coordinate `n` to successor
  batch `n+1`, initial-batch exclusion, three shares, global centering and the
  `episodes*rounds` denominator. The explicit bound contains the irreducible
  term `2*horizon*rewardBound` caused by the coarse transition budget. Next
  prove a self-consistent shrinking budget for contraction `q<1`; do not infer
  vanishing consistency, anytime/minimax control, or complete UCB-VI by merely
  tuning the current fixed-budget schedule.

## Compiled Theorem Route: Actual-Sampled Realized Successor Average Behavior Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Lean-facing statement: outside one union of the sampled empirical-model bad
  event and successor global-return deviation event, every actual sampled plan
  is optimistic and the realized average regret of source successor batches
  `1..rounds` is bounded by the sampled occupancy selected-radius average,
  explicit exploration charge, and globally centered return radius divided by
  `episodes * rounds`.
- Local APIs/imports: sampled successor exploratory expected-regret terminal;
  concrete sampled-source `GlobalReturnMeasurability`;
  `successorGlobalReturnDeviationBadEvent`; successor global-return tail;
  `realizedSuccessorAverageRegret`; exact expected-to-realized decomposition;
  `measure_union_le` and positive division.
- Proof route: infer finite-table global-return measurability; identify source
  successor expected cumulative/average regret with the sampled-plan
  exploratory behavior expression; use the parent count/reward event for
  optimism and expected regret; union it with the return event; apply the
  exact global-return deviation inequality and normalize by positive rounds.
- Regularity contracts: finite measurable nonempty Standard Borel State/Action
  with equality/singletons; probability initial law; positive rounds,
  episodes, reward variance proxy and cumulative successor global-return
  proxy; one mean-compatible uniform sub-Gaussian reward source; separate
  valid count/reward/return deltas; valid exploration; bounded true means;
  path support, strict count margin, and half-contraction. Sampled rewards may
  be unbounded.
- Retrieval evidence: exact route search no-hit; compiled sampled successor
  expected-regret and successor return-tail/decomposition routes;
  `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, and `MLIB-ORDER-ALGEBRA`; theorem cards and
  proof weapons remain evidence/inspiration, not local proofs.
- Status: `leanCompiled`; focused module and external `Tests.Basic` canaries
  compile for the regularity instance, exact source rewrite, and full terminal.
- Failure policy: preserve actual samples, sampled coordinate `n` to successor
  batch `n+1`, initial-batch exclusion, all three failure shares, global
  centering including sampled initial-state policy-value fluctuation, and the
  `episodes * rounds` denominator. The explicit-budget consumer above closes
  the trajectory occupancy term, but this parent alone gives no vanishing
  rate, anytime/minimax result, realized initial-batch control, or complete
  UCB-VI.

## Compiled Theorem Route: Actual-Sampled Successor Exploratory Behavior Expected Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-SUCCESSOR-EXPLORATORY-BEHAVIOR-EXPECTED-REGRET`.
- Lean-facing statement: sampled coordinate `n` determines the concrete source
  successor exploratory policy for coordinate `n + 1`. On the unchanged
  measurable two-share good event, all sampled plans are optimistic and the
  finite sum of those successor policies' expected regrets is bounded by the
  occupancy selected-radius sum plus `rounds` explicit exploration charges.
- Local APIs/imports: cumulative sampled recommendation parent;
  `sampledEmpiricalOptimisticPolicyTable`; `DeterministicMarkovPolicyTable`;
  `successorPolicy`; `Preorder.frestrictLe`;
  `exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge`;
  `exploratoryBehaviorRegretCharge`; finite sums.
- Proof route: identify the sampled table with its plan's optimistic policy;
  identify its exploratory mixture with the actual source successor policy;
  apply the deterministic exploration comparison at every coordinate; collect
  the constant terms with `Finset.sum_add_distrib`; combine with the compiled
  cumulative recommendation/occupancy result and unchanged event.
- Regularity contracts: exactly the parent terminal's finite measurable
  nonempty Standard Borel State/Action, probability, positive rounds/episodes/
  proxy, uniform sub-Gaussian mean-compatible reward, separate confidence
  shares, exploration, bounded-mean, path-support, strict-margin, and half-
  contraction contracts. The algebraic transport only uses valid exploration
  and the mean-reward bound beyond finite spaces and probability.
- Retrieval evidence: exact route search no-hit; compiled cumulative sampled
  recommendation and deterministic exploration-charge routes;
  `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, and
  `MLIB-ORDER-ALGEBRA`; RL/UCB-VI cards are placement evidence and proof
  weapons remain inspiration only.
- Status: `leanCompiled`; the focused module and root-imported `Tests.Basic`
  compile. The external Unit/Bool canary instantiates the cumulative behavior
  assembly, and public checks expose the source alignment and full terminal.
- Failure policy: preserve actual sampled rewards, `n -> n + 1` successor
  indexing, exclusion of the initial policy, separate shares, and one explicit
  charge per selected plan. The three-share realized consumer now compiles
  above. This expected-regret parent alone still does not imply an explicit
  rate, anytime/minimax control, or complete UCB-VI.

## Compiled Theorem Route: Actual-Sampled Cumulative Recommended Expected Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-RECOMMENDED-EXPECTED-REGRET`.
- Lean-facing statement: every actual sampled stochastic batch coordinate
  determines its all-coordinate empirical optimistic plan. On the parent's
  measurable two-share good event, all plans are optimistic and the finite sum
  of their recommended policies' expected regrets is at most the finite sum of
  their occupancy selected-radius certificates.
- Local APIs/imports: the compiled sampled confidence/path-support terminal;
  `sampledEpisodeBatchOfStochasticTrajectories`;
  `stochasticAllCoordinateEmpiricalFiniteBatchModel`; `EstimatedModelPlan`;
  `MarkovPolicy.expectedRegret`; `occupancySumRemaining`;
  `selectedRadiusRemaining`; `Finset.sum_le_sum`.
- Proof route: name the actual-sampled plan at every trajectory coordinate;
  define the recommended-regret and occupancy-radius `Fin` sums; preserve every
  roundwise optimism certificate; sum the pointwise regret inequalities; reuse
  the parent event, tail, exact generating-policy fibers, and explicit
  calibration unchanged.
- Regularity contracts: exactly the parent finite measurable nonempty Standard
  Borel State/Action, probability, positive rounds/episodes/proxy, uniform
  sub-Gaussian mean-compatible reward, separate share, exploration,
  bounded-mean, path-support, strict-margin, and half-contraction contracts.
  The finite-sum helper adds no concentration premise.
- Retrieval evidence: exact route search no-hit; compiled sampled confidence
  parent and deterministic cumulative recommendation pattern;
  `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, and
  `MLIB-ORDER-ALGEBRA`; RL/UCB-VI cards are placement evidence and proof
  weapons remain inspiration only.
- Status: `leanCompiled`; focused source modules and root-imported
  `Tests.Basic` compile. The external canary instantiates the finite-sum
  assembly, the cumulative terminal is root-visible, and the reward-swap
  canary preserves actual sampled-reward dependence.
- Failure policy: preserve actual sampled rewards, one plan per batch,
  generating-policy confidence indexing, exact history fibers, separate
  shares, and recommendation-level semantics. The successor exploratory-policy
  charge now compiles above. Do not infer realized regret, an explicit rate,
  anytime/minimax control, or complete UCB-VI from this parent.

## Compiled Theorem Route: Stochastic-Reward IID Explicit Exploratory Calibration

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EXPLORATORY-PATH-SUPPORT-EXPLICIT-CALIBRATION`.
- Lean-facing target: replace every coordinatewise margin and reward/transition
  cover required by the stochastic sampled-reward empirical-model terminal
  with one common expected-count floor, explicit uniform budgets, and one
  scalar half-contraction; then derive that floor from `ExploratoryPathSupport`
  for a concrete exploratory policy.
- Local APIs/imports: the compiled stochastic iid all-coordinate confidence
  parent, `ExploratoryPathUniformVisitFloor`,
  `DeterministicMarkovPolicyTable.uniformVisitFloor_expectedCount_le`,
  `uniformFloorTransitionCoordinateRadius`,
  `expectedCountTransitionCoordinateRadius_le_uniformFloor`, simultaneous
  reward/count radii, finite constant sums, and ordered Real division.
- Proof route: divide the simultaneous reward-sum radius by
  `episodes * visitFloor - countRadius`; use denominator antitonicity to bound
  every coordinate reward radius; set `transitionBudget` to
  `rewardBound + 2 * rewardBudget`; rewrite the stochastic value envelope as
  `2 * transitionBudget * remaining`; sum the uniform next-state radius and
  apply the half-contraction; construct the exploratory expected-count floor
  from path support and invoke the parent terminal.
- Regularity contracts: finite measurable nonempty State/Action with equality
  and measurable singletons; Standard Borel at the probability terminal;
  probability initial law; deterministic table, exploratory support/rate;
  mean-compatible uniform sub-Gaussian reward source; positive episodes/total
  proxy; separate valid shares; true mean-reward bound; common floor with
  strict scalar margin; and scalar half-contraction. No sampled-reward bound is
  assumed.
- Retrieval evidence: exact local stochastic-confidence and path-support
  calibration parents; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`;
  `SCN-RL-MDP` and `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` place the route;
  `WEAPON-UCB-OPTIMISM` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.
- Current status: `leanCompiled` in
  `FiniteHorizonStochasticRewardIIDExplicitCalibration`. Seven declarations
  expose both uniform budgets, coordinate reward-radius transport, transition
  cover, fixed-policy terminal, and practical path-support terminal. The
  horizon-two Bool/Bool canary uses 4194304 episodes, visit floor `1/8`, a
  proved half-contraction, and nondegenerate symmetric `+/-1` rewards; it
  retains sampled reward `1` while the stored mean is `0`. Placeholder scan is
  clean and four representative axiom audits are baseline-only. Independent
  review found no P0-P2, confirmed the denominator and doubled-envelope
  directions, and its unnecessary helper-regularity P3 is resolved. Focused,
  root, `Tests.Basic`, declaration/index, and full project checks pass.
- Failure policy: preserve the strict positive denominator, separate shares,
  explicit budgets, path-support semantics, fixed-policy iid law, and coarse
  `episodes * varianceProxy` reward tail. The half-contraction is sufficient,
  not minimax. Next prove exact history-selected stochastic batch-law
  transport; do not claim adaptive/cumulative/realized/anytime/minimax or
  complete-UCB-VI results.

## Compiled Theorem Route: Stochastic-Reward IID Empirical-Model Confidence

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-ALL-COORDINATE-EMPIRICAL-MODEL-CONFIDENCE`.
- Lean-facing target: from a finite iid family of complete reward-bearing
  trajectories generated by one fixed Markov policy, construct the actual
  sampled-reward `EpisodeBatch`; expose one measurable finite union bad event;
  bound its mass by separate count/transition and reward shares; and, outside
  that event, build `MDP.FiniteBatchModel.Confidence` together with the existing
  optimism and recommended-policy expected-regret conclusion.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardTrajectory`,
  `FiniteHorizonStochasticRewardIIDTotalReturnConcentration`,
  `FiniteHorizonStochasticRewardIIDEmpiricalRewardConfidence`,
  `FiniteHorizonStochasticRewardIIDAllCoordinateEmpiricalModelConfidence`,
  `FiniteHorizonIIDTrajectoryBatch`,
  `FiniteHorizonIIDCountConcentration`,
  `FiniteHorizonIIDSimultaneousCountConfidence`,
  `FiniteHorizonIIDAllCoordinateFiniteBatchConfidence`,
  `MDP.trajectoryStateAt`, `MDP.EpisodeBatch`,
  `MDP.FiniteBatchModel.Confidence`, finite `Measure.pi`, `iIndepFun`, and the
  local independent sub-Gaussian sum tail theorem.
- Proof route: retain each sampled reward when mapping a stochastic trajectory
  to an empirical episode.  For a fixed stage/state/action coordinate, use the
  visit-masked centered reward
  `1{S_h=s,A_h=a} * (R_h - mdp.reward s a)`.  Transport the selected stage
  reward law from the stochastic trajectory construction, prove one-coordinate
  sub-Gaussian MGF with proxy `varianceProxy`, lift it across iid episodes, and
  apply the existing sum tail theorem with the conservative total proxy
  `episodes * varianceProxy`.  Union these reward events over the finite visit
  coordinates and union once more with `simultaneousCountBadEvent`.  On the
  complement, divide the masked reward sum by the positive realized visit
  count supplied by the count margin, combine transition confidence with a
  reward-budget calibration, and instantiate `FiniteBatchModel.Confidence`.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; Standard Borel State/Action; probability
  initial law; a fixed Markov policy; a mean-compatible reward kernel with one
  uniform selected-reward sub-Gaussian proxy; positive episode count, positive
  variance proxy, and positive count/reward failure shares; explicit expected-
  visit count margins and deterministic reward/transition budget calibration.
  No almost-sure bound on sampled rewards is assumed.
- Retrieval evidence: the compiled iid count modules already provide episode
  independence, count/transition union events, positive-count transport, and
  transition frequency bounds.  The current all-coordinate model theorem uses
  `EpisodeBatch.RewardConsistent`, so it only covers the known-reward
  projection.  The stochastic trajectory modules provide complete
  reward-bearing iid laws and selected-reward conditional sub-Gaussian MGF;
  exact stage-coordinate masking/transport is the first supporting leaf to
  compile.  The RL/UCB-VI cards place the route; theorem cards and proof weapons
  are not local proofs.
- Current status: `leanCompiled`; arbitrary probability mixtures preserve the
  uniform fiberwise reward MGF, stage-coordinate masked deviations recurse
  through the generated stochastic trajectory kernel, finite iid episode sums
  satisfy the conservative `episodes * varianceProxy` two-sided tail, and the
  actual sampled rewards are retained in the generated `EpisodeBatch`. The
  pulled-back count event and finite reward-coordinate union are separately
  measurable and consume `countDelta` and `rewardDelta`; outside their union,
  deterministic positive count margins bound every empirical reward error and
  every transition singleton error. The canonical sampled-reward model has the
  explicit envelope
  `remaining * (rewardBound + 2 * rewardBudget + transitionBudget)`, yields a
  complete `FiniteBatchModel.Confidence`, and exposes global optimism plus the
  recommended-policy one-episode expected-regret bound. Focused module builds,
  root import, and a nondegenerate Bool/Bool external terminal canary pass. The
  canary uses 16384 episodes and symmetric `+/-1` rewards, proves its margins
  and covers internally, distinguishes sampled reward `1` from stored mean
  reward `0`, and invokes the terminal without caller hypotheses. Placeholder
  and representative public-axiom audits pass. Independent review's original
  vacuous-canary P2 is repaired; its source-independent receiver API P3 is
  retained with explicit semantic comments. The declaration/index refresh and
  full repository gate pass.
- Failure policy: preserve the actual sampled rewards, fixed-policy iid law,
  global initial-state mixture, stage/state/action indexing, and separate
  confidence shares.  A coarse `episodes * varianceProxy` reward proxy is
  acceptable, but do not silently replace sampled rewards by stored means,
  assume bounded reward samples, or claim an optimal count-dependent radius.
  If the existing stochastic trajectory API cannot expose the selected stage
  reward law, isolate that exact measurable map/law identity as a compiled
  supporting leaf before retrying concentration.  Do not claim adaptive,
  cumulative, anytime, minimax, realized-regret, or complete UCB-VI results.

## Compiled Theorem Route: Stochastic Common-Space L1 Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: strengthen the compiled stochastic common-space
  `TendstoInMeasure` theorem to integrability of every scheduled realized-
  behavior regret coordinate, convergence of its expected absolute value to
  zero, exact exponent-one `eLpNorm` convergence, and convergence of the named
  `MemLp.toLp` process in the `Lp` topology.
- Local APIs/imports:
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceConsistency`,
  `AdaptiveStochasticEpisodeBatchSource.realizedSuccessorAverageRegret_eq_expected_sub_deviation`,
  `AdaptiveStochasticEpisodeBatchSource.successorGlobalReturnDeviation`,
  the compiled successor conditional sub-Gaussian MGF, exact common-space
  coordinate marginals, `Measure.infinitePi_map_eval`, `integral_map`,
  `integral_mono_ae`, the scaled-MGF first-absolute-moment adapter, `MemLp`,
  `eLpNorm`, `MemLp.toLp`, and `Lp.norm_toLp`.
- Proof route: first prove the selected-policy expected average regret has the
  deterministic `2H` envelope from the stored mean-reward bound.  Obtain a
  square-root first-absolute-moment bound for the globally centered stochastic
  return deviation by evaluating its existing sub-Gaussian MGF at
  `1 / sqrt(proxy)`.  Combine the exact realized-regret decomposition with
  this bound to prove an integrable scheduled coordinate.  Integrate the
  selected-policy expected-regret term using its deterministic mean-reward
  envelope and projected-count bad-event probability; integrate the stochastic
  deviation directly, rather than imposing a false pathwise reward envelope.
  Show the planner, failure, and normalized square-root proxy terms vanish,
  identify exponent-one `eLpNorm` with expected absolute value, and finish in
  `Lp`.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; Standard Borel State/Action; probability
  initial law; positive horizon and base visit floor; exploratory path support
  and uniform visit floor; deterministic reward means bounded by one; one
  mean-compatible reward kernel with a uniform selected-reward sub-Gaussian
  proxy.  No almost-sure bound on sampled rewards is assumed.  Composite batch,
  trajectory, and countable-product Standard Borel instances come from the
  compiled regularity-closed/common-space parents.
- Retrieval evidence: the adjacent deterministic episodewise expected/L1
  modules provide only the integral and `Lp` assembly template; their `2H`
  sampled-path envelope is not valid for stochastic rewards.  The stochastic
  common-space parent provides exact marginals, measurable coordinates, the
  sharp good-event radius, and the vanishing two-share failure budget.  Exact
  Mathlib retrieval found `HasSubgaussianMGF.integrable`, `mgf_le`,
  `ae_eq_zero_of_hasSubgaussianMGF_zero`, and `Real.exp_abs_le`; the local
  scaled-tilt adapter now compiles with the required `sqrt(proxy)` scaling.
  Exact exponent-one `eLpNorm` assembly remains supplied by the adjacent
  deterministic L1 module.  The RL/UCB-VI cards place the route, while proof
  weapons remain inspiration only.
- Current status: `leanCompiled` in
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceL1Consistency`.
  Thirty declarations expose the deterministic mean-regret envelope, cumulative
  successor MGF, integrability, scaled-MGF first-moment bound, count-only common
  bad event, explicit expected-absolute bound and limit, exponent-one `MemLp`
  and `eLpNorm`, named `Lp` process, and terminal L1/TendstoInMeasure package.
- Verification evidence: fresh source and focused dependency builds, external
  Bool/Bool integrability/expected-absolute/MemLp/Lp/TendstoInMeasure canaries,
  clean placeholder scan, and four representative axiom audits containing
  only `propext`, `Classical.choice`, and `Quot.sound`. Independent local review
  found no P0/P1/P2/P3 issue after the canary namespace repair.
- Failure policy: preserve unbounded sampled rewards, global initial-law
  centering, successor indexing, `episodes * rounds` normalization, exact
  schedule marginals, and the parent's two-share in-probability budget. The L1
  expectation proof pays only the count-event share and integrates stochastic
  return deviation from its MGF; do not add a return bad-event share to that
  bound. If the existing
  conditional sub-Gaussian interface cannot be composed into the cumulative
  successor MGF, isolate that exact transport as the blocker.  Do not reuse
  the deterministic reward-consistency `2H` sample-path
  argument, assume bounded reward samples, or claim natural shared-stream,
  pathwise, almost-sure, anytime, reward-mean estimation, minimax, or complete
  UCB-VI consistency.

## Compiled Theorem Route: Stochastic Common-Space In-Probability Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: strengthen the compiled stochastic scheduled-window
  certificate to an absolute realized successor-average regret certificate;
  put one complete stochastic experiment for every schedule index on a
  dependent infinite product; prove exact coordinate marginals, measurable
  regret coordinates, and `TendstoInMeasure ... atTop (fun _ => 0)`.
- Local APIs/imports:
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationRegularityClosedConsistency`,
  `FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceConsistency`,
  `AdaptiveStochasticEpisodeBatchSource.realizedSuccessorAverageRegret_eq_expected_sub_deviation`,
  `MDP.measurable_sampledCumulativeRewardSum`,
  `MarkovPolicy.expectedRegret_nonneg`,
  `successorGlobalReturnDeviationBadEvent`, `Measure.infinitePi`,
  `Measure.infinitePi_map_eval`, `measurePreserving_eval_infinitePi`, and
  `tendstoInMeasure_iff_dist`.
- Proof route: prove stochastic realized-regret measurability and expected-
  regret nonnegativity; outside the existing projected-count/global-return
  union, combine the expected upper bound with the two-sided return-deviation
  event through the exact realized decomposition to control the absolute
  realized regret by the compiled vanishing stochastic envelope. Define the
  schedule-indexed stochastic source and law, couple all laws with
  `Measure.infinitePi`, pull back each finite bad event along evaluation, and
  bound every distance event by that pulled-back bad event. Finish with the
  compiled regret-envelope and failure-budget limits.
- Regularity contracts: finite measurable nonempty State/Action with
  decidable equality and measurable singletons; Standard Borel State/Action;
  probability initial law; positive horizon and base visit floor; exploratory
  path support and uniform visit floor; deterministic reward means bounded by
  one; a mean-compatible reward kernel with one uniform selected-reward
  sub-Gaussian proxy. Composite deterministic/stochastic batch and trajectory
  Borel instances are inferred by the compiled regularity layer. No
  cross-window dependence assumption is needed because the coupling is the
  explicitly independent product of complete finite-window experiments.
- Retrieval evidence: exact memory and local declaration searches for the
  stochastic common-space route returned no hit. The deterministic
  common-space module supplies the product-measure/TendstoInMeasure template;
  the stochastic cumulative module supplies the exact two-sided return event,
  vanishing regret envelope, vanishing two-share failure budget, and regularity-
  closed finite endpoint. `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-ASYMPTOTICS`, and `SCN-RL-MDP` place
  the route; UCB-VI cards and weapons remain placement/inspiration only.
- Current status: `leanCompiled` in
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceConsistency`.
  Seventeen declarations expose the generic absolute adapter, scheduled source
  and laws, independent common measure, exact marginal, measurable process,
  pulled-back bad event, and terminal `TendstoInMeasure` theorem. Root import
  and external Bool/Bool exact-marginal/process/terminal canaries compile.
- Verification evidence: fresh source compilation, focused module and
  `Tests.Basic` builds, declaration retrieval, clean placeholder scan, five
  representative axiom audits containing only `propext`, `Classical.choice`,
  and `Quot.sound`, and independent review. The review's first-pass P1 stale-
  olean parse finding was repaired; the fresh second pass found no remaining
  P0/P1/P2/P3.
- Failure policy: preserve global centering, successor indexing, the two-share
  failure budget, `episodes * rounds` normalization, and exact schedule
  marginals. If absolute control fails, audit expected-regret nonnegativity and
  the strict complement of `radius <= |deviation|`; do not weaken the target to
  a one-sided violation event. The constructed common space is not a natural
  nested causal stream and gives no pathwise, almost-sure, anytime, reward-mean
  estimation, minimax, or complete-UCB-VI theorem.

## Compiled Theorem Route: Regularity-Closed Stochastic Cumulative Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REGULARITY-CLOSED-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: construct the missing Standard Borel instances for the
  product-coordinate `EpisodeStep`, deterministic adaptive batch trajectories,
  and stochastic adaptive batch trajectories; then expose the compiled finite-
  and all-window stochastic realized-behavior consistency endpoints with only
  State/Action Standard Borel assumptions and no caller-supplied composite
  batch or trajectory witnesses.
- Local APIs/imports:
  `FiniteHorizonEpisodeBatchStandardBorel`,
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationConsistency`,
  `EpisodeStep.instMeasurableSpace`, `EpisodeStep.toProdEquiv`,
  `upgradeStandardBorel`, `MeasurableEmbedding.iff_comap_eq`,
  `MeasurableEmbedding.borelSpace`, `Topology.IsInducing.induced`,
  `Equiv.polishSpace_induced`, and `StandardBorelSpace.pi_countable`.
- Proof route: identify `EpisodeStep State Action` with
  `State × Action × Real × State`; install the induced topology, prove the
  coordinate equivalence is a measurable embedding for the existing comap,
  transport Borel and Polish structures, and infer Standard Borel. Let the
  finite `Fin`-indexed batch products and the deterministic `Nat` trajectory
  synthesize automatically, add a stable countable-product instance for
  `Nat → StochasticEpisodeBatch`, and apply the existing finite-window theorem
  at every schedule index.
- Regularity contracts: the `EpisodeStep` instance requires measurable and
  Standard Borel State/Action; the stochastic trajectory instance additionally
  inherits finite State/Action from the finite-horizon batch aliases. The
  theorem wrappers retain finite measurable
  nonempty State/Action with decidable equality and measurable singletons,
  probability initial law, positive horizon/base floor, exploratory path
  support, bounded deterministic means, and a mean-compatible uniform
  sub-Gaussian reward law. Composite deterministic/stochastic batch and
  trajectory Standard Borel witnesses are no longer caller contracts. The
  schedule still changes the sample space at every index.
- Retrieval evidence: exact memory search for the combined Standard Borel route
  returned no hit; local declaration search recovered the conditional-MGF
  consumers that require batch and trajectory Standard Borel instances.
  Exact Mathlib source supplies `upgradeStandardBorel`,
  `StandardBorelSpace.prod`, `StandardBorelSpace.pi_countable`,
  `MeasurableEmbedding.iff_comap_eq`, `MeasurableEmbedding.borelSpace`, and
  `Equiv.polishSpace_induced`. `MLIB-PROBABILITY-KERNEL` and
  `MLIB-CONDITIONAL-EXPECTATION` place the downstream consumers;
  `SCN-RL-MDP` and UCB-VI are placement evidence only, and weapons are
  inspiration only.
- Current status: `leanCompiled` in
  `FiniteHorizonEpisodeBatchStandardBorel` and
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationRegularityClosedConsistency`.
  Three foundation declarations and two theorem wrappers compile. Root imports
  and external Bool/Bool instance, finite-window, and witness-free all-window
  canaries compile.
- Failure policy: preserve the existing finite-window law, named violation set,
  two confidence shares, global centering, successor indexing, and
  `episodes * rounds` normalization. Do not call this a shared-stream,
  convergence-in-probability, almost-sure, anytime, reward-estimation, minimax,
  or complete-UCB-VI result. The closed boundary is only composite Standard
  Borel construction.

## Compiled Theorem Route: Stochastic Cumulative Decaying-Exploration Realized Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: construct the stochastic-reward lift of the cumulative
  empirical-optimistic exploratory source, prove its complete known-reward
  trajectory projection equals the compiled deterministic cumulative source,
  and transport the scheduled count/optimism/expected-behavior certificate to
  a realized successor-average regret certificate. The finite-window failure
  budget and realized bound must both tend to zero along the existing
  decaying-exploration schedule.
- Local APIs/imports:
  `FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticRealizedBehaviorRegret`,
  `FiniteHorizonAdaptiveCumulativeDecayingExplorationBehaviorConsistency`,
  `AdaptiveCumulativeEmpiricalOptimisticSource.successorTable`,
  `measurable_successorTable`, `knownRewardEpisodeBatchTrajectory`,
  `exploratoryIIDStochasticEpisodeBatchKernel`,
  `trajectoryMeasure_expected_to_realized_successor_average_regret_transport_two_delta`,
  `measurable_selectedExploratoryGlobalReturnDeviation`, and the deterministic
  decaying-exploration expected-behavior endpoint.
- Proof route: define the cumulative projected-selector stochastic source;
  identify initial and selected batch pushforwards; prove prefix/next joint-law
  transport and complete trajectory pushforward; pull back the deterministic
  count event; identify stochastic successor expected regret with projected
  cumulative exploratory behavior regret; derive automatic global-return
  measurability from the finite table selector; apply the two-delta stochastic
  expected-to-realized transport; finally normalize the global stochastic
  return proxy and prove the scheduled radius, failure budget, and realized
  certificate tend to zero.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; Standard Borel State/Action and
  caller-supplied deterministic/stochastic batch and trajectory instances for
  every scheduled window; probability initial law; positive horizon and base
  visit floor; exploratory path support; mean-compatible reward kernel with a
  uniform selected-reward sub-Gaussian proxy; deterministic means bounded by
  one. The sample space changes with the schedule index.
- Retrieval evidence: exact route search returned no local hit. Exact compiled
  cumulative selector/decaying expected-behavior, stochastic projection,
  global-return transport, and sub-Gaussian proxy declarations were retrieved.
  Mathlib cards are `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, and `MLIB-ASYMPTOTICS`.
  `SCN-RL-MDP` and `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` are placement evidence;
  `WEAPON-UCB-OPTIMISM` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.
- Current status: `leanCompiled` in
  `FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationConsistency`.
  Thirty-three declarations cover the episode-linear global proxy, normalized
  scheduled radius and scalar limits, cumulative projected-selector source,
  initial/fiber/joint/conditional/complete projection laws, projected count and
  expected-regret transport, named realized violation set, finite-window
  two-share terminal, and all-window paired failure/regret limit. Root import and
  the explicit Bool/Bool endpoint canary compile.
- Failure policy: preserve known-mean projection, global initial-law centering,
  successor coordinates, independent count/return confidence shares, and the
  `episodes * rounds` normalization. Do not reuse the deterministic-reward
  realized theorem as stochastic evidence. Do not infer one common process,
  convergence in probability, almost-sure/anytime control, stochastic reward
  estimation, minimax regret, or complete UCB-VI.

## Compiled Theorem Route: Concrete Stochastic Empirical-Optimistic Realized Behavior Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EMPIRICAL-OPTIMISTIC-REALIZED-BEHAVIOR-REGRET`.
- Lean-facing target: for the projected-selector stochastic empirical-transition
  source, combine the projected count-confidence/optimism event with the global
  stochastic return-deviation event, transport projected recommendation regret
  to the actual exploratory successor policies, and prove a fixed-window
  realized successor-average regret theorem with separate count and return
  confidence shares.
- Local APIs/imports:
  `FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticProjection`,
  `FiniteHorizonAdaptiveStochasticRewardRealizedBehaviorRegret`,
  `FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret`,
  `FiniteHorizonAdaptiveEmpiricalOptimisticOccupancyEnvelope`,
  `GlobalReturnMeasurability`,
  `successorGlobalReturnDeviationBadEvent`,
  `exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge`,
  `adaptiveEmpiricalOptimisticOccupancyRadiusSum_eq`, and
  `realizedSuccessorAverageRegret_eq_expected_sub_deviation`.
- Proof route: generalize the event transport to distinct `countDelta` and
  `returnDelta`; derive dynamic global-return measurability by partitioning over
  the finite optimistic policy-table type; identify every stochastic successor
  policy with the exploratory policy selected from the projected batch; sum the
  per-policy exploration charge; divide by positive rounds; rewrite the fixed
  occupancy-radius sum to `rounds * (horizon * (2 * transitionBonus))`; finally
  apply the two-budget global-return tail and exact realized/expected identity.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; Standard Borel State/Action,
  deterministic `EpisodeBatch`, stochastic batch, and stochastic trajectory at
  the terminal; probability initial law; mean-compatible reward source with a
  uniform selected-reward sub-Gaussian proxy; deterministic mean-reward bound;
  positive rounds, episodes, and total proxy; valid independent count/return
  deltas; exploration-rate and deterministic source-calibration contracts.
- Retrieval evidence: exact route search returned no local hit; exact compiled
  projection, stochastic realized-regret, exploratory behavior-charge, and
  fixed-bonus occupancy declarations were retrieved. Mathlib evidence is
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and
  `MLIB-REAL-LOG-SQRT`; RL/UCB-VI cards are placement evidence only and proof
  weapons remain inspiration only.
- Status: `leanCompiled`; ten declarations through
  `exploratorySource_trajectoryMeasure_projectedAllCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret`,
  root imported, with Unit and positive Bool/Bool two-action calibrated terminal
  canaries using a non-degenerate symmetric stochastic reward source and
  distinct `1/2` and `1/4` confidence shares. The two-action canary locks the
  endpoint's complete result type. Independent review found no P0/P1; its P2
  canary-contract finding was repaired, while the unsynthesized dependent
  `StandardBorelSpace` instances remain an explicit P3 regularity boundary.
- Failure policy: preserve global initial-law centering, successor coordinates
  `1..rounds`, the `episodes * rounds` denominator, separate confidence shares,
  and the explicit exploration charge. This route excludes the initial batch,
  stochastic reward-mean estimation, a vanishing schedule, anytime/common-space
  control, minimax regret, and complete UCB-VI. Do not advertise the stochastic
  trajectory model as fully closed until those dependent Standard Borel
  instances are constructed by a later measurable-space leaf.

## Compiled Theorem Route: Adaptive Stochastic Known-Mean Projection Confidence

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-KNOWN-MEAN-EMPIRICAL-OPTIMISTIC-PROJECTION-CONFIDENCE`.
- Lean-facing target: construct a concrete stochastic-reward lift of the
  exploratory empirical-transition optimistic adaptive source whose policy
  selector reads only the known-reward projection of the observed stochastic
  prefix; prove that the complete stochastic adaptive trajectory maps exactly
  to the existing deterministic `exploratorySource.trajectoryMeasure`; then
  transport the compiled all-coordinate count-confidence, global optimism, and
  recommended-policy expected-regret terminal to the stochastic law.
- Local APIs/imports: `AdaptiveStochasticEpisodeBatchSource`,
  `AdaptiveEpisodeBatchSource`, `AdaptiveEmpiricalOptimisticSource.exploratorySource`,
  `knownRewardEpisodeBatchOfStochasticTrajectories`,
  `iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure`,
  `Kernel.ofFunOfCountable`, `Kernel.comap`, `Measure.compProd`,
  `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`,
  `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`, and
  `exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret`.
- Proof route: define measurable batch, prefix, and complete-trajectory
  known-reward projections; build a table-indexed stochastic iid kernel and
  comap it along the projected latest-batch optimistic selector; prove dynamic
  return measurability by a finite partition over policy tables; map every
  selected stochastic batch kernel to its deterministic counterpart; transport
  prefix/next-batch compProd laws, identify the full projected trajectory by
  regular conditional distributions and projective-limit uniqueness; finally
  pull back the deterministic count event and terminal conclusions.
- Regularity contracts: finite measurable State/Action with decidable equality,
  measurable singletons, and nonempty types; probability initial-state law;
  one mean-compatible stochastic reward source; a Standard Borel and nonempty
  deterministic `EpisodeBatch` at the full-process identification endpoint;
  the inherited positive rounds/episodes, valid delta, deterministic mean-reward
  bound, nonnegative transition bonus, exploration-rate, and source-calibration
  contracts. No sampled-reward bound, stochastic reward confidence, or
  cross-round independence is used by this projection route.
- Retrieval evidence: exact local-memory search for the route returned no hit;
  exact local declarations for the deterministic terminal and fixed-policy iid
  erasure law were retrieved. Mathlib kernel, posterior/conditional-law,
  product-measure, and projective-limit APIs support the transport. Placement
  is `SCN-RL-MDP`, `TXT-SLIVKINS-2019-2024`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `WEAPON-UCB-OPTIMISM` is inspiration only.
- Status: `leanCompiled`; 22 declarations now expose the measurable projections,
  table-indexed stochastic kernel, concrete projected-selector source, selected
  batch law, projected prefix/next joint and conditional laws, complete
  trajectory pushforward, pulled-back bad event, and projected terminal.
  Focused/root/Tests builds, semantic non-degenerate-reward canaries,
  placeholder and baseline-axiom audits, independent review, synchronized
  indexes, and the full gate are required handoff evidence.
- Failure policy: the adaptive selector must factor through the known-reward
  projection by construction, and the projection must preserve every action
  and next state while reinstating only `mdp.reward`. Do not condition on erased
  sampled rewards, infer stochastic reward estimation, replace the projected
  process law by pointwise kernel equalities, or claim realized behavior regret,
  minimax rates, or complete UCB-VI.

## Compiled Theorem Route: Stochastic Reward Erasure IID Batch Law

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-ERASURE-IID-EPISODE-BATCH-LAW`.
- Lean-facing target: map every reward-bearing finite policy trajectory to the
  corresponding action/next-state trajectory by discarding only the sampled
  Real reward; prove exact equality with `trajectoryKernelRemaining`, lift it
  through the initial-state trajectory law and finite iid product, and identify
  the projected known-reward `EpisodeBatch` law with `iidEpisodeBatchMeasure`.
- Local APIs/imports: `RewardStepTrace`, `StepTrace`,
  `stochasticTrajectoryKernelRemaining`, `trajectoryKernelRemaining`,
  `actionRewardStateKernel_map_dropReward`, `Measure.compProd_map`,
  `Kernel.comap_map_comm`, `Measure.map_map`, `Measure.pi_map_pi`,
  `stochasticTrajectoryMeasure`, `iidStochasticTrajectoryFamilyMeasure`,
  `iidTrajectoryFamilyMeasure`, and `episodeBatchOfTrajectories`.
- Proof route: define the measurable coordinatewise reward erasure and prove it
  commutes with `Fin.cons`; induct on the remaining horizon, transporting the
  head with the compiled one-step drop-reward law and the tail with the
  induction hypothesis; then map the initial-state compProd law, the finite iid
  family, and the existing trajectory-to-batch conversion.
- Regularity contracts: finite measurable State/Action and the existing
  mean-compatible reward source; probability initial-state law only at the
  mixed full-trajectory surface; finite episode index for iid lifting. The
  final measurable `EpisodeBatch` projection additionally requires
  `MeasurableSingletonClass State` and `MeasurableSingletonClass Action`; the
  kernel, trajectory, and iid-erasure laws do not. No Standard Borel, reward
  boundedness, sub-Gaussian, reachability, confidence, or regret assumption is
  needed.
- Retrieval evidence: exact local-memory search for stochastic empirical
  optimistic known-reward transport returned no hit; exact local declarations
  for `actionRewardStateKernel_map_dropReward` and both recursive trajectory
  kernels were retrieved. Mathlib kernel map/comap, compProd, product-measure,
  and finite-sum cards provide the implementation surface. Placement evidence
  is `SCN-RL-MDP`, `TXT-SLIVKINS-2019-2024`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; proof-weapon cards are inspiration only.
- Status: `leanCompiled` in
  `FiniteHorizonStochasticRewardErasureLaw`. Fourteen declarations expose the
  coordinate projection, generic two-output `compProd` transport, recursive
  kernel equality, initial-law equality, iid family equality, and final
  known-reward batch law. Root-imported external canaries instantiate a
  two-action uniform policy with a genuinely non-degenerate symmetric reward
  source, verify action preservation, cover zero and positive horizons plus
  zero and two episodes, retain the next state, and check known-mean batch
  reward reinstatement. Focused/Tests builds, clean placeholder scan, and four
  baseline axiom audits pass. Independent review found no mathematical defect;
  its regularity and canary findings are repaired, and the generated
  indexes/full gate are refreshed before handoff. The immediate downstream
  consumer is a concrete stochastic known-mean empirical-transition optimistic
  adaptive source.
- Failure policy: erase sampled reward values only while retaining actions and
  next states exactly. The projected `EpisodeBatch` deliberately reinstates
  the known deterministic mean `mdp.reward`; do not call this stochastic reward
  estimation, reward confidence, adaptive count transport, behavior regret, or
  complete UCB-VI.

## Compiled Theorem Route: Adaptive Stochastic Realized Behavior Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT`.
- Lean-facing target: center every complete stochastic episode return by the
  selected policy's global initial-law value, prove the finite iid batch MGF,
  transport it to successor coordinates `1..rounds` of an adaptive stochastic
  batch source, and combine its two-sided tail with a caller-supplied count-good
  event to bound fixed-window realized average behavior regret.
- Local APIs/imports:
  `FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration`,
  `sampledCumulativeReturnDeviationSum`, `sampledCumulativeReward`,
  `MarkovPolicy.valueRemaining_abs_le_of_rewardBound`,
  `boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`,
  `HasSubgaussianMGF.of_map`, `iIndepFun_pi`,
  `HasSubgaussianMGF.sum_of_iIndepFun`, generic `HasSubgaussianMGF.add`,
  retained-input dynamic `condDistrib`, trimmed `condExpKernel.map`, `piLE`,
  and the compiled strongly-adapted two-sided tail.
- Proof route: split a globally centered episode return into the existing
  sampled-return deviation centered at its sampled initial state plus the
  selected policy value's initial-state fluctuation. Bound the latter on
  `[-horizon * rewardBound, horizon * rewardBound]`, lift it through the exact
  initial-state marginal, sum independent complete episodes, and combine the
  two batch components with the honest squared-sum-of-square-roots proxy.
  Add an explicit dynamic global-deviation measurability contract, identify the
  successor conditional law, prove a zero-plus-successors martingale tail, then
  establish realized equals expected minus deviation and union the count/return
  events.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action and complete batch/infinite trajectory at conditional endpoints;
  nonempty Action; probability initial-state law; fixed mean-compatible reward
  source; one selected-reward sub-Gaussian proxy; bounded deterministic MDP
  means; explicit prefix×batch global-deviation measurability; positive total
  proxy and `0 < delta <= 1`. No sampled-reward boundedness, within-episode
  stage independence, or cross-round independence is assumed.
- Retrieval evidence: exact local-memory search returned no hit; the compiled
  adaptive per-state-centered route and deterministic realized-regret transport
  are parents; exact Mathlib/local product independence, bounded Hoeffding,
  conditional-distribution, conditional-expectation, filtration, and
  sub-Gaussian APIs were retrieved. Source placement is `SCN-RL-MDP`,
  `TXT-SLIVKINS-2019-2024`, and `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`;
  `WEAPON-TAIL-INEQUALITIES` is inspiration only.
- Status: `leanCompiled` in
  `FiniteHorizonAdaptiveStochasticRewardRealizedBehaviorRegret`. Fifty-four
  declarations expose the initial-state value fluctuation and exact marginal,
  iid value/global-return MGFs, the squared-sum-of-square-roots batch proxy,
  dynamic successor law and trimmed conditional-expectation transport,
  successor-only conditional MGFs and tail, exact realized/expected regret
  identities, measurable return bad event, and the count/return event-union
  endpoint. Root and external Bool/Unit canaries instantiate the initial
  marginal, both MGF layers, exact global centering identity, dynamic
  `condDistrib`, conditional MGF, positive two-round proxy, tail, averaged
  regret identity, and full event transport. Placeholder scanning is clean;
  four representative axiom audits report only `propext`, `Classical.choice`,
  and `Quot.sound`. Independent review found no P0-P2. Its P3 constant-policy
  measurability gap is repaired with the existing history-sensitive
  Bool-action `Kernel.piecewise` source; the remaining P3 asks the next
  concrete policy/count-event consumer for a nonzero two-action terminal test.
- Failure policy: do not identify the existing per-sampled-state-centered
  return deviation with deviation from the global expected return. The missing
  initial-state policy-value fluctuation must be present in the statistic and
  proxy. Do not add the two component proxies unless conditional independence
  is proved; the generic same-space combination uses the squared sum of square
  roots. Preserve successor coordinates `1..rounds` and two confidence shares.
  Concrete stochastic empirical-policy source construction, a matching
  count/optimism event, decaying schedules, anytime, minimax, and complete
  UCB-VI remain downstream.

## Compiled Theorem Route: Adaptive Stochastic Episode Sampled Return Tail

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EPISODE-BATCH-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: generate an infinite adaptive trajectory of finite
  complete stochastic-reward episode batches; identify every successor batch
  conditional law with the finite iid law of the policy selected from the
  observed prefix; prove initial and successor sampled-return/value-deviation
  MGFs with the compiled iid proxy; expose a finite-round two-sided martingale
  tail with the exact round-linear proxy.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardIIDTotalReturnConcentration`,
  `FiniteHorizonAdaptiveEpisodeBatchLaw`, `ConditionalExpectationReward`,
  `Kernel.trajMeasure`, `Kernel.id`, `Kernel.prod`, `Kernel.map`,
  `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`,
  `condDistrib_comp`,
  `condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim`,
  `hasCondSubgaussianMGF_of_condExpKernel_map_eq`, `Filtration.piLE`, and the
  local strongly-adapted sub-Gaussian sum delta tail.
- Proof route: define the complete stochastic episode-family and adaptive
  history/source surfaces; reuse the iid product as every initial/successor
  batch law; retain the conditioning prefix with `Kernel.id ×ₖ batchKernel`
  before mapping the history-dependent deviation; identify its regular
  conditional distribution; transport the iid MGF to initial and successor
  coordinates; assemble the strongly-adapted finite-round sum and tail.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action and the generated batch/trajectory spaces; nonempty Action;
  probability initial-state law; fixed mean-compatible reward source; common
  selected-reward proxy and bounded deterministic mean rewards. The source
  must expose measurability of the history-selected policy deviation on
  prefix×batch; the tail additionally requires positive total proxy and
  `0 < delta <= 1`. No cross-round or within-episode independence is assumed.
- Retrieval evidence: exact adaptive stochastic-episode sampled-return search
  no-hit; compiled iid stochastic-return parent and deterministic adaptive
  episode-law/martingale route; exact Mathlib trajectory, conditional-law,
  kernel-product, filtration, and sub-Gaussian APIs; `SCN-RL-MDP` and
  `WEAPON-TAIL-INEQUALITIES` are placement/inspiration evidence only.
- Status: `leanCompiled` in
  `FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration`. Thirty-three
  recorded declarations expose the retained-input generic kernel transport,
  adaptive source/trajectory, dynamic `condDistrib` and trimmed
  `condExpKernel` laws, initial/successor MGFs, strong adaptation, exact
  round-linear proxy, cumulative deviation, and finite-round tail. Root and
  external canaries cover a concrete Bool/Unit source, dynamic law, conditional
  MGF, proxy `22 = 2 * 11`, and two-round tail. A history-sensitive Bool-action
  `Kernel.piecewise` source selects different successor policies from the
  observed prefix; its true/false conditional iid batch laws are proved unequal
  through first-action marginals, and its dynamic `condDistrib` endpoint is
  instantiated. Placeholder and baseline-axiom audits pass. Independent review
  found no P0/P1; its P2 weak-adaptivity-canary and P3 overbroad-regularity
  findings are repaired.
- Failure policy: preserve centering by each sampled initial state's value
  under the prefix-selected policy and add variance proxies before applying
  the confidence radius. The infinite real-reward trajectory's
  `StandardBorelSpace` remains an explicit conditional-kernel contract. Do not
  substitute global initial-law mean centering, infer measurability of a
  history policy selector from pointwise definitions, assume cross-round or
  within-episode independence, or claim uniform/anytime, regret, optimism,
  minimax, or complete UCB-VI conclusions.

## Compiled Theorem Route: Finite IID Episode Sampled Return Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EPISODE-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: construct the finite iid product of complete
  reward-bearing stochastic trajectories; prove exact coordinate marginals
  and independence of each episode's sampled-return deviation; prove the
  finite episode sum MGF with proxy
  `episodes * (horizon * rewardVarianceProxy +
  meanBellmanInnovationVarianceProxy rewardBound horizon)`; expose the
  corresponding two-sided delta tail.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration`,
  `Measure.pi`, `measurePreserving_eval`, `iIndepFun_pi`,
  `HasSubgaussianMGF.of_map`, `HasSubgaussianMGF.sum_of_iIndepFun`,
  and `subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun`.
- Proof route: define the product of identical full stochastic trajectory
  measures; identify each evaluation pushforward exactly; compose the compiled
  full-trajectory deviation with coordinate evaluation; transport its MGF
  through the map equality; use product-coordinate independence and Mathlib's
  finite independent-sum MGF theorem; consume the local delta-calibrated tail.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action; nonempty Action; probability initial-state law; fixed
  MDP/policy/mean-compatible product source; common reward proxy and bounded
  deterministic means. The tail additionally requires positive total episode
  proxy and `0 < delta <= 1`. Episodes are complete iid coordinates; no
  within-episode stage independence or adaptive cross-episode policy update.
- Retrieval evidence: exact stochastic-reward iid sampled-return search no-hit;
  compiled initial-law parent; local deterministic-trajectory iid product
  pattern; exact Mathlib product-independence/sub-Gaussian sum APIs;
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, and `SCN-RL-MDP`.
- Status/failure policy: `leanCompiled`; twelve declarations, zero-episode
  empty-product/zero-sum/zero-proxy/MGF canaries, and two-episode
  product/marginal/independence/proxy/MGF/tail canaries compile.
  Preserve complete-episode iid semantics and per-trajectory initial-state
  value centering. Do not assume
  stagewise independence, replace the sum proxy by a confidence-radius sum,
  or infer adaptive, uniform/anytime, regret, optimism, minimax, or complete
  UCB-VI conclusions.

## Compiled Theorem Route: Initial-Law Sampled Return Sub-Gaussian Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-INITIAL-LAW-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: define sampled cumulative return centered by
  `policy.valueRemaining` at the trajectory's own initial state; lift the
  common statewise MGF proxy through
  `initialState.compProd stochasticTrajectoryKernelRemaining`; expose the
  fixed-horizon two-sided delta tail under the full stochastic trajectory
  measure.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration`,
  `FiniteHorizonStochasticRewardTotalReturnConcentration`,
  `Measure.integrable_compProd_iff`, `Measure.integral_compProd`,
  `AEStronglyMeasurable.integral_kernel_compProd`,
  `integrable_of_fintype_aestronglyMeasurable`,
  `stochasticTrajectoryMeasure`, and the compiled statewise sampled-return
  MGF/tail route.
- Proof route: prove a reusable finite-index fiber-MGF mixture theorem by
  Fubini: establish exponential integrability on every kernel fiber and on the
  finite outer law, rewrite the full MGF as an iterated integral, apply each
  fiber MGF bound, and integrate the common constant. Instantiate it with the
  generated full-horizon trajectory kernel, then consume the existing
  one-coordinate strongly-adapted delta-tail theorem.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action; nonempty Action; probability initial-state law; fixed
  MDP/policy/mean-compatible product source; one common selected-reward
  `NNReal` proxy; bounded deterministic mean rewards. The tail also needs a
  positive total proxy and `0 < delta <= 1`. No singleton measurability,
  reachability, iid episodes, adaptive filtration, optimism, or regret premise.
- Retrieval evidence: exact initial-law sampled-return route search no-hit;
  compiled statewise parent; exact Mathlib `compProd` integrability/integral
  and sub-Gaussian structure sources; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, and `SCN-RL-MDP`.
  Theorem cards and weapons remain route evidence only.
- Status/failure policy: `leanCompiled`; five declarations, focused/root and
  external Dirac plus non-Dirac Bool-mixture MGF/tail canaries compile.
  Independent review's mixture-coverage finding is repaired. Preserve state-dependent
  centering and the common fiber proxy. Do not center by a global initial-law
  mean, add a state-mixture variance term without proving a different theorem,
  or infer finite-iid, adaptive, uniform/anytime, regret, minimax, or complete
  UCB-VI conclusions.

## Compiled Theorem Route: Sampled Return Around Policy Value Sub-Gaussian Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: define the actual sampled cumulative return minus
  `policy.valueRemaining`; prove its exact pathwise decomposition into the
  compiled cumulative selected-reward noise and cumulative mean Bellman
  innovation; prove a generated-trajectory MGF with additive proxy
  `remaining * rewardVarianceProxy +
  meanBellmanInnovationVarianceProxy rewardBound remaining`; expose the
  corresponding fixed-horizon two-sided delta tail.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardTotalReturnConcentration`,
  `FiniteHorizonStochasticRewardBellmanInnovationConcentration`,
  `MDP.sampledCumulativeRewardFrom`,
  `MDP.sampledCumulativeRewardDeviationFrom`,
  `MDP.sampledCumulativeMeanBellmanInnovationFrom`,
  `UniformSubgaussianRewardLaw`, `actionStateKernel`,
  `actionRewardStateKernel`, `rewardNextStateKernel`, `Kernel.id`, `comap`,
  `map`, `compProd`, `Kernel.HasSubgaussianMGF.add_compProd`,
  `IdentDistrib`, and the existing fixed-horizon delta tail.
- Proof route: first prove the pathwise telescoping identity. For the sharp
  additive one-step proxy, sample `(action,nextState)` under
  `actionStateKernel`, conditionally resample reward from the selected reward
  kernel while retaining action/next state, and prove that mapping this
  hierarchical kernel recovers `actionRewardStateKernel`. Apply
  `add_compProd` to the mean Bellman innovation and the conditionally centered
  reward noise, then recurse on the sampled next state and map the augmented
  law back to the exact generated trace.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action and nonempty Action for conditional kernel composition; fixed
  MDP/policy/mean-compatible source; one common selected-reward `NNReal`
  variance proxy; an `NNReal` absolute bound on deterministic MDP mean rewards;
  explicit start state. The tail additionally requires positive total proxy
  and `0 < delta <= 1`. The source retains its conditional product of reward
  and next-state laws given state/action; no cross-stage independence is used.
- Retrieval evidence: exact local-memory search no-hit; compiled cumulative
  reward-noise and mean-Bellman-innovation parents;
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`;
  `SCN-RL-MDP`; `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` is placement evidence;
  tail/optimism weapons are inspiration only.
- Status: `leanCompiled`; 33 declarations cover the exact pathwise split,
  generic composition-product map helpers, retained state/action/next-state
  kernels, raw and centered reward law transports, the one-step combined MGF,
  the recursive generated-trajectory MGF, and the fixed-horizon tail. Focused,
  root, and `Tests.Basic` builds pass. External canaries instantiate
  nondegenerate sampled reward, randomized action, and randomized transition
  models. Placeholder and baseline-axiom audits pass; independent local review
  found no semantic or regularity defect.
- Failure policy: do not infer an additive proxy from two marginal MGFs or
  silently assume unconditional independence. Generic `HasSubgaussianMGF.add`
  only yields a squared sum-of-square-roots proxy and is not the target route.
  The required kernel law transport now compiles. Do not replace it by radius
  addition, generalize to correlated reward/next-state laws, or infer an
  initial-law, iid-episode, uniform/anytime, regret, optimism, minimax, or
  complete UCB-VI theorem from this fixed-state route.

## Compiled Theorem Route: Mean Bellman Innovation Sub-Gaussian Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-MEAN-BELLMAN-INNOVATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: define the recursive generated-trajectory sum of
  `mdp.reward state action + valueRemaining tail nextState - valueRemaining
  current state`; prove its one-step bounded centered MGF, cumulative MGF with
  proxy `sum k=1..remaining, (k * rewardBound)^2`, and fixed-horizon two-sided
  delta tail.
- Local APIs/imports: finite-horizon Bellman/value and action-state kernels;
  stochastic reward-bearing trajectory/head laws; finite-state integral
  bounds; `intervalVarianceProxy` and the bounded-centered Hoeffding wrapper;
  kernel fiber lifting, retained-input product kernels, `add_compProd`, exact
  generated-kernel maps, and the existing delta tail.
- Proof route: bound every continuation value by its remaining reward
  envelope; identify the policy action/transition integral of the one-step
  mean return with the current `valueRemaining`; apply Hoeffding on that
  bounded centered variable; transport it to the reward-bearing head law;
  recurse through the exact generated trajectory kernel and add the
  stage-dependent proxies.
- Regularity contracts: finite measurable State/Action; Standard Borel
  State/Action and nonempty Action for recursive kernel composition; fixed
  MDP/policy/mean-compatible source and explicit state; `NNReal` reward bound
  on deterministic MDP means. The tail additionally requires a positive total
  proxy and `0 < delta <= 1`; sampled rewards need not be bounded.
- Retrieval evidence: exact local-memory search no-hit; compiled stochastic
  cumulative reward-deviation and trajectory parents;
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`;
  `SCN-RL-MDP`; UCB-VI paper placement evidence; tail/optimism weapons only as
  route inspiration.
- Status: `leanCompiled`; 15 declarations cover the stage/cumulative proxies,
  policy-value envelope, exact law transports, one-step and generated MGFs,
  and the fixed-horizon two-sided tail. Focused/root/Tests, randomized-action
  canaries, and a nondegenerate uniform-transition canary with two-sided mass
  `1/2` and trace innovations `+/-1/2` pass. Independent review found no route
  defect; its compile and semantic-coverage findings were repaired before the
  audits, indexes, and full gate.
- Failure policy: do not center only the next-state term under a randomized
  policy or use a whole-return `H^2` shortcut. Its exact conditional consumer
  with sampled reward noise now compiles above; do not infer that consumer from
  the two marginal theorems alone. No uniform/anytime, regret, minimax, or
  complete UCB-VI claim.

## Compiled Theorem Route: Stochastic Reward Cumulative Deviation Sub-Gaussian Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-CUMULATIVE-DEVIATION-SUBGAUSSIAN-TAIL`.
- Lean-facing target: define the sum of actual sampled rewards minus the
  stored MDP mean at each actual pre-step state and sampled action; prove its
  generated-trajectory MGF has proxy `remaining * varianceProxy`, then expose
  the fixed-horizon two-sided delta tail.
- Local APIs/imports:
  `FiniteHorizonStochasticRewardCumulativeConcentration`, the compiled
  stochastic trajectory and head-concentration parents,
  `kernel_hasSubgaussianMGF_of_ae`, `Kernel.id ×ₖ`, kernel map/compProd,
  `Kernel.HasSubgaussianMGF.add_compProd`, `IdentDistrib`, and the local
  strongly-adapted delta tail.
- Proof route: recurse on remaining horizon; lift the head MGF to a kernel over
  the start-state Dirac law; retain the recursive input and map it to the
  sampled next state plus tail; lift induction-hypothesis fibers to a kernel
  MGF; add the proxies; prove the augmented kernel maps exactly to the
  original generated trace; transport the MGF and specialize the delta tail.
- Regularity contracts: finite measurable State/Action, Standard Borel
  State/Action, nonempty Action, explicit start state, and one common selected
  reward-law `NNReal` proxy. The tail additionally requires positive total
  proxy and `0 < delta <= 1`. The source's `rewardNextStateKernel` is the
  conditionally independent reward/transition product given state/action; no
  independence between stages, measurable-singleton, uniform-time, optimism,
  or regret premise is added.
- Retrieval/status/failure policy: exact route retrieval was a no-hit; reuse
  the compiled trajectory/head concentration parents and Mathlib
  sub-Gaussian/kernel/measure/martingale APIs. The project-local route compiles
  with seven declarations and horizon-zero plus nondegenerate two-step
  symmetric canaries. The latter compute all-positive event mass `1/4`, show
  deviation two there, and witness positive mass for the `delta = 3/4` tail.
  Preserve actual state/action centering and the linear proxy; do not
  substitute an `H^2` bounded-total-return theorem or infer transition/Bellman
  concentration, regret, minimax rates, or complete UCB-VI.

## Compiled Theorem Route: Stochastic Reward Head Conditional Sub-Gaussian Tail

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-SUBGAUSSIAN-TAIL`.
- Lean-facing target: package a common selected-reward sub-Gaussian proxy,
  construct it from common a.s. interval support, and prove that the actual
  first sampled reward centered by the mean of its sampled action is
  conditionally sub-Gaussian on `comap headAction`, globally sub-Gaussian, and
  satisfies the existing one-step two-sided delta tail.
- Local APIs/imports: `FiniteHorizonStochasticRewardConcentration`,
  `FiniteHorizonStochasticRewardConditionalLaw`, `ConcentrationSubGaussian`,
  `Mathlib.Probability.Process.Adapted`,
  `boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`,
  `hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq`,
  `HasSubgaussianMGF.trim/add_of_hasCondSubgaussianMGF`, `Filtration.const`,
  `StronglyAdapted`, and
  `condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted`.
- Proof route: use the selected-law mean identity and common interval support
  for a Hoeffding proxy; transport each selected MGF through the compiled head
  `condExpKernel.map` law; add the conditional increment to zero on the
  trimmed action-generated sigma-algebra; specialize the finite strongly
  adapted sum tail to one full-space-measurable coordinate.
- Regularity contracts: finite measurable State/Action, standard Borel
  State/Action, nonempty Action, and an explicit start state which supplies
  nonempty State. The abstract source needs one common `NNReal` proxy; the
  constructor needs one common selected-reward interval; the tail needs a
  positive real proxy and `0 < delta <= 1`. No measurable-singleton,
  multi-step filtration, action-independence, or regret premise is added.
- Retrieval/status/failure policy: exact route retrieval was a no-hit; reuse
  the compiled conditional-law parent, local conditional-MGF and adaptive-tail
  patterns, Mathlib probability/sub-Gaussian/conditional-expectation/kernel
  cards, and RL/UCB-VI placement only. The project-local route compiles with
  ten declarations and a nondegenerate symmetric `{-1,1}` canary. Preserve
  `headReward - mdp.reward state headAction` and `comap headAction`; do not
  substitute the randomized reward mixture, infer the source law from `L1`,
  or claim multi-step, uniform/anytime, regret, minimax, or complete UCB-VI.

## Compiled Theorem Route: Stochastic Reward Trajectory Head Conditional Law

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-LAW`.
- Lean-facing target: under each generated positive stochastic trajectory,
  the first sampled reward conditioned on the first sampled action has the
  state-frozen selected reward law; expose the same identification as a
  trimmed `condExpKernel.map` equality.
- Local APIs/imports: `FiniteHorizonStochasticRewardConditionalLaw`, the
  compiled head marginal maps, `RewardStepTrace.headAction/headReward`,
  `Kernel.sectR`, `Measure.ext_prod/fst_compProd`,
  `condDistrib_ae_eq_iff_measure_eq_compProd`, and
  `condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim`.
- Proof route: freeze state with `sectR`; use the compiled rectangle formula
  and finite product-measure extensionality to identify the action/reward law
  with the action kernel composed with the selected reward kernel; derive the
  action marginal; characterize the one-step and generated conditional laws
  by their composition-product joint measures; apply the local Real-valued
  conditional-expectation bridge.
- Regularity contracts: finite measurable State/Action for the factorization
  and `condDistrib` layers. The final `condExpKernel` wrapper additionally
  requires standard Borel State/Action and nonempty Action; nonempty State is
  derived from its explicit argument. No boundedness, second moment,
  sub-Gaussian, measurable-singleton, or deterministic-policy assumption is
  added.
- Retrieval/status/failure policy: exact route search was a no-hit; reuse
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-POSTERIOR`,
  `MLIB-CONDITIONAL-EXPECTATION`, the compiled head marginal parent, and the
  local condDistrib-to-condExpKernel bridge. The project-local route is
  compiled with ten declarations and external canaries. Do not replace the
  selected law by its randomized-action mixture or mean, and do not infer a
  conditional MGF, concentration, regret, optimism, or complete UCB-VI.

## Compiled Theorem Route: Stochastic Reward Trajectory Head Marginal Factorization

- Route id:
  `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-MARGINAL-FACTORIZATION`.
- Lean-facing target: for every positive remaining horizon and starting state,
  identify the generated trace's first `(action,reward,nextState)` law with
  `actionRewardStateKernel`; define its `(action,reward)` and reward-only
  Markov marginals; prove the exact action/reward rectangle factorization and
  reward-event policy-mixture formula.
- Supporting declarations: measurable first-step, action/reward, and reward
  projections on `RewardStepTrace`; `actionRewardKernel` and
  `rewardMarginalKernel` with Markov instances; trajectory map laws; joint
  rectangle and reward-event endpoints.
- Local APIs/imports: `FiniteHorizonStochasticRewardTrajectory`, the compiled
  `actionRewardStateKernel` and recursive trajectory kernel,
  `Kernel.map_apply/map_comp_right/fst_compProd/compProd_apply_prod`,
  `Kernel.prod_apply_prod`, `Measure.map_apply/map_map`, and the deterministic
  `MarkovPolicy.trajectoryKernelRemaining_map_head` proof pattern.
- Proof route: unfold one positive recursive step; compose the generated
  cons-map with first-coordinate evaluation; discard the Markov tail through
  `fst_compProd`; map away next state and then action; for measurable
  rectangles, rewrite projection preimages as product sets and expand the
  action and reward/transition composition products. Transition mass one
  leaves exactly the selected reward law integrated against the policy action
  kernel.
- Regularity contracts: finite measurable State/Action and the existing MDP,
  Markov policy, and mean-compatible Markov reward source. Event statements
  require measurable action/reward sets. No reward boundedness, moment beyond
  the parent `L1` contract, measurable-singleton, Standard Borel,
  `condDistrib`, or correlated reward/next-state law is assumed.
- Retrieval evidence: exact local/memory search for the stochastic reward
  trajectory marginal was a no-hit. Reuse the compiled deterministic head-map
  theorem and generic `RewardKernel` marginal patterns; Mathlib cards
  `MLIB-PROBABILITY-KERNEL` and `MLIB-MEASURE-INTEGRAL`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` place the route only;
  `WEAPON-TAIL-INEQUALITIES` is inspiration only.
- Status: `leanCompiled`; `FiniteHorizonStochasticRewardMarginal` contributes
  16 public declarations. Focused/`Tests.Basic` builds, randomized-policy exact
  mass canaries, a horizon-two stage-one canary, nondegenerate generated-law
  transport, placeholder/axiom/declaration audits, synchronized registries,
  independent review, and the full repository gate pass before handoff.
- Failure policy: preserve randomized policy mixing and the actual generated
  reward coordinate. Do not replace the law by `mdp.reward`, specialize the
  policy to a deterministic action, infer sub-Gaussian concentration from
  `L1`, or claim a regular conditional distribution without its explicit
  Standard Borel/singleton contract. If factorization fails, isolate the exact
  map/compProd preimage or measurability premise instead of weakening the law.

## Compiled Theorem Route: Stochastic Reward Trajectory Value Identity

- Route id: `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-VALUE-IDENTITY`.
- Lean-facing target: generate finite traces with actual
  `(action,reward,nextState)` coordinates from a policy and the compiled
  mean-compatible reward/transition product kernel; prove sampled cumulative
  reward integrable; identify its statewise expectation with
  `stochasticValueRemaining`; integrate an initial probability law and rewrite
  the endpoint as both stochastic and existing mean `valueAt 0`.
- Local APIs/imports: `FiniteHorizonStochasticRewardBellman`, deterministic
  `FiniteHorizonTrajectory` recursion, `Kernel.compProd/comap/map`,
  `integrable_map_measure`, kernel/measure `integrable_compProd_iff` and
  `integral_compProd`, measurable kernel integrals, and stochastic backward
  value identities.
- Proof route: define measurable reward-trace cons/tail and recursive kernels;
  induct on remaining horizon. Because reward coordinates are Real, replace
  the deterministic route's finite-type shortcut by nested conditional L1:
  selected reward integrability plus tail integrability bounds the inner norm,
  `integrable_compProd_iff` closes both kernel layers, and Fubini turns the
  recursive sampled return into the stochastic Bellman recursion.
- Regularity contracts: finite measurable State/Action, parent MDP and Markov
  policy, mean-compatible selected reward laws, and a probability initial law
  only for the full trajectory theorem. No reward bound, second moment,
  sub-Gaussian assumption, Standard Borel condition, or arbitrary correlated
  reward/next-state coupling is introduced.
- Retrieval evidence: exact memory/local search found no reward-bearing finite
  trajectory consumer. The pinned Mathlib kernel/product/map/Fubini/L1 APIs
  are covered by `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-FINSET-SUMS`; `SCN-RL-MDP` and UCB-VI literature place the route only.
- Status: `leanCompiled`; `FiniteHorizonStochasticRewardTrajectory` contributes
  18 public declarations. Focused/root/`Tests.Basic` builds, deterministic and
  symmetric two-point canaries, including exact generated first-reward mass
  `1/2`, placeholder/axiom/declaration audits, synchronized registries,
  independent review, and the full repository gate pass before handoff.
- Failure policy: do not fall back to deterministic `mdp.reward`, silently add
  boundedness to avoid the L1 proof, or claim correlated joint laws,
  concentration, realized-regret tails, optimism, minimax, or complete UCB-VI.
  If recursive L1 transport fails, isolate the exact compProd measurability or
  norm-integrability premise instead of weakening the trajectory identity.

## Compiled Theorem Route: Stochastic Reward Kernel Bellman Transport

- Route id: `RL-FINITE-HORIZON-STOCHASTIC-REWARD-KERNEL-BELLMAN-TRANSPORT`.
- Lean-facing target: package a
  `RewardKernel.MarkovRewardKernel (State x Action) Real` whose selected
  identity is integrable and has mean `mdp.reward state action`; form its
  product with `mdp.transition`; prove the sampled one-step action value and
  policy Bellman operator equal the existing mean-reward definitions; carry
  this equality through `valueRemaining` and `valueAt`; construct the law for
  the existing deterministic reward as a compatibility witness.
- Local APIs/imports: `FiniteHorizonPolicy`, `RewardKernel.MarkovRewardKernel`,
  `Kernel.prod`, `Kernel.prod_apply`, `Integrable.comp_fst`,
  `Integrable.comp_snd`, `integral_prod`, `integrable_of_fintype`,
  `MDP.bellmanQ`, `MarkovPolicy.bellman`, `valueRemaining`, and `valueAt`.
- Proof route: use the selected reward and transition probability instances;
  lift reward and continuation integrability to the product measure; apply
  Fubini; split the inner and outer sums; rewrite the selected reward integral
  by the compatibility law and the state integral by `transitionValue`; use
  the pointwise identity under the action kernel; finish the backward values
  by induction and proof irrelevance.
- Regularity contracts: finite measurable State/Action; parent Markov
  transition and measurable mean reward; measurable continuation values;
  integrable identity under every selected Real reward law; exact selected
  mean equality. The product kernel models conditional independence of reward
  and next state given `(state,action)`.
- Retrieval evidence: exact local/memory search found no stochastic-reward
  Bellman consumer. Pinned Mathlib provides product kernels, selected product
  measures, Fubini, and product integrability under
  `MLIB-PROBABILITY-KERNEL` and `MLIB-MEASURE-INTEGRAL`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` place the route. Weapon cards are
  inspiration only.
- Status: `leanCompiled`; 14 registered declarations in
  `FiniteHorizonStochasticRewardBellman`, root export, and external Unit
  law/Q/policy/remaining/value/terminal canaries compile. Declaration,
  placeholder, axiom, index, and full-gate evidence is refreshed before
  handoff.
- Failure policy: do not claim arbitrary correlated reward/next-state joint
  laws, a stochastic-reward trajectory measure, realized stochastic return,
  concentration, optimism, or regret. If product/Fubini rewriting is blocked,
  keep the mean-compatible law and one-step integral lemma explicit instead
  of weakening the equality target or adding unproved regularity.

## Compiled Theorem Route: Common-Space L1 Realized Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-CONSISTENCY`.
- Lean-facing target: on the compiled independent-coordinate common measure,
  prove every scheduled realized-behavior regret coordinate belongs to
  Mathlib `MemLp` at exponent one, identify its `eLpNorm` with the `ENNReal`
  lift of the compiled expected absolute regret, prove the canonical
  `eLpNorm (process n - 0) 1` tends to zero, and package the coordinates as an
  `Lp Real 1` sequence converging to zero in the `Lp` topology.
- Supporting leaves: convert compiled integrability with
  `memLp_one_iff_integrable`; simplify
  `MemLp.eLpNorm_eq_integral_rpow_norm` at exponent one; transport the real
  expectation limit through `ENNReal.continuous_ofReal`; rewrite subtraction
  by the zero function; construct the `MemLp.toLp` sequence; apply
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; recover convergence in measure through
  `tendstoInMeasure_of_tendsto_eLpNorm` as a consistency cross-check.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceExpectedConsistency`,
  `memLp_one_iff_integrable`,
  `MemLp.eLpNorm_eq_integral_rpow_norm`, `eLpNorm_congr_ae`,
  `ENNReal.continuous_ofReal`, `MemLp.toLp`,
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`, and
  `tendstoInMeasure_of_tendsto_eLpNorm`; candidate import
  `Mathlib.MeasureTheory.Function.LpSpace.Complete`.
- Proof route: reuse the exact integrability theorem rather than reproving the
  good/bad split. At exponent one, rewrite `eLpNorm` to the Bochner integral of
  the Real norm, identify norm with absolute value and the existing expected
  absolute definition, then map the compiled Real `Tendsto` through
  `ENNReal.ofReal`. Normalize the zero-limit subtraction form and use the
  standard `Lp` convergence equivalence for the packaged process.
- Regularity contracts: exactly the compiled expected-absolute parent: finite
  measurable nonempty State/Action with decidable equality and measurable
  singletons; probability initial law; positive horizon/base visit floor;
  deterministic absolute reward bound one; path support/full-exploration
  floor; indexed Standard Borel batch and trajectory witnesses. No new moment
  or cross-window dependence premise is introduced.
- Retrieval evidence: exact memory/local searches for common-space `L1`,
  `snorm`/`eLpNorm`, `MemLp`, and realized-behavior regret returned no local
  consumer. Pinned Mathlib provides the exponent-one `MemLp`, `eLpNorm`, `Lp`
  topology, and convergence-in-measure bridge under `MLIB-MEASURE-INTEGRAL`
  and `MLIB-PROBABILITY-VARIANCE`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` place the route;
  `WEAPON-TAIL-INEQUALITIES` remains inspiration only.
- Status: `leanCompiled`; 8 public declarations in
  `FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceL1Consistency` compile
  through
  `exploratorySource_decayingExplorationEpisodewiseCommonMeasure_memLp_eLpNorm_L1_tendsto_zero`.
  Root export and external `MemLp`, exact-`eLpNorm`, named-`Lp`, and terminal
  canaries compile; declaration/index/axiom/full-gate evidence is refreshed
  before handoff.
- Failure policy: this is `L1` convergence under the explicit independent
  product coupling of complete scheduled experiments. It does not construct a
  nested causal online stream and does not imply pathwise, almost-sure,
  anytime, or cross-window causal consistency. Do not infer stochastic
  rewards, minimax rates, or complete UCB-VI. Do not replace the direct norm
  identity by a stronger Vitali/uniform-integrability route unless the direct
  Mathlib API is genuinely unavailable.

## Compiled Theorem Route: Common-Space Expected Absolute Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-EXPECTED-ABSOLUTE-REALIZED-CONSISTENCY`.
- Lean-facing target: on the compiled independent-coordinate common probability
  space, prove every scheduled realized-behavior regret coordinate integrable,
  bound its expected absolute value by the decaying finite-window good-event
  radius plus `2*horizon` times the real-valued failure budget, and prove that
  expectation tends to zero.
- Supporting leaves: a pointwise `horizon` envelope for deterministic finite
  trajectory return and for `optimalInitialExpectedReturn`; adaptive successor
  batches are reward-consistent a.e.; realized successor-average regret has an
  a.e. `2*horizon` envelope and is integrable; the pulled-back common bad event
  is measurable; good/bad indicator integration yields the finite expectation
  bound; both terms in that bound tend to zero.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceConsistency`,
  `MDP.cumulativeRewardFrom_eq_sum_traceReward`,
  `EpisodeBatch.abs_totalReturn_le_of_rewardConsistent`,
  `MarkovPolicy.iidEpisodeBatchMeasure_rewardConsistent_ae`,
  `AdaptiveEpisodeBatchSource.trajectoryMeasure_prefix_compProd`,
  `Measure.ae_compProd_of_ae_ae`, `ae_of_ae_map`,
  `Filter.eventually_all`, `Integrable.mono'`, `integral_indicator`,
  `setIntegral_const`, `ENNReal.toReal_mono`, `ENNReal.tendsto_toReal`, and
  `squeeze_zero`.
- Proof route: first transport the iid generated-batch reward-consistency
  support through every adaptive successor kernel and the exact prefix/next
  `compProd` law. Use the deterministic reward bound to control optimal return
  and every reward-consistent realized window by `2*horizon`, then transport
  that a.e. envelope through the exact common-space coordinate marginal to get
  integrability. Split the absolute process into the compiled measurable bad
  event and its complement: outside, use the decaying sharp radius; inside,
  use the uniform envelope. Integrate the indicator, apply the existing failure
  budget, convert it with `ENNReal.toReal`, and squeeze to zero.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; probability initial law; positive
  horizon and base visit floor; deterministic rewards bounded in absolute value
  by one; path support/full-exploration visit floor; indexed Standard Borel
  batch and trajectory witnesses. No extra cross-window dependence assumption
  is added.
- Retrieval evidence: exact local/memory searches for common-space `L1`,
  expected absolute realized regret, adaptive realized-regret integrability, and
  adaptive trajectory reward consistency returned no declaration; the compiled
  common-space route is the parent. Mathlib measure/integral, product-kernel,
  ENNReal topology, and finite-filter APIs provide the leaves;
  `SCN-RL-MDP` and `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` place the route;
  `WEAPON-TAIL-INEQUALITIES` is inspiration only.
- Status: `leanCompiled`; 17 public declarations in
  `FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceExpectedConsistency`
  compile through
  `exploratorySource_decayingExplorationEpisodewiseCommonMeasure_integrable_expectedAbsoluteRealizedBehaviorRegret_tendsto_zero`.
  Root export and external deterministic-envelope, integrability, finite-bound,
  and terminal canaries compile; declaration/index/axiom/full-gate evidence is
  refreshed before handoff.
- Failure policy: the expectation is taken under the explicit independent
  product coupling of complete scheduled experiments. It is not a natural
  nested online stream and does not imply pathwise, almost-sure, anytime, or
  cross-window causal consistency. Do not infer stochastic rewards, minimax
  rates, or complete UCB-VI.

## Compiled Theorem Route: Episodewise Common-Space Consistency In Probability

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-CONSISTENCY`.
- Lean-facing target: construct one explicit dependent infinite-product
  probability space whose coordinate `n` has exactly the compiled scheduled
  adaptive trajectory law, define the scheduled realized-behavior regret
  process on that space, prove every process coordinate measurable, strengthen
  the finite-window good side to an absolute regret bound, and prove Mathlib
  `TendstoInMeasure` to zero.
- Supporting leaves: measurability of realized cumulative/average regret;
  nonnegativity of successor expected cumulative/average
  regret; absolute realized-regret control from the expected bound and the
  two-sided return deviation; a finite-window absolute terminal; the dependent
  window space, marginal laws, `Measure.infinitePi` coupling, coordinate
  marginal equality, and the common-space tail squeeze.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeEpisodewiseRealizedBehaviorConsistency`,
  `EpisodeBatch.measurable_totalReturn`, `measurable_pi_apply`,
  `MarkovPolicy.expectedRegret_nonneg`,
  `realizedSuccessorAverageRegret_eq_expected_sub_deviation`,
  `Measure.infinitePi`, `Measure.infinitePi_map_eval`,
  `measurePreserving_eval_infinitePi`, `TendstoInMeasure`,
  `tendstoInMeasure_iff_dist`, `abs_sub`, and `abs_div`.
- Proof route: compose measurable finite return sums with the dependent-product
  evaluation maps. Then use the existing count-event expected-regret certificate and
  sharp two-sided return event to bound the absolute realized regret outside
  their union. Couple the varying finite-window laws as independent coordinates
  of `Measure.infinitePi`; use the exact coordinate marginal, eventual decay of
  the deterministic regret bound, event containment, and the vanishing doubled
  confidence budget to squeeze every positive-distance event to zero.
- Regularity contracts: the parent finite measurable nonempty State/Action,
  probability initial law, positive horizon/base floor, deterministic reward
  bound one, path support/full-exploration floor, and indexed Standard Borel
  batch/trajectory witnesses. The product coupling adds no cross-window law
  assumptions.
- Retrieval evidence: exact local common-space search returned no hit; the
  compiled episodewise all-window terminal is the parent; Mathlib
  `Probability.ProductMeasure` and `ConvergenceInMeasure` provide the product,
  marginal, and convergence APIs; `SCN-RL-MDP` and the UCB-VI paper card place
  the route; tail and optimism weapons are inspiration only.
- Status: `leanCompiled`; seventeen registered declarations expose realized
  regret measurability, expected-regret nonnegativity, absolute realized transport, the finite-window absolute
  terminal, dependent window/source/law/common-measure/process/bad-event APIs,
  measurable process coordinates, exact marginals, the common-event tail,
  outside-event absolute control, and the final
  measurability-plus-marginals-plus-`TendstoInMeasure` theorem. Focused module
  (3043 jobs), root (3529 jobs), Tests (3531 jobs), and typed external canaries
  compile. Placeholder/JSON/declaration checks pass; five representative axiom
  audits are baseline-only; `tools/bandit.py check` passes with 17 CLI tests and
  one expected skip.
- Failure policy: this is an explicit independent-coordinate coupling of the
  finite-window experiments, not the natural nested online algorithm on one
  shared data stream. Do not infer pathwise, almost-sure, anytime, stochastic
  reward, minimax, or complete UCB-VI conclusions.

## Compiled Theorem Route: Episodewise Decaying-Exploration Realized Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: replace the coarse whole-batch return proxy by the sum of
  independent centered episode-return proxies, transport that sharper MGF
  through the adaptive successor law, and expose finite-window plus all-window
  decaying-exploration realized-behavior consistency terminals with the sharp
  normalized return radius.
- Supporting leaves: independence of complete episode rows under
  `iidEpisodeBatchMeasure`; episode-return mean and bounded centered MGF;
  `episodes*horizon^2` batch proxy; successor `condExpKernel` law transport;
  `rounds*episodes*horizon^2` cumulative proxy and strongly-adapted tail;
  sharp return bad event and expected-to-realized transport; exact normalized
  radius, scalar limits, named violation set, and indexed all-window source.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeDecayingExplorationRealizedBehaviorConsistency`,
  `iidTrajectoryFamilyMeasure`, `iidEpisodeBatchMeasure`,
  `iIndepFun_pi`, `iIndepFun.comp`,
  `iIndepFun_iff_map_fun_eq_pi_map`,
  `HasSubgaussianMGF.sum_of_iIndepFun`,
  `boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`,
  `hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq`,
  `condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted`, and the
  compiled realized-regret decomposition and decaying source parent.
- Proof route: expose the whole generated episode row as one measurable product
  coordinate; transfer product-coordinate independence through the mapped batch
  law; compose with `episodeReturn`; center each episode by its common policy
  trajectory mean and apply bounded Hoeffding on `[-H,H]`; sum independent MGFs;
  rewrite the sum as centered `totalReturn`; reuse the existing total-return
  `condExpKernel` identification; run the strongly-adapted successor sum tail;
  union it with the count event; normalize by `episodes*rounds`; then package the
  sharp finite-window and indexed all-window terminals.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; probability initial law; positive
  episodes/rounds/horizon and base visit floor where division/positivity is used;
  deterministic rewards bounded in absolute value by one; fixed-window
  Standard Borel batch/trajectory instances; full-exploration path support and
  indexed Borel witnesses only at the concrete decaying source terminal.
- Retrieval evidence: exact `search-memory "episode return subgaussian"` no-hit;
  local iid episode batch, episode return, coarse realized transport, and
  decaying-consistency declarations; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, and
  Mathlib independence/product-measure APIs; UCB-VI/scenario cards are route
  evidence only and concentration weapons remain inspiration only.
- Status: `leanCompiled`; 33 declarations close whole-episode independence,
  sharp batch and cumulative MGFs, adaptive conditional transport, finite-window
  tail/regret transport, exact normalized radius and scalar limits, the named
  violation set, and the indexed all-window source terminal. Focused/root/Tests
  builds, numeric and typed external canaries, clean placeholder scan, complete
  declaration retrieval, four baseline-only axiom audits, and the full
  `tools/bandit.py check` gate pass.
- Failure policy: do not assume stagewise independence within an episode. The
  independence index is episodes, each summand is one complete trajectory
  return, and successor coordinates remain `1..rounds`. Preserve two confidence
  shares and changing sample-space semantics. Do not infer stochastic rewards,
  common-space convergence, pathwise/a.s./anytime control, minimax rates, or a
  complete UCB-VI theorem.

## Compiled Theorem Route: Decaying-Exploration Realized Behavior Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: simplify the finite-window whole-batch return proxy,
  prove the normalized successor-return radius tends to zero under the
  compatible decaying schedule, combine it with the expected behavior bound
  and doubled failure budget, name the realized violation set, and expose an
  all-window dependent-family source theorem retaining optimism.
- Supporting leaves: exact batch and cumulative proxy casts; normalized-radius
  definition, nonnegativity, and exact cancellation; elementary log/power
  envelope; scheduled episode positivity; radius/envelope Tendsto; realized
  bound and doubled `ENNReal` budget limits; violation containment and
  `measure_mono`; indexed Standard Borel all-window transport.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeRealizedBehaviorRegret`,
  `batchReturnVarianceProxy`, `cumulativeSuccessorReturnVarianceProxy`,
  `subGaussianSumConfidenceRadius_sq`, `Real.log_le_sub_one_of_pos`,
  `Real.sqrt_le_iff`, `pow_le_pow_right₀`, `squeeze_zero`,
  `tendsto_const_nhds.div_atTop`, `nhds_prod_eq`, `measure_mono`, and the
  compiled decaying expected-behavior and finite-window realized terminals.
- Proof route: show the proxy casts are `(episodes*H)^2` and
  `rounds*(episodes*H)^2`; use nonnegative square equality to cancel episodes
  from the normalized radius; under `q=n+2`, bound `log(2q)` by `2q` and use
  `q^(H+4)` to obtain `radius<=2H/q`; squeeze to zero; add the expected bound;
  add the two failure shares; include the named violation set in the combined
  event; quantify all windows with indexed Borel witnesses.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; probability initial law; positive
  horizon/base floor; deterministic absolute reward bound one; full-exploration
  path support; one `StandardBorelSpace` witness for every scheduled batch and
  trajectory type. Proxy algebra and scalar limits use fewer contracts through
  explicit `omit` blocks.
- Retrieval evidence: exact `search-memory` no-hit; compiled realized-regret
  and decaying expected-behavior local cards; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, and
  `MLIB-FINSET-SUMS`; `SCN-RL-MDP`, UCB-VI/textbook cards as route evidence;
  tail/optimism weapons are inspiration only.
- Status: `leanCompiled`; nineteen declarations, focused/root/Tests builds,
  exact positive-parameter, nonzero-horizon envelope, doubled-budget, strict
  violation-membership, and full typed all-window canaries pass. Placeholder
  scanning and four baseline-only axiom audits pass. Independent review found
  no theorem defect; its multiline result-level `letI` retrieval finding is
  fixed and regression-tested. Generated indexes and the blueprint retain the
  complete terminal statement. The final repository gate passes with root and
  Tests builds plus 17 CLI tests with one expected skip.
- Failure policy: preserve the two delta shares, successor coordinates
  `1..rounds`, coarse whole-batch proxy, and changing sample-space semantics.
  The theorem proves a joint scalar limit and every finite-window certificate,
  not convergence in probability, pathwise/almost-sure convergence, a common
  coupling, sharper episode concentration, stochastic rewards, anytime
  control, minimax rates, or complete UCB-VI.

## Compiled Theorem Route: Finite-Window Realized Behavior Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT`.
- Lean-facing target: on one fixed adaptive finite-window
  `EpisodeBatchTrajectory` law, define the recorded successor-batch return and
  realized exploratory-behavior regret; center every successor return by its
  prefix-kernel integral; prove a conditional Hoeffding/Azuma tail; and combine
  that event with the compiled cumulative-count event so realized average
  regret is bounded by the expected behavior certificate plus an explicit
  reward-deviation radius.
- Supporting leaves: measurable episode/batch return; generated trajectory
  return identity; iid batch-return mean equals `episodes` times the policy
  trajectory mean; bounded centered batch-return MGF; generic measurable
  successor-statistic `condDistrib`/`condExpKernel` transport; strongly adapted
  return increments; finite-sum tail; exact expected-to-realized regret
  decomposition; union-event source endpoint.
- Local APIs/imports: `MDP.cumulativeReward`,
  `MarkovPolicy.integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero`,
  `MarkovPolicy.expectedRegret`, `iidEpisodeBatchMeasure`,
  `AdaptiveEpisodeBatchSource.trajectoryMeasure_condDistrib`,
  `ConditionalExpectationReward.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq`,
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`,
  `Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted`,
  `Filtration.piLE`, `integral_finset_sum`, `measure_union_le`, and the compiled
  exploratory-behavior source terminal.
- Intended proof route: sum recorded rewards within each episode and batch;
  identify generated episode returns with `MDP.cumulativeReward`; transport
  the trajectory expectation through the finite iid batch map; bound each
  batch return in `[-episodes*horizon, episodes*horizon]`; map the source
  successor conditional law through total return; obtain conditionally
  sub-Gaussian kernel-centered increments; apply the finite strongly-adapted
  sum theorem; algebraically rewrite realized regret as expected regret minus
  centered return noise; union the count and return bad events.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; probability initial law; Standard Borel
  batch and trajectory spaces; positive episodes and recommendation rounds;
  positive horizon; deterministic rewards bounded in absolute value by one;
  the existing path-support/calibration contracts enter only in the terminal
  source consumer.
- Retrieval evidence: exact local search found no finite-horizon RL realized
  regret declaration; the compiled adaptive count martingale module supplies
  the law-transport proof shape; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, and
  `MLIB-ORDER-ALGEBRA` are the Mathlib routes; UCB-VI/textbook/scenario cards
  are theorem-route evidence only; martingale/tail weapons are inspiration,
  not proof dependencies.
- Status: `leanCompiled`; `FiniteHorizonAdaptiveCumulativeRealizedBehaviorRegret`
  exposes forty-six declarations. The focused module, root import, and
  `Tests.Basic` compile, including an external finite-window source canary. The
  concrete decaying terminal retains optimism, bounds the count/return union by
  `ofReal delta_n + ofReal delta_n`, and adds the explicit normalized return
  radius to the expected behavior certificate. Explicit full-contract,
  nonzero-return, and coordinate-one canaries compile; four public axiom audits
  contain only `propext`, `Classical.choice`, and `Quot.sound`; independent
  review findings are resolved; generated indexes are refreshed; and the full
  `python3 tools/bandit.py check` gate passes.
- Failure policy: preserve the actual recorded successor batches, the exact
  prefix-conditioned iid law, and the distinction between expected and
  realized regret. Do not replace the adaptive law by independent rounds,
  silently count the initial batch as a recommendation round, infer a
  common-space theorem across changing schedules, or claim anytime/a.s.,
  stochastic-reward, minimax, or complete UCB-VI results. The whole-batch
  Hoeffding proxy is sufficient but deliberately not sharp in `episodes`.

## Compiled Theorem Route: Decaying-Exploration Behavior Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-BEHAVIOR-CONSISTENCY`.
- Lean-facing target: derive exact exploration-rate power scaling for the
  selected path-support state and visit floors; choose compatible exploration,
  recommendation-window, visit-floor, batch-size, and confidence schedules;
  prove the average exploratory-behavior expected-regret certificate and
  `ENNReal` failure budget tend jointly to zero; and instantiate the source
  event at every finite window.
- Supporting declarations: action/state/visit floor scaling; full-exploration
  floor transport; `decayingExplorationScale`, `decayingExplorationRate`,
  `decayingExplorationRounds`, `decayingExplorationVisitFloor`, and scheduled
  episodes; recommendation, behavior, and explicit envelope bounds; positivity
  and admissibility facts; the effective visit-mass identity; envelope,
  exploration-charge, behavior-bound, and joint limits; the named violation
  set; and the finite-window source terminal.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret`;
  `exploratoryPathStateLowerNat`; `ExploratoryPathUniformVisitFloor`;
  `pow_le_pow_of_le_one`; `Real.sqrt_mul`; `Real.sqrt_sq_eq_abs`;
  `tendsto_pow_atTop`; `Filter.Tendsto.inv_tendsto_atTop`, `div_atTop`,
  and `prodMk`; `measure_mono`; the scheduled recommendation source theorem;
  and the fixed-rate average behavior transport.
- Intended proof route: prove by induction that the selected state floor at
  stage `t` is multiplied by `gamma^t` and the visit floor by
  `gamma^(t+1)`; use `0<=gamma<=1` and `t+1<=horizon` for the uniform floor.
  Set `q_n=n+2`, `gamma_n=q_n^-1`, `rounds_n=q_n^(horizon+4)`, and
  `visitFloor_n=baseVisitFloor*gamma_n^horizon`. Simplify
  `visitFloor_n*rounds_n` to `baseVisitFloor*q_n^4`, rewrite the recommendation
  envelope as a constant over `q_n^2`, add the behavior charge over `q_n`, and
  squeeze to zero. Reuse the parent bad event and include behavior violations.
- Regularity contracts: finite measurable nonempty state/action with decidable
  equality and measurable singletons; probability initial law; positive
  horizon and positive base visit floor; one full-exploration path-support
  uniform visit-floor certificate; deterministic rewards bounded in absolute
  value by one; and Standard Borel witnesses for the changing scheduled batch
  and trajectory types at the finite window.
- Retrieval evidence: exact no-hit project-memory search; compiled local
  scheduled-average, vanishing-delta, and fixed-exploration behavior routes;
  `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, and `MLIB-PROBABILITY-KERNEL`; Slivkins/UCB-VI and
  `SCN-RL-MDP` as route evidence only; proof weapons are inspiration only.
- Status: `leanCompiled`; twenty-six declarations compile in the focused
  module, root import, and `Tests.Basic`. Unit canaries cover the explicit
  schedule, joint limit, source terminal, and typed source projections. A
  Bool-state/Bool-action horizon-two canary covers nondegenerate floor scaling
  and effective visit mass. Indexes, independent review, axiom audits, and the
  final repository gate are refreshed before handoff.
- Failure policy: the polynomial schedule is a sufficient consistency
  schedule, not a minimax or computational-efficiency claim. Every window has
  a different scheduled episode count and trajectory type. Do not infer
  violation-set measurability, a common process, TendstoInProbability,
  pathwise/almost-sure convergence, stochastic rewards, a minimax rate, or
  complete UCB-VI. A downstream finite-window realized-regret martingale
  transport now compiles, but its normalized reward radius and changing-space
  asymptotics remain separate.

## Compiled Theorem Route: Exploratory Behavior Expected-Regret Transport

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EXPLORATORY-BEHAVIOR-REGRET-TRANSPORT`.
- Lean-facing target: prove the exact exploratory PMF integral, bound the
  remaining-horizon policy value under deterministic rewards, and show actual
  exploratory-policy expected regret is at most deterministic recommendation
  regret plus `explorationRate*rewardBound*horizon*(horizon+1)`. Lift this to
  cumulative and positive-window average regret, then reuse the vanishing-delta
  source event to bound a named behavior-regret violation set.
- Supporting declarations: exact PMF apply/integral lemmas; bounded Bellman-Q,
  transition-value, and policy-value lemmas; deterministic/exploratory Bellman
  recursions; source `policyAt` successor alignment; value and expected-regret
  transport; the named charge; cumulative
  and average behavior regrets and bounds; fixed-rate limit; behavior violation
  set; and the finite-window source terminal.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtHighProbabilityAverageConsistency`;
  `PMF.integral_eq_sum`; `exploratoryActionPMF`; `exploratoryPolicy`;
  `MarkovPolicy.valueRemaining` and the expected-regret integral identity;
  `countRadiusOptimisticPolicyTable_toMarkovPolicy`; integral norm/monotonicity
  lemmas; `measure_mono`; and `Filter.Tendsto.add`.
- Intended proof route: expand the exploratory PMF as uniform weight
  `explorationRate` plus selected weight `1-explorationRate`; prove
  `|V_remaining|<=remaining*rewardBound`; propagate the selected/exploratory
  gap through transition kernels and Bellman recursion; sum the stage costs;
  sum over rounds and divide by positive rounds; include the behavior violation
  set in the already measured recommendation bad event.
- Regularity contracts: finite measurable nonempty state/action with decidable
  equality and measurable singletons; probability initial law; exploration
  rate at most one; deterministic reward absolute bound; positive rounds for
  the average theorem. The source terminal inherits positive horizon/floor,
  path support/common floor, and dependent Standard Borel scheduled spaces.
- Retrieval evidence: exact no-hit memory search; compiled local exploratory
  policy/source and scheduled-average routes; `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, `MLIB-ASYMPTOTICS`, and
  `MLIB-ORDER-ALGEBRA`; Slivkins/UCB-VI/scenario cards as route evidence;
  optimism/tail weapons as inspiration only.
- Status: `leanCompiled`; twenty declarations compile in the focused module,
  root import, and `Tests.Basic`. Unit and explicitly typed canaries cover the
  charge, successor coordinate alignment, average transport, source terminal,
  violation containment/tail, and good-side charged bound. A two-action
  one-step reward canary locks a nonzero value gap. Placeholder and public
  axiom audits, synchronized indexes, independent review/re-review, and the
  full root/Tests/CLI gate pass.
- Failure policy: fixed positive exploration leaves a nonzero residual charge,
  and the compiled bound tends to that charge rather than zero. The downstream
  compatible decaying-exploration support/calibration route now gives a
  zero-limit dependent finite-window consumer. Do not infer violation-set
  measurability, a common process, pathwise or realized regret, stochastic
  rewards, minimax rate, or complete UCB-VI.

## Compiled Theorem Route: Vanishing-Delta High-Probability Average Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-VANISHING-DELTA-HIGH-PROBABILITY-AVERAGE-CONSISTENCY`.
- Lean-facing target: set `delta_n=1/(n+2)`, `rounds=n+1`, and use the
  existing explicit scheduled episodes at that delta. Prove the real and
  `ENNReal` failure budgets tend to zero, the varying average recommendation
  certificate tends to zero, and both converge jointly. Name the
  average-regret violation set, prove it is included in the measurable parent
  bad event with outer measure at most `delta_n`, retain optimism outside the
  event, and package every window with explicit dependent Standard Borel
  witnesses.
- Supporting declarations: `vanishingAverageConfidenceDelta`;
  `vanishingDeltaScheduledEpisodes`;
  `vanishingDeltaScheduledAverageRecommendedExpectedRegretBound`; delta
  positivity/boundedness/real/ENNReal limits; varying-bound nonnegativity,
  envelope and limit; joint product limit;
  `vanishingDeltaScheduledAverageRegretViolationSet`; the per-window terminal;
  and its `_allWindows` dependent-family wrapper.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtAverageConsistency`;
  `tendsto_const_div_atTop_nhds_zero_nat`;
  `Filter.tendsto_add_atTop_nat`; `ENNReal.continuous_ofReal`;
  `Filter.Tendsto.prodMk`; `nhds_prod_eq`; `squeeze_zero`;
  `MeasureTheory.measure_mono`; and the compiled scheduled source terminal.
- Intended proof route: establish `0<delta_n<=1`; compose the standard
  constant-over-natural limit with `n+2`; transport it through
  `ENNReal.ofReal`; squeeze the varying-delta certificate under the parent's
  delta-independent inverse-root envelope; combine both limits in the product
  topology. At each source window, specialize the parent theorem, use its
  good-side average inequality to include the violation set in the bad event,
  apply `measure_mono`, and quantify explicit Borel witnesses for each changing
  sample space.
- Regularity contracts: finite measurable nonempty state/action with
  decidable equality and measurable singletons; probability initial law;
  positive horizon and visit floor; path support/common visit floor;
  exploration probability at most one; deterministic rewards bounded in
  absolute value by one; one Standard Borel witness for every scheduled batch
  and trajectory type. No common sample space, summable anytime budget,
  stochastic reward law, behavior-regret, or realized-regret premise is added.
- Retrieval evidence: compiled scheduled-average, average, and normalized
  local cards; `TXT-SLIVKINS-2019-2024`,
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`, and `SCN-RL-MDP` as route evidence;
  `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, and `MLIB-PROBABILITY-KERNEL`; exact local
  declaration lookup and no prior memory hit. Optimism and tail weapons are
  inspiration only.
- Status: `leanCompiled`; fourteen declarations compile in the focused module,
  root import, and `Tests.Basic`. Unit canaries check `delta_0=1/2`,
  `delta_2=1/4`, the joint limit, a nontrivial `n=2` source terminal, and the
  explicit all-window Borel-witness interface. Typed projection canaries lock
  violation containment/tail, good-side optimism/average regret, and the
  all-window `forall n` certificate. Placeholder/axiom audits and indexes pass;
  independent review found no P0-P2 and its P3 inferred-canary gap is resolved.
  The full root/Tests/CLI gate passes.
- Failure policy: the source measures and trajectory types vary with `n`, so
  this is a dependent family of finite-window high-probability certificates,
  not one-process convergence in probability, pathwise convergence, or an
  almost-sure theorem. `1/(n+2)` is nonsummable and does not create an anytime
  event. Do not relabel recommended-policy expected regret as exploratory
  behavior or realized regret. Fixed-rate exploratory-behavior transport and
  its compatible decaying-exploration support/calibration consumer now compile
  downstream. The next exact boundary is an explicit common-space
  embedding/coupling or realized-regret martingale transport;
  the violation set itself has an outer-measure bound but no compiled
  measurability theorem. No stochastic rewards, minimax rate, or complete
  UCB-VI is claimed.

## Compiled Theorem Route: Scheduled Average Adaptive Cumulative Inverse-Sqrt Consistency

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-SCHEDULED-AVERAGE-CONSISTENCY`.
- Lean-facing target: with
  `L = cumulativeInverseSqrtLogFactor mdp rounds delta` and normalized
  threshold `T`, define the real schedule target
  `max T (2*L/visitFloor)` and the natural batch size
  `Nat.ceil(target)+1`. Prove that it clears calibration, satisfies
  `L < episodes*visitFloor/2`, bounds the average recommendation guarantee by
  `16*card(State)*horizon^2/(sqrt(visitFloor)*sqrt(rounds))`, and makes the
  scalar bound tend to zero along `rounds=n+1`. Instantiate the same-event
  source terminal separately at every positive finite window.
- Supporting declarations:
  `normalizedCumulativeInverseSqrtScheduledEpisodeThreshold`;
  `normalizedCumulativeInverseSqrtScheduledEpisodes`;
  `normalizedCumulativeInverseSqrtScheduledAverageEnvelope`;
  `cumulativeInverseSqrtLogFactor_pos`; strict schedule/calibration and
  log-mass lemmas; bound nonnegativity/envelope/Tendsto theorems; and
  `exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_scheduledAverageRecommendedExpectedRegret`.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtAverageRate`;
  `normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound_eq_totalEpisodes`;
  `Nat.le_ceil`; `Real.log_pos`; `Real.sqrt_le_sqrt`; `Real.sqrt_mul`;
  `Real.tendsto_sqrt_atTop`; `tendsto_natCast_atTop_atTop`;
  `Filter.Tendsto.div_atTop`; `squeeze_zero`; ordered-field algebra; and the
  compiled average source terminal.
- Intended proof route: use the strict ceil successor to dominate both max
  branches. Cross-multiply the positive visit floor to obtain
  `L<episodes*visitFloor/2`; compare square roots; factor total visit mass as
  `(episodes*visitFloor/2)*rounds`; cancel the bounded square-root ratio; and
  squeeze the scalar average bound under the explicit inverse-root envelope.
  Invoke the parent source terminal with the schedule's positivity and strict
  threshold witnesses.
- Regularity contracts: finite measurable nonempty state/action with
  decidable equality and measurable singletons; probability initial law;
  Standard Borel spaces for each scheduled batch and trajectory; positive
  horizon, rounds, visit floor, and delta; delta at most one; path support and
  a common visit floor; deterministic rewards bounded in absolute value by
  one. No new reward law, independence, filtration, or integrability premise
  is introduced.
- Retrieval evidence: compiled average, normalized, and explicit local cards;
  `TXT-SLIVKINS-2019-2024`, `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`, and
  `SCN-RL-MDP` as route evidence; `MLIB-REAL-LOG-SQRT`,
  `MLIB-ASYMPTOTICS`, `MLIB-ORDER-ALGEBRA`, `MLIB-FINTYPE-FIN`,
  `MLIB-MEASURE-INTEGRAL`, and `MLIB-PROBABILITY-KERNEL`; direct Mathlib
  ceil/Tendsto/squeeze APIs; optimism and tail weapons are inspiration only.
  Exact memory search found no matching schedule route.
- Status: `leanCompiled`; fourteen declarations compile in the focused module,
  root import, and `Tests.Basic`. Unit canaries at `delta=1/2` check positivity,
  strict threshold clearance, log-mass coverage, the exact four-round envelope
  value eight, scalar convergence, and the full per-window source terminal.
  Placeholder scan is clean and both main public axiom audits are baseline-only.
  Two time-bounded read-only agent reviews returned no report and are not
  counted; an independent local statement/algebra/sample-space audit found no
  issue. The full root/Tests/CLI gate passes.
- Failure policy: the convergence theorem concerns the deterministic scalar
  bound. Because `episodes(n)` changes `EpisodeBatchTrajectory`, the source
  theorem is intentionally finite-window and does not assert convergence on
  one fixed sample space. Do not claim convergence in probability, almost-sure
  consistency, stochastic rewards, exploratory behavior or realized regret,
  a minimax rate, or complete UCB-VI. The downstream decaying-confidence
  family, fixed-exploration behavior transport, and compatible decaying-
  exploration support/calibration consumer now compile; a common-space
  embedding or realized-regret martingale transport remains separate.

## Compiled Theorem Route: Average Adaptive Cumulative Inverse-Sqrt Recommendation Rate

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-AVERAGE-RECOMMENDATION-RATE`.
- Lean-facing target: define the average of
  `adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret` over a
  positive number of recommendation rounds, divide the compiled normalized
  scalar bound by the same round count, and prove the exact expansion
  `2*horizon * min 1
    (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor) /
      sqrt((episodes*rounds)*visitFloor/2))`, where `episodes*rounds` is the
  total number of exploratory episodes in all observed batches.
- Supporting declarations:
  `AdaptiveEpisodeBatchSource.cumulativeExploratoryEpisodeCount`;
  `.normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound`;
  `.normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound_eq_totalEpisodes`;
  `adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret`; and
  the same-event source terminal ending in
  `normalizedAverageRecommendedExpectedRegret`.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtNormalizedRate`;
  `normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound_eq`;
  `Real.sqrt_mul`, `Real.sqrt_pos`, `Real.sq_sqrt`;
  `min_div_div_right`; `Nat.cast_mul`; ordered-field division; and the
  compiled normalized source terminal.
- Intended proof route: unfold both average definitions; distribute division
  over the outer horizon factor; use positive rounds to rewrite
  `min rounds x / rounds` as `min 1 (x/rounds)`; identify
  `sqrt(rounds)*sqrt(episodes*visitFloor/2)` with
  `sqrt((episodes*rounds)*visitFloor/2)`; cancel the remaining positive square
  root. Divide the parent recommendation-regret inequality by positive rounds
  without changing the event, tail, or optimism conjuncts.
- Regularity contracts: the parent finite measurable nonempty state/action,
  probability initial law, Standard Borel batch/trajectory, exploratory path
  support, normalized reward, delta, visit-floor, and episode-threshold
  contracts; additionally, positive rounds and episodes justify all average
  and square-root cancellations. No new law, measurability, or integrability
  premise is introduced.
- Retrieval evidence: the compiled normalized and explicit-rate local cards;
  `TXT-SLIVKINS-2019-2024` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `SCN-RL-MDP`; `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-PROBABILITY-KERNEL`; UCB optimism and tail weapons are inspiration
  only. Exact local memory search found no existing finite-horizon adaptive
  total-episode average-recommendation route.
- Status: `leanCompiled`; the focused module, root, and `Tests.Basic` builds
  pass. Five public declarations compile. The Unit-MDP canary uses three
  rounds, 1000 episodes per batch, total exploratory count 3000,
  `delta=1/2`, and visit floor one; it checks the exact average expansion and
  invokes the full same-event source terminal. The two public theorem axiom
  audits are baseline-only. Independent local review found no P0-P3 and
  confirmed the inclusive-prefix count, exact algebra, unchanged event, and
  recommendation-only semantics; the zero-reward Unit witness does not test
  nonzero regret or reachability.
- Failure policy: preserve the exact cumulative recommendation sum divided by
  rounds, the inclusive cumulative prefix semantics, and the unchanged global
  event. Do not identify this average recommendation error with exploratory
  behavior or realized regret. Its downstream explicit integer schedule and
  scalar consistency theorem now compile; do not retroactively treat this
  parent finite-window theorem as a process-level or minimax UCB-VI result.

## Compiled Theorem Route: Normalized Adaptive Cumulative Inverse-Sqrt Rate

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-NORMALIZED-RATE`.
- Lean-facing target: specialize the compiled explicit-rate endpoint to
  normalized deterministic rewards `|reward| <= 1`, zero-count budget `1`,
  and
  `scale = 4*card(State)*horizon*sqrt(L)/sqrt(visitFloor)`, where
  `L = cumulativeInverseSqrtLogFactor mdp rounds delta`. Replace both prior
  scalar calibration premises by the single sufficient threshold
  `32*card(State)^2*horizon^2*L/visitFloor^2 < episodes`, and expose the
  same-event recommendation-regret bound
  `2*horizon * min rounds
    (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor)*sqrt(rounds) /
      sqrt(episodes*visitFloor/2))`.
- First supporting lemmas:
  `normalizedCumulativeInverseSqrtScale_nonneg`;
  `normalizedCumulativeInverseSqrtScale_cover`; and
  `cumulativeInverseSqrtCalibrationEpisodeThreshold_lt_of_normalizedThreshold`.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtExplicitRate`;
  `cumulativeInverseSqrtLogFactor_nonneg`;
  `cumulativeInverseSqrtCoverCoefficient`;
  `cumulativeInverseSqrtPathCalibration_of_episodeThreshold`;
  the compiled closed-form terminal; `Fintype.card_pos_iff`;
  `Real.sqrt_nonneg`, `Real.sqrt_pos`, `Real.sq_sqrt`; and ordered-field
  square/division algebra.
- Intended proof route: use nonempty finite state space and positive horizon to
  show the normalized scale is nonnegative. Rewrite the cover coefficient at
  reward bound and budget one to `4*card(State)*horizon`; square the normalized
  scale, cancel the positive visit-floor square root, and obtain the scale
  cover with equality. Show the first branch of the old max threshold is
  dominated by the normalized coefficient and the second branch is exactly
  the normalized threshold. Invoke the compiled explicit calibration and
  terminal, then normalize the general closed-form bound by ring algebra.
- Regularity contracts: finite measurable nonempty state/action spaces with
  decidable equality and measurable singletons; probability initial law;
  Standard Borel batch/trajectory spaces; positive horizon, rounds, episodes,
  visit floor, and delta with `delta <= 1`; exploratory path support/common
  visit floor; deterministic rewards bounded in absolute value by one; and the
  single normalized episode threshold above.
- Retrieval evidence: compiled explicit-rate and capped path-support local
  cards; `TXT-SLIVKINS-2019-2024` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `SCN-RL-MDP`; `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-PROBABILITY-KERNEL`; `WEAPON-UCB-OPTIMISM` and
  `WEAPON-TAIL-INEQUALITIES` are inspiration only. Exact local memory search
  found no existing normalized cumulative inverse-square-root route.
- Compiled declarations:
  `AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScale`;
  `.normalizedCumulativeInverseSqrtEpisodeThreshold`;
  `.normalizedCumulativeInverseSqrtCountRadius`;
  `.normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound`;
  `.normalizedCumulativeInverseSqrtScale_nonneg`;
  `.normalizedCumulativeInverseSqrtScale_cover`;
  `.cumulativeInverseSqrtCalibrationEpisodeThreshold_le_normalized`;
  `.cumulativeInverseSqrtCalibrationEpisodeThreshold_lt_of_normalizedThreshold`;
  `.normalizedCumulativeInverseSqrtPathCalibration_of_episodeThreshold`;
  `.normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound_eq`; and
  `AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_normalizedRecommendedExpectedRegret`.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds pass. The Unit-MDP
  canary uses three rounds, `delta=1/2`, local delta `1/12`, `L<23`, 1000
  episodes, and visit floor one; it closes the normalized threshold,
  calibration, explicit bound expansion, and full source terminal.
- Failure policy: preserve normalized reward semantics, accumulated adaptive
  counts, the existing single measurable event, and recommendation-policy
  expected regret. If the constant `32` does not dominate both old threshold
  branches, record the exact scalar counterexample rather than weakening the
  endpoint. This route does not model stochastic rewards, identify exploratory
  behavior or realized regret, establish a minimax rate, or complete UCB-VI.
  Its downstream average-rate route now divides by positive rounds and
  exposes total exploratory episodes. The next boundary is an integer
  batch-size schedule satisfying calibration with vanishing average
  recommendation error, without reopening the probability law.

## Compiled Theorem Route: Explicit Adaptive Cumulative Inverse-Sqrt Rate

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-EXPLICIT-CALIBRATION-RATE`.
- Lean-facing target: eliminate the caller-supplied roundwise
  `CumulativeInverseSqrtPathCalibration` from the capped path-support terminal.
  Write `L = log(2 / cumulativeCountLocalDelta)` and
  `C = 2 * card(State) * horizon * (rewardBound + budget)`. From
  `max (2*L/visitFloor^2)
    (2*C^2*L/(budget^2*visitFloor^2)) < episodes` and
  `C^2*L <= scale^2*visitFloor`, construct the complete two-scale calibration,
  sum the round envelopes, and prove recommended-policy expected regret at most
  `2*horizon * min (rounds*budget)
    (2*scale*sqrt(rounds)/sqrt(episodes*visitFloor/2))` on the same good event.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeInverseSqrtCalibration`;
  `Concentration.subGaussianSumConfidenceRadius_sq`;
  `MarkovPolicy.iidBernoulliVarianceProxy_eq`;
  `Real.sqrt_le_sqrt`, `Real.sq_sqrt`, `sq_lt_sq₀`, `sq_le_sq₀`;
  finite `Fin` sums; and the compiled cross-domain scalar lemma
  `Tsallis.sum_range_one_div_sqrt_natSucc_le_two_sqrt`.
- Intended proof route: compute the exact prefix-radius square
  `r_k^2 = k*episodes*L/2`. The first threshold branch implies
  `k*episodes*visitFloor/2 < lowerMargin_k`. The second branch compares squares
  to prove `C*r_k < budget*(k*episodes*visitFloor/2)`, hence `coverBudget`.
  Multiplying the separate scale-square condition by `k*episodes/2` and using
  the same lower margin proves `coverScale`. Construct the parent calibration;
  dominate every capped envelope both by `budget` and by
  `(scale/sqrt(episodes*visitFloor/2))/sqrt(k)`; sum the shifted inverse roots;
  then compose with the existing terminal without changing its event or delta.
- Regularity contracts: finite measurable nonempty state/action spaces with
  decidable equality and measurable singletons; probability initial law;
  Standard Borel batch/trajectory spaces; positive horizon, rounds, episodes,
  visit floor, budget, and global delta with `delta <= 1`; nonnegative scale;
  exploratory path support/common visit floor; known deterministic reward
  bound; the explicit episode threshold and scale-square condition above.
- Retrieval evidence: the compiled capped path-support calibration and
  cumulative count-martingale routes; `LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-OPTIMIZATION`
  only for its local scalar finite-sum lemma; `MLIB-REAL-LOG-SQRT`,
  `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-PROBABILITY-KERNEL`; UCB-VI literature is route evidence only and proof
  weapons remain inspiration only.
- Compiled declarations:
  `AdaptiveEpisodeBatchSource.cumulativeInverseSqrtLogFactor`;
  `.cumulativeInverseSqrtCoverCoefficient`;
  `.cumulativeInverseSqrtCalibrationEpisodeThreshold`;
  `.cumulativeCoordinateConfidenceRadius_sq_eq`;
  `.half_cumulativePathVisitExpectedFloor_lt_lowerMargin_of_episodeThreshold`;
  `.cumulativeInverseSqrtPathCalibration_of_episodeThreshold`;
  `.cumulativeInverseSqrtEnvelopeSumBound`;
  `.sum_cumulativeInverseSqrtRadiusEnvelope_le_explicit`;
  `.cumulativeInverseSqrtRecommendedExpectedRegretBound`;
  `.sum_horizon_mul_two_cumulativeInverseSqrtRadiusEnvelope_le_explicit`; and
  `AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_closedFormRecommendedExpectedRegret`.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds expose the public
  route, the positive Unit instance closes threshold/calibration/sum/terminal
  composition, and an exact `Fin 3` canary expands the shifted inverse-root
  indices `1,2,3`. The Unit terminal uses `delta=1` only as a satisfiability
  witness, not as evidence for a nontrivial probability tail. Placeholder and
  baseline-axiom audits plus independent local review pass.
- Failure policy: the endpoint is finite-window recommended-policy expected
  regret under explicit path support and known deterministic rewards. It does
  not choose or optimize `budget` and `scale`, identify exploratory behavior or
  realized regret, add stochastic-reward confidence, establish a minimax rate,
  or complete UCB-VI. The next route should instantiate/optimize the two scale
  parameters against `C` and `L`, not reopen the cumulative probability law.

## Compiled Theorem Route: Adaptive Cumulative Inverse-Sqrt Path-Support Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-PATH-SUPPORT-REGRET`.
- Lean-facing target: define a concrete nonnegative antitone count radius equal
  to `budget` at zero visits and
  `min budget (scale / sqrt(count))` at positive visits;
  use `ExploratoryPathUniformVisitFloor` to lower-bound every adaptive batch's
  predictable visit mean; accumulate that lower bound across each prefix; use
  the compiled cumulative martingale event to lower-bound realized visit
  counts; discharge `AdaptiveCumulativeCountMartingaleCover` from one
  deterministic roundwise two-scale calibration; bound every selected radius by
  a deterministic capped inverse-square-root round envelope; and invoke the concrete
  exploratory optimism/recommended-policy expected-regret terminal.
- Local APIs/imports:
  `FiniteHorizonAdaptiveCumulativeCountMartingaleConfidence`;
  `FiniteHorizonExploratoryPathSupportExplicitCalibration`;
  `TransitionCountRadius`; `Real.sqrt_le_sqrt`; `Real.sq_sqrt`;
  `DeterministicMarkovPolicyTable.uniformVisitFloor_expectedCount_le`;
  `AdaptiveEpisodeBatchSource.coordinateMeanAt` and
  `.cumulativeCoordinateMean`; cumulative visit raw-count/deviation identities;
  `TransitionCountSummary.countRadiusOptimisticPlan_selectedRadiusRemaining`;
  finite sums; ordered-field division; and the compiled generic/concrete
  cumulative-martingale terminals.
- Intended proof route: prove antitonicity of the zero/positive capped
  inverse-sqrt radius by splitting the left count at zero. Identify the cumulative source's
  initial and successor policy means with exploratory tables, apply the common
  path-support expected-count floor at each batch, and sum. Outside the global
  bad event, convert the absolute visit deviation into
  `prefixExpectedFloor - radius < realizedVisitCount`. A deterministic
  calibration records positivity of this lower margin and the scalar inequality
  needed both for the constant cap and after multiplying by
  `sqrt(realizedVisitCount)`. Use them to prove the finite next-state cover and
  selected-radius envelope, then instantiate
  the existing concrete source terminal without a new failure event.
- Regularity contracts: finite measurable nonempty state/action spaces with
  decidable equality and measurable singletons; probability initial law;
  Standard Borel batch and trajectory spaces; positive horizon/rounds/episodes;
  `0 < delta <= 1`; explicit default state; exploration rate at most one;
  an `ExploratoryPathSupport` certificate and positive uniform visit floor;
  nonnegative reward bound, zero-count budget, and inverse-sqrt scale; known
  reward bound; and one roundwise deterministic calibration comparing the
  cumulative count radius, visit floor, state cardinality, horizon, cap, and
  value envelope.
- Retrieval evidence: compiled cumulative count-martingale producer and
  cumulative contract terminal; compiled path-support expected-count floor;
  `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`,
  `MLIB-MEASURE-INTEGRAL`, and `MLIB-PROBABILITY-KERNEL`;
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` is route evidence only;
  `WEAPON-UCB-OPTIMISM` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.
- Compiled declarations:
  `TransitionCountRadius.cappedInverseSqrt`;
  `AdaptiveEpisodeBatchSource.CumulativeInverseSqrtPathCalibration`;
  `AdaptiveCumulativeEmpiricalOptimisticSource.exploratorySource_coordinateMeanAt_visit_ge_pathFloor`;
  `.exploratorySource_cumulativeCoordinateMean_visit_ge_pathFloor`;
  `.exploratorySource_cumulativePathVisitLowerMargin_lt_visitCount`;
  `.exploratorySource_adaptiveCumulativeCountMartingaleCover_of_pathSupport_inverseSqrtCalibration`;
  `.adaptiveCumulativeEmpiricalOptimisticPlanAt_selectedRadiusRemaining_le_inverseSqrtEnvelope`;
  and
  `.exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_explicitRecommendedExpectedRegret`.
- Status: `leanCompiled`.
- Failure policy: do not assume zero visits away, replace accumulated adaptive
  counts by one iid batch, or identify recommendation regret with exploratory
  behavior/realized regret. The rejected one-scale radius
  `budget / sqrt(count)` made the Unit zero-reward cover asymptotically require
  `2 * radius <= sqrt(margin)`, which is false for the current two-sided tail
  constant. Preserve the capped two-scale repair and its explicit positive
  Unit calibration witness. The downstream explicit-calibration/rate route now
  constructs this calibration and closes the finite sum from deterministic
  episode and scale inequalities. Remaining work is parameter choice/tuning,
  not a radius-definition-only leaf or a claimed minimax/complete UCB-VI rate.

## Compiled Theorem Route: Adaptive Cumulative Count Martingale Confidence Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-MARTINGALE-CONFIDENCE-REGRET`.
- Lean-facing target: for every finite visit or joint-transition coordinate,
  center each adaptive episode-batch raw count by its history-kernel integral;
  prove the successor increments conditionally sub-Gaussian with total
  Bernoulli proxy `episodes / 4`; derive two-sided concentration for every
  cumulative prefix; take one finite union over rounds and coordinates; use
  the resulting count deviations to construct
  `AdaptiveCumulativeCoordinateConfidenceContract`; and invoke the compiled
  optimism/recommended-regret terminal.
- Local APIs/imports: `FiniteHorizonAdaptiveCumulativeEmpiricalOptimisticRegret`;
  `CountCoordinate`; `MarkovPolicy.iidBernoulliVarianceProxy`;
  `HasSubgaussianMGF.sum_of_iIndepFun`; `Filtration.piLE`;
  `AdaptiveEpisodeBatchSource.trajectoryMeasure_condDistrib_eq_iidEpisodeBatchMeasure`;
  `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim`;
  `.hasCondSubgaussianMGF_centered_of_condExpKernel_map_eq`;
  `Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted`;
  finite union bounds; cumulative empirical-transition normalization; and the
  existing coordinate-confidence/regret consumer.
- Intended proof route: expose a measurable raw count and its selected-policy
  mean for each `CountCoordinate`; package the iid within-batch sum MGF; use
  `condDistrib_comp` and the real trimmed bridge to identify the next raw-count
  law; keep the predictable center as the measurable kernel integral so the
  source need not add measurability of `successorPolicy`; form the natural
  product filtration and apply the conditional sub-Gaussian sum theorem; union
  all fixed-prefix/fixed-coordinate tails; then combine visit and transition
  deviations with the exact transition-joint factorization and the realized
  cumulative denominator to build the planner confidence contract and terminal.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty state/action; probability
  initial law; Standard Borel episode batches/trajectories as required by
  regular conditional laws; positive rounds and episodes; `0 < delta <= 1`;
  known rewards; and explicit deterministic zero-count and positive-count
  transition-radius cover conditions for the caller's antitone count radius.
  The source's exact history-selected iid batch-kernel equality is reused;
  no measurable `successorPolicy` field is added.
- Retrieval evidence: compiled adaptive batch condDistrib law, real
  `condDistrib`/`condExpKernel.map` bridge, centered conditional-MGF consumer,
  iid Bernoulli count-indicator MGF, cumulative planner contract, and Mathlib
  `Filtration.piLE`/conditional sub-Gaussian sum APIs. Cards:
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MARTINGALE-STOCHASTIC`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-FINSET-SUMS`; `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` is route evidence and
  `WEAPON-TAIL-INEQUALITIES`/`WEAPON-UCB-OPTIMISM` are inspiration only.
- Compiled declarations: `CountCoordinate.deviation_hasSubgaussianMGF`;
  `AdaptiveEpisodeBatchSource.trajectoryMeasure_condDistrib_rawCount`;
  `.condExpKernel_map_rawCount_eq_batchKernel`;
  `.coordinateIncrement_succ_hasCondSubgaussianMGF`;
  `.trajectoryMeasure_cumulativeCoordinateDeviation_abs_tail_le`;
  `.trajectoryMeasure_adaptiveCumulativeCountBadEvent_le`;
  `.cumulativeEmpiricalTransitionMass_abs_sub_transition_lt`;
  `.coordinateConfidence_of_not_mem_adaptiveCumulativeCountBadEvent`;
  `.adaptiveCumulativeCoordinateConfidenceContract_of_martingale`; and the
  generic/concrete terminals ending in
  `_cumulativeCountMartingale_optimism_and_explicitRecommendedExpectedRegret`.
- Status: `leanCompiled`.
- Failure policy: do not replace the kernel-centered increment by an
  unmeasurable selected-policy center, collapse the accumulated tail back to
  independent latest-batch events, or claim behavior/realized regret, a
  minimax rate, or complete UCB-VI. If the route stops, record the exact failed
  `condDistrib`/`condExpKernel`, filtration, or ratio-cover declaration rather
  than weakening the theorem to a measurability-only leaf.

## Compiled Theorem Route: Adaptive Cumulative Count-Radius Contract Regret

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-RADIUS-CONTRACT-REGRET`.
- Lean-facing target: replace the latest-batch planner input by the sum of all
  transition counts in the observed finite prefix; prove that this summary and
  the resulting history-selected optimistic action table are measurable; use
  a nonnegative antitone count-radius object so every coordinate radius can
  shrink as cumulative visits increase; construct the corresponding adaptive
  iid batch source; and terminate at global optimism plus a finite sum of
  recommended-policy expected regrets bounded by
  `sum round, horizon * (2 * radiusEnvelope round)` under one explicit
  cumulative coordinate-confidence contract.
- Local APIs/imports: `FiniteHorizonAdaptiveEmpiricalOptimisticOccupancyEnvelope`;
  `EpisodeBatchPrefix`; `Preorder.frestrictLe`; `EpisodeBatch.transitionCount`;
  `MarkovPolicy.measurable_cast_transitionCount`; `TransitionCountSummary` and
  its empirical kernel; `empiricalFiniteBatchValueEnvelope`;
  `EstimatedModelPlan.CoordinateConfidence`;
  `MarkovPolicy.occupancySumRemaining_mono` and
  `.occupancySumRemaining_const`; `Kernel.ofFunOfCountable`, `Kernel.comap`,
  `Finset.range`, `Finset.sum_range_succ`, and finite sums of measurable maps.
- Intended proof route: sum every raw batch transition-count coordinate over
  `range (n + 1)` and transport measurability through the finite history
  projections. Normalize that cumulative summary with the existing empirical
  kernel. Define the transition radius as `countRadius.radius visitCount` and
  select the optimistic table from this plan; comap the existing table-indexed
  iid batch kernel along the cumulative selector. For the terminal, consume a
  family of coordinate-confidence witnesses outside one measurable bad event,
  apply the compiled one-round optimism/regret theorem at every round, bound
  each selected radius by a caller-supplied round envelope, use occupancy
  monotonicity and the exact constant-occupancy identity, and sum over rounds.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty State/Action where the empirical
  fallback and optimizer need them; probability initial law; a nonnegative
  antitone `Nat -> Real` count radius; measurable global bad event with an
  `ENNReal.ofReal delta` tail; roundwise cumulative `CoordinateConfidence`
  witnesses off that event; and a pointwise selected-plan radius envelope.
  Rewards remain known. Recommendation regret remains distinct from behavior
  and realized regret. No adaptive cumulative concentration producer,
  stochastic reward confidence, square-root/log rate, minimax theorem, or
  complete UCB-VI theorem is claimed.
- Retrieval evidence: exact local/memory search found no cumulative transition
  summary declaration. The latest-batch source exposes measurable history
  projection and table-indexed iid-kernel APIs; coordinate confidence already
  accepts arbitrary coordinate radii; occupancy monotonicity and the constant
  occupancy identity are compiled. Retrieved cards are `MLIB-FINSET-SUMS`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-CONDITIONAL-EXPECTATION`, and `MLIB-MARTINGALE-STOCHASTIC`, with
  `TXT-SLIVKINS-2019-2024`, `SCN-RL-MDP`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-UCB-OPTIMISM` and `WEAPON-TAIL-INEQUALITIES` are inspiration only.
- Status: `leanCompiled`; the cumulative prefix summary, its measurability and
  successor identity, monotone visit counts, shrinking count-radius theorem,
  count-radius empirical plan and zero-count value envelope, measurable
  exploratory source, global confidence contract, and explicit recommendation-
  regret terminal compile. Root and `Tests.Basic` builds pass. The Unit-MDP
  canary has cumulative visit counts `1` and `2` in its first two prefixes and
  `linearDecay 4` radii `3` and `2`; the source and terminal are instantiated
  externally. Placeholder scan is empty and eight key axiom audits report only
  `propext`, `Classical.choice`, and `Quot.sound`. This is a compiled cumulative
  planner/source and regret consumer under an explicit statistical contract,
  not a claim that the contract's adaptive martingale producer already exists.
- Failure policy: preserve actual prefix accumulation, history measurability,
  count antitonicity, and the unchanged recommended-regret terminal. If direct
  cumulative concentration cannot be derived from the current per-batch iid
  event, expose the missing conditional-centered count-MGF/martingale producer
  as the next exact blocker. Do not fall back to latest-batch counts, a fixed
  bonus, an unmeasurable selector, or theorem-card evidence presented as Lean.

## Compiled Theorem Route: Explicit Occupancy-Radius Envelope

- Route id:
  `RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-OCCUPANCY-RADIUS-ENVELOPE`.
- Lean-facing target: prove that a probability occupancy sum with constant
  stage cost `c` is exactly `remaining * c`; identify the selected radius of
  the known-reward empirical optimistic plan with its fixed transition bonus;
  derive
  `adaptiveEmpiricalOptimisticOccupancyRadiusSum =
    rounds * (2 * horizon * transitionBonus)`; and refine the compiled
  path-support episode-threshold terminal with the explicit recommended-policy
  expected-regret upper bound obtained by setting `transitionBonus = rewardBound`.
- Local APIs/imports: `FiniteHorizonExploratoryPathSupportEpisodeThreshold`;
  `MarkovPolicy.occupancySumRemaining` and `.occupancySumRemaining_succ`;
  `EstimatedModelPlan.selectedRadiusRemaining`;
  `TransitionCountSummary.optimisticPlan`;
  `adaptiveEmpiricalOptimisticPlanAt`;
  `adaptiveEmpiricalOptimisticOccupancyRadiusSum`; `integral_const` under
  `IsProbabilityMeasure`; probability preservation of induced state kernels;
  `Finset.sum_const`, `Fintype.card_fin`, and ordered semiring normalization.
- Intended proof route: induct on the remaining horizon and use that every
  induced state law remains a probability measure, so each constant integral
  is the same constant. Unfold the concrete optimistic plan to reduce
  `rewardRadius + transitionRadius` to `0 + transitionBonus`; substitute this
  into every round's occupancy term; evaluate the finite `Fin rounds` sum; then
  compose the exact identity with the existing episode-threshold global event.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty Action and an explicit default
  State; probability initial law. The generic occupancy identity uses only the
  probability-kernel contracts inherited by `MarkovPolicy`. The terminal keeps
  the episode-threshold route's positive horizon/rounds/episodes/visit-floor,
  valid delta, exploration-rate, path-support, and deterministic reward-bound
  assumptions. No accumulated statistics, count-dependent or decaying bonus,
  stochastic reward, behavior regret, realized regret, minimax rate, or
  complete UCB-VI theorem is claimed.
- Retrieval evidence: exact local/memory search found no constant-occupancy
  theorem; local declarations expose only `occupancySumRemaining_succ` and
  `.occupancySumRemaining_mono`; `MLIB-MEASURE-INTEGRAL`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, and
  `MLIB-ORDER-ALGEBRA`; `TXT-SLIVKINS-2019-2024`; `SCN-RL-MDP`;
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `WEAPON-UCB-OPTIMISM` as inspiration
  only.
- Status: `leanCompiled`; five public declarations compile. Focused/root/Tests
  builds pass. The Bool horizon-two, two-round, bonus-one canary proves the
  exact occupancy sum is `8` and the episode-threshold terminal gives
  recommended expected regret at most `8`. Placeholder scan is empty, all five
  declaration axiom audits contain only the baseline `propext`,
  `Classical.choice`, and `Quot.sound`, and independent local review found no
  P0-P3. The full gate passes with root 3514 jobs, Tests 3516 jobs, and 15 CLI
  tests with one expected skip.
- Failure policy: if exact constant integration or proof-dependent remaining
  indices obstruct reduction, retain a one-sided occupancy envelope with an
  explicit nonnegative bonus rather than weakening probability assumptions.
  Never describe this fixed-bonus linear envelope as a statistical regret rate;
  the next rate-bearing route must introduce accumulated cross-round counts and
  radii that shrink with those counts.

## Compiled Theorem Route: Path-Support Episode-Threshold Calibration

- Route id:
  `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EPISODE-THRESHOLD-CALIBRATION`.
- Concrete target: replace the compiled explicit-calibration endpoint's
  caller-supplied count-margin and half-contraction inequalities by one
  closed-form lower bound on the per-round episode count. The route must still
  construct `SourceCalibration` and return the unchanged global confidence,
  optimism, and recommended-policy expected-regret endpoint.
- Compiled Lean statements: the dimension factor
  `4 * card State * horizon + 1`; an explicit Real episode threshold using the
  simultaneous coordinate confidence share; a strict uniform-radius bound by
  `episodes * visitFloor / dimensionFactor`; automatic count margin and
  half-contraction; source calibration; and the final adaptive terminal.
- Local APIs/imports:
  `FiniteHorizonExploratoryPathSupportExplicitCalibration`,
  `Concentration.subGaussianSumConfidenceRadius_sq`,
  `MarkovPolicy.iidBernoulliVarianceProxy_eq`,
  `MarkovPolicy.simultaneousCountDelta_pos`,
  `MarkovPolicy.simultaneousCountDelta_le_one`,
  `multiBatchLocalDelta`, `sq_lt_sq₀`, `div_lt_iff₀`, and ordered-field
  arithmetic.
- Intended proof route: with
  `q = 4 * card State * horizon + 1`, rewrite the squared count radius as
  `episodes / 2 * log (2 / localCoordinateDelta)`. The threshold inequality
  gives `(q * radius)^2 < (episodes * visitFloor)^2`; nonnegativity then gives
  `radius < episodes * visitFloor / q`. Since `1 <= q`, this implies the strict
  count margin. Cross-multiplication in the positive denominator proves
  `card State * horizon * 2 * radius / (episodes * visitFloor - radius) <= 1/2`,
  so the compiled explicit-calibration source producer and terminal apply.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty Action and an explicit default
  State; probability initial law; positive horizon, rounds, episodes, and
  visit floor; `0 < delta <= 1`; exploration rate at most one; a valid path
  support certificate and common visit floor; deterministic reward absolute
  bound. No arbitrary-MDP support, accumulated cross-round counts, stochastic
  rewards, behavior/realized regret, occupancy-radius rate, or complete UCB-VI.
- Retrieval evidence: no exact local/memory route hit;
  `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`; compiled
  explicit path-support calibration declarations; `TXT-SLIVKINS-2019-2024`,
  `SCN-RL-MDP`, `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; and
  `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; eight public declarations compile. The Bool
  horizon-two canary proves `q=17`, local coordinate delta `1/96`, and
  `9248*log(192)<2^22`, then constructs the combined margin/contraction,
  positive bonus-one cover, `SourceCalibration`, and final terminal. Focused
  and root-imported Tests builds pass; placeholder and five-key axiom audits
  are clean beyond `propext`, `Classical.choice`, and `Quot.sound`.
  Independent read-only local review found no P0-P3 and rebuilt both targets.
- Failure policy: preserve strict threshold and positive-denominator
  hypotheses. If the square transport fails, report the exact algebra/API
  obstruction rather than weakening the endpoint or reintroducing the two
  caller calibration premises.

## Compiled Theorem Route: Explicit Path-Support Count/Bonus Calibration

- Route id:
  `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EXPLICIT-COUNT-BONUS-CALIBRATION`.
- Concrete target: remove both remaining calibration premises from the compiled
  path-support endpoint. A single state-action visit floor, one strict scalar
  count-radius inequality, and a finite-state/horizon half-contraction now
  construct the source-wide count margin and transition cover with
  `transitionBonus = rewardBound`, then recover the unchanged global
  confidence/optimism/recommended-regret theorem.
- Compiled Lean statements: `uniformFloorTransitionCoordinateRadius` and its
  nonnegativity; the policy coordinate-radius upper bound; the common
  `ExploratoryPathUniformVisitFloor`; full count-margin and table expected-count
  producers; the reward-bound transition-cover theorem; source-wide cover;
  `SourceCalibration`; and the final adaptive terminal.
- Local APIs/imports:
  `FiniteHorizonExploratoryPathSupportReachability`,
  `exploratoryPathStateLower`, `exploratoryActionProbabilityFloor`,
  `stateLower_expectedCount_le`, `expectedCountTransitionCoordinateRadius`,
  `simultaneousCountConfidenceRadius`, `div_le_div_of_nonneg_left`,
  `Finset.sum_le_sum`, finite cardinality, and ordered-field arithmetic.
- Proof route: bound every genuine expected count below by
  `episodes * visitFloor`; enlarge each radius to
  `2*r/(episodes*visitFloor-r)` using the positive denominator; sum the constant
  bound over next states; use `remaining <= horizon`; and apply
  `card(State)*uniformRadius*horizon <= 1/2` to close the value-envelope cover
  at bonus `rewardBound`. Instantiate this for the initial and every successor
  exploratory table, build the exact source calibration, and invoke the prior
  path-support endpoint.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty Action and an explicit default
  State; probability initial law; `explorationRate <= 1`; valid path support;
  one common visit floor below every recursive path-state floor times the
  exploratory action floor; strict `countRadius < episodes*visitFloor`; the
  finite-state/horizon half contraction; deterministic reward absolute bound;
  positive rounds/episodes; and `0 < delta <= 1`. Endpoint reward-bound
  nonnegativity follows from the absolute bound at the supplied default state.
- Retrieval evidence: exact local/memory search returned no route hit; compiled
  path-support, state-reachability, and all-coordinate finite-batch confidence
  routes; `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`;
  `TXT-SLIVKINS-2019-2024`, `SCN-RL-MDP`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; ten public declarations and focused/root-imported
  Tests builds compile. The Bool horizon-two canary proves a common `1/8`
  visit floor, a `2^22`-episode local radius below `30000`, uniform transition
  radius at most `1/8`, the exact two-state/two-stage half contraction, positive
  source cover with bonus one, full source calibration, and the final terminal.
  Placeholder scan is clean and the five-key-declaration axiom audit contains
  only `propext`, `Classical.choice`, and `Quot.sound`. Independent read-only
  local review found no P0-P3 and separately rebuilt the focused module and
  `Tests.Basic`.
- Failure policy: retain the strict positive denominator, all-stage/all-state
  floor, local-delta alignment, and half contraction. This route does not solve
  the square-root/log episode inequality in closed form, establish arbitrary
  MDP support, accumulate samples across rounds, model stochastic rewards,
  prove behavior/realized regret, or complete UCB-VI.

## Compiled Theorem Route: Exploratory Path-Support Reachability Calibration

- Route id:
  `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-REACHABILITY-CALIBRATION`.
- Concrete target: construct a policy-independent state lower envelope from an
  explicit initial singleton floor and a chosen predecessor state/action plus
  true-transition singleton floor for every successor-stage/state. Prove this
  envelope for the initial and every adaptive successor exploratory behavior,
  then invoke the compiled state-reachability calibration and global
  confidence/optimism/recommended-regret terminal without accepting
  `SourceStateReachability` as a caller premise.
- Compiled Lean statements: stage-zero state-mass identification; containment of
  one predecessor transition event in the next-stage state event; explicit
  path-support data and recursive state floor; nonnegativity; table-local and
  source-wide reachability; source calibration; final adaptive terminal.
- Local APIs/imports:
  `FiniteHorizonExploratoryReachabilityCalibration`,
  `stageTransitionJointProbability_eq_stageVisitProbability_mul_transition`,
  `stageVisitProbability_eq_stageStateProbability_mul_action`,
  `exploratoryActionProbabilityFloor_le_actionKernel_real`,
  `trajectoryStateAt`, `episodeStepOfTrajectory`, `measureReal_mono`,
  `Measure.fst_compProd`, ordered multiplication, and exploratory-source
  initial/successor policy equalities.
- Intended proof route: identify coordinate zero with the initial marginal;
  prove the selected transition event implies the next-state event; recursively
  multiply the previous state floor by the uniform exploratory action floor and
  chosen transition floor; induct over the chronological stage; instantiate the
  resulting table theorem for all source tables; consume the existing
  state-reachability calibration route.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty Action and an explicit default
  State; probability initial law; `explorationRate <= 1`; nonnegative initial
  and transition floors bounded by their true singleton masses; one predecessor
  state/action per successor-stage/state; the existing strict local count
  margin and unchanged transition-bonus cover; the terminal additionally keeps
  positive rounds/episodes, valid delta, reward bound, and nonnegative bonus.
- Retrieval evidence: exact local/memory search returned no route hit; compiled
  transition-joint, stage-visit, and exploratory calibration routes;
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-ORDER-ALGEBRA`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; thirteen public declarations, focused/root/Tests
  builds, direct chronology and table-local checks, a nondegenerate two-state/
  two-action full-terminal canary, clean placeholder and baseline-axiom audits,
  independent local review with its P3 coverage gap resolved, and refreshed
  declaration/reference indexes.
- Failure policy: this route may derive reachability only from the supplied
  path-support certificate. It must not claim positive support for arbitrary
  MDPs, replace the strict count margin or bonus cover by an unproved rate, or
  identify recommended expected regret with behavior/realized regret or
  complete UCB-VI.

## Compiled Theorem Route: Exploratory State-Reachability Calibration

- Leaf/route id:
  `RL-FINITE-HORIZON-EXPLORATORY-STATE-REACHABILITY-CALIBRATION`.
- Concrete targets: compile
  `AdaptiveEmpiricalOptimisticSource.exploratorySource_sourceCalibration_of_stateReachability`,
  which constructs the exact `SourceCalibration` consumed by the existing
  adaptive all-coordinate confidence/optimism theorem from a state-only lower
  envelope, the uniform-exploration action floor, and the unchanged bonus-cover
  contract, and the route endpoint
  `exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_stateReachability`,
  which directly recovers the global event and regret conclusion without an
  abstract calibration argument.
- Supporting Lean statements: nonnegativity of `stageStateProbability`; a Real
  exploratory action-kernel singleton floor; state-floor visit-probability and
  expected-count lower bounds; `ExploratoryStateCountMargin`;
  source-level `SourceStateReachability` and `SourceTransitionBonusCover`; and
  a policy-local `EmpiricalOptimisticCalibration` constructor.
- Local APIs/imports:
  `FiniteHorizonStageVisitFactorization`,
  `FiniteHorizonAdaptiveEmpiricalOptimisticConfidence`,
  `stageVisitProbability_eq_stageStateProbability_mul_action`,
  `explorationRate_mul_inv_card_le_exploratoryActionPMF`,
  `PMF.toMeasure_apply_singleton`, `ENNReal.toReal_mono`,
  `VisitCoordinate.expectedCount`, initial/successor exploratory source policy
  equalities, and ordered multiplication.
- Proof route: convert the existing ENNReal PMF lower bound to a Real kernel
  singleton bound; multiply by the nonnegative generated state mass using the
  exact stage-visit factorization; multiply again by the nonnegative episode
  count; discharge each policy-local calibration margin from the explicit
  state lower envelope and `ExploratoryStateCountMargin`; preserve the existing
  transition bonus cover verbatim; assemble initial and every in-horizon
  successor policy into `SourceCalibration`.
- Regularity contracts: finite measurable state/action spaces with decidable
  equality and measurable singletons; nonempty Action and explicit default
  State; probability initial law; `explorationRate <= 1`; a state lower envelope valid for the
  initial behavior and every in-horizon successor behavior; strict count radius
  below episodes times that state floor times the exploration floor; and the
  unchanged transition-radius/value-envelope bonus cover. No automatic state
  reachability, bonus rate, stochastic reward, behavior/realized regret, or
  complete UCB-VI claim is introduced. A separate `0 <= stateLower` premise is
  unnecessary; the strict margin itself enforces a useful positive product.
- Retrieval evidence: no exact local route hit; compiled stage-visit and
  adaptive exploratory confidence cards; `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; fourteen declarations, focused/root/Tests builds,
  Bool exact-half action-floor checks, a distinct-policy source with initial
  true-action mass `1/4` versus successor mass `3/4`, and a concrete horizon-one Unit source
  with sixteen episodes and two rounds compile. The concrete source proves
  local delta one quarter, radius below sixteen, state mass one for arbitrary
  initial/successor policies, zero cover, full `SourceCalibration`, and the
  final global confidence/optimism/recommended-regret terminal.
- Failure policy: preserve the strict local-delta count inequality, source
  policy quantification, and unchanged cover. Do not infer state reachability
  from exploration, weaken strict margins, identify recommendation regret with
  behavior regret, or describe this theorem as automatic calibration or
  complete UCB-VI.

## Compiled Leaf: Finite-Horizon MDP Mathlib Surface

- Leaf id: `RL-FINITE-HORIZON-MDP-MATHLIB-SURFACE`.
- Lean statements: `FiniteHorizonRL.MDP`, its transition-kernel instance,
  `FiniteHorizonRL.MDP.transitionValue`, `FiniteHorizonRL.MDP.bellmanQ`,
  `FiniteHorizonRL.MDP.measurable_transitionValue`,
  `FiniteHorizonRL.MDP.measurable_bellmanQ`, and
  `FiniteHorizonRL.MDP.bellmanQ_zero`.
- Local APIs/imports: `Mathlib.Probability.Kernel.MeasurableIntegral`,
  `ProbabilityTheory.Kernel`, `ProbabilityTheory.IsMarkovKernel`, Bochner
  integration, and `StronglyMeasurable.integral_kernel`.
- Proof route: store the transition Markov witness and measurable uncurried
  reward in the MDP; register the kernel instance; integrate a measurable
  continuation value against the selected transition measure; use Mathlib's
  measurable kernel-integral theorem; add the reward surface; simplify the
  zero-continuation integral.
- Regularity contracts: finite state and action types with supplied measurable
  spaces, a Markov transition kernel, and measurable uncurried deterministic
  Real reward. A measurable continuation value is required only by the two
  measurability theorems. No policy, trajectory, initial distribution,
  boundedness, separate integrability, recursion, optimality, occupancy, or
  regret premise is introduced.
- Retrieval evidence: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`, exact local Mathlib
  `MeasurableIntegral` source inspection, `SCN-RL-MDP`, and the task's textbook
  card. The textbook card is evidence, not a local proof.
- Status: `leanCompiled`; focused module, root import, and external
  `Tests.Basic` declaration/instance/measurability/zero-value canaries pass.
- Failure policy: this leaf closes only the finite data and one-step operator
  layer. The downstream policy-evaluation theorem now compiles; do not infer
  trajectory existence, Bellman optimality, occupancy identities, or RL regret
  from this data layer alone.

## Compiled Theorem Route: Finite-Horizon Markov Policy Evaluation

- Leaf/route id: `RL-FINITE-HORIZON-MARKOV-POLICY-EVALUATION-BELLMAN`.
- Lean statements: `FiniteHorizonRL.MarkovPolicy`, the action-kernel and
  induced-state-kernel Markov instances,
  `FiniteHorizonRL.MarkovPolicy.inducedStateKernel`, `bellman`,
  `measurable_bellman`, `valueRemaining`, `measurable_valueRemaining`,
  `valueAt`, `measurable_valueAt`, `valueAt_horizon`, and the route endpoint
  `valueAt_bellman`.
- Local APIs/imports: `BanditRLProof.RL.FiniteHorizonMDP`, Mathlib
  `Kernel.compProd`, `Kernel.map`, `Kernel.IsMarkovKernel.map`,
  `StronglyMeasurable.integral_kernel_prod_right`, finite subtypes, Nat
  subtraction, `omega`, and proof irrelevance.
- Proof route: index policy kernels by `Fin mdp.horizon`; compose each policy
  action law with the MDP transition and project `Prod.snd`; integrate
  `mdp.bellmanQ` against the action kernel; recursively evaluate by decisions
  remaining, where the selected chronological stage is
  `horizon - remaining`; define `valueAt stage` using `horizon - stage`; prove
  the terminal equation and transport
  `horizon-stage = horizon-(stage+1)+1` through a proof-irrelevant congruence
  lemma to obtain the chronological Bellman equation.
- Regularity contracts: finite state and action types with supplied measurable
  spaces; the parent Markov transition and measurable reward contracts; one
  Markov action kernel for every valid decision stage. Measurability of all
  recursively generated values is derived. No initial state law, trajectory,
  bounded reward premise, caller integrability, deterministic policy,
  maximization, optimality, occupancy, conditional expectation, or regret is
  assumed.
- Retrieval evidence: `LOCAL-LEAF-RL-FINITE-HORIZON-MDP-MATHLIB-SURFACE`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, exact Mathlib
  `CompProd`, `MapComap`, and `MeasurableIntegral` declarations, `SCN-RL-MDP`,
  and textbook/UCB-VI cards as route evidence only.
- Status: `leanCompiled`; focused module, project root, ten declaration checks,
  induced-kernel/measurability/terminal/Bellman external canaries, and
  `Tests.Basic` pass.
- Failure policy: policy-kernel composition, recursive policy evaluation,
  terminal value, chronological Bellman recursion, and recursive measurability
  are closed. The next theorem route is a generated finite policy trajectory
  with expected cumulative reward equal to `valueAt 0`. Do not jump directly
  to Bellman optimality, occupancy regret, UCB-VI optimism, or episode regret,
  and do not treat literature cards as imported Lean proofs.

## Compiled Theorem Route: Finite Policy Trajectory Value Identity

- Leaf/route id: `RL-FINITE-HORIZON-POLICY-TRAJECTORY-VALUE-IDENTITY`.
- Lean statements: `FiniteHorizonRL.StepTrace`,
  `MarkovPolicy.actionStateKernel`, `trajectoryKernelRemaining`, their Markov
  instances, `MDP.cumulativeRewardFrom`, its measurability and automatic
  trajectory-law integrability wrappers, the statewise
  `integral_cumulativeRewardFrom_trajectoryKernelRemaining_eq_valueRemaining`,
  `MarkovPolicy.trajectoryMeasure`, `MDP.cumulativeReward`, and the route
  endpoint
  `integral_cumulativeReward_trajectoryMeasure_eq_integral_valueAt_zero`.
- Local APIs/imports: the compiled policy route, Mathlib `Kernel.compProd`,
  `Kernel.comap`, `Kernel.map`, `Measure.compProd`, `integral_map`,
  `ProbabilityTheory.integral_compProd`, deterministic kernels, Pi-space
  measurability, `Fin.cons`, `Fin.tail`, and `Integrable.of_bound`.
- Proof route: represent exactly `n` decisions by `Fin n -> Action × State`;
  recursively sample the current policy action and MDP next state, run the tail
  kernel from that next state, and prepend with `Fin.cons`; prove the generated
  return measurable and automatically integrable on the finite trace type;
  expand the head/tail integral and then action/transition integral; identify
  the recursive tail with `valueRemaining`; finally apply
  `Measure.integral_compProd` to the probability initial-state law.
- Regularity contracts: finite state/action types with supplied measurable
  spaces, the parent MDP and stagewise Markov-policy contracts, and a
  probability initial-state measure for the final theorem. Finite-type
  measurability derives all Real integrability. No reward bound, caller
  integrability premise, deterministic policy, infinite suffix, maximization,
  optimality, occupancy, conditional expectation, optimism, or regret is used.
- Retrieval evidence: the two parent local RL cards,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, exact Mathlib `IntegralCompProd`, `MapComap`, and kernel
  `Basic` declarations, `SCN-RL-MDP`, and literature cards as evidence only.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds, declaration checks,
  and external Markov/measurability/integrability/identity canaries pass.
- Failure policy: finite policy trajectory existence and expected-return
  identification are closed. The next leaf is finite-action Bellman
  optimality; do not infer occupancy recursion, UCB-VI optimism, episode
  regret, or complete RL formalization from this theorem.

## Compiled Theorem Route: Finite-Horizon Bellman Optimality

- Leaf/route id: `RL-FINITE-HORIZON-BELLMAN-OPTIMALITY`.
- Lean statements: `MDP.optimalAction`, its maximizing and measurability
  theorems, `optimalBellman`, transition/Bellman/policy-Bellman monotonicity,
  `optimalValueRemaining`, `optimalValueAt`, terminal and chronological
  Bellman equations, `MarkovPolicy.valueAt_le_optimalValueAt`, the deterministic
  `MDP.optimalPolicy`, its one-step and all-stage attainment theorems, and the
  route endpoint `MDP.optimalValueAt_dominates_and_is_attained`.
- Local APIs/imports: the compiled finite trajectory/value route, Mathlib
  `Finite.exists_max`, `measurable_of_finite`, `Kernel.deterministic`,
  `integral_dirac'`, `integral_mono`, probability-kernel constant integrals,
  finite-type automatic integrability, and `Nat.decreasingInduction`.
- Proof route: choose a pointwise Bellman-Q maximizer over the finite nonempty
  action type; derive selector measurability from finite singleton-measurable
  states; prove transition and all Bellman operators monotone; recurse the
  optimal value backward; use chronological decreasing induction to dominate
  every Markov policy; build deterministic greedy kernels against the next
  optimal value; evaluate each Dirac integral at its maximizing action; use a
  second decreasing induction to prove all-stage attainment.
- Regularity contracts: finite state/action types with supplied measurable
  spaces, the parent MDP contracts, `Nonempty Action`, and
  `MeasurableSingletonClass State` as the explicit finite-discrete measurable
  selection contract. No initial distribution, reward bound, caller
  integrability, compactness, occupancy, conditional expectation, optimism,
  UCB-VI, episode regret, or complete-RL assumption is introduced.
- Retrieval evidence: all three parent local RL cards,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, exact Mathlib finite-max/measurability/kernel/integral
  declarations, `SCN-RL-MDP`, and literature cards as evidence only.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds, public declaration
  checks, and selector/Markov/dominance/attainment external canaries pass.
- Failure policy: finite Bellman optimality and measurable greedy-policy
  attainment are closed. The next row is occupancy/value-difference/regret;
  do not infer occupancy recursion, performance-difference telescoping,
  optimism, UCB-VI, episode regret, or complete RL formalization yet.

## Compiled Theorem Route: Finite-Horizon Occupancy Regret

- Leaf/route id: `RL-FINITE-HORIZON-OCCUPANCY-REGRET`.
- Lean statements: chronological `MarkovPolicy.stateOccupancy` and its
  probability instance; measurable/nonnegative `policyBellmanGap`; the kernel
  integral and Bellman-difference transport lemmas; recursive
  `occupancyGapRemaining` and its chronological successor equation; the exact
  performance-difference identity; `expectedRegret`, its occupancy equality
  and nonnegativity; greedy-policy zero regret; and the packaged route endpoint
  `MDP.expectedRegret_eq_occupancyGap_nonneg_and_optimalPolicy_zero`.
- Local APIs/imports: all compiled finite-horizon RL parents, Mathlib
  `MeasureComp`, `Measure.snd_compProd`, `integral_map`, measure/kernel
  `integral_compProd`, measure-kernel probability instances, and finite-type
  automatic integrability.
- Proof route: recursively compose induced state kernels from the initial law;
  expand the projected action-transition kernel; identify Bellman continuation
  differences with next-state integrals; recurse over decisions remaining and
  telescope the integrated optimal-policy value difference; rewrite generated
  trajectory reward using the compiled trajectory/value theorem.
- Regularity contracts: finite state/action types with supplied measurable
  spaces, the parent MDP/policy/trajectory/optimality contracts,
  `Nonempty Action`, `MeasurableSingletonClass State`, and a probability
  initial-state law. No reward bounds or caller integrability are needed. No
  optimism, confidence set, repeated-episode, high-probability, minimax, or
  asymptotic-regret assumption is introduced.
- Retrieval evidence: all parent local RL cards,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, exact Mathlib composition/integral declarations,
  `SCN-RL-MDP`, and literature/UCB-VI cards as evidence only.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds and external
  probability/equality/endpoint canaries pass; full handoff gate required.
- Failure policy: occupancy recursion, policy performance difference, exact
  expected trajectory regret, nonnegativity, and greedy-policy zero regret are
  closed. UCB-VI optimism/confidence and multi-episode regret remain separate.

## Compiled Theorem Route: Optimistic Bellman Certificate

- Leaf/route id: `RL-FINITE-HORIZON-OPTIMISTIC-BELLMAN-CERTIFICATE`.
- Lean statements: `MDP.optimalBellman_mono`;
  `MDP.OptimisticBellmanCertificate` and its canonical exact instance;
  local-to-global optimal-value domination; generic monotone
  `MarkovPolicy.occupancySumRemaining`; measurable/nonnegative policy Bellman
  residuals; exact residual telescope; canonical compatibility with
  `occupancyGapRemaining`; expected-regret-to-residual and residual-to-bonus
  inequalities; and the packaged endpoint
  `expectedRegret_le_residual_le_occupancyBonusRemaining`.
- Local APIs/imports: the compiled occupancy/regret route, true-policy
  `bellman`, `optimalBellman`, `optimalValueRemaining`, induced state kernels,
  measure-kernel composition, finite-state integrability, and integral
  monotonicity.
- Proof route: prove finite-action optimal Bellman monotonicity; induct from the
  exact zero terminal surface to turn local Bellman upper inequalities into
  global optimism; telescope upper value minus policy value by pushing tail
  differences through the true induced state kernel; lift pointwise
  residual-to-bonus domination through recursive occupancy-sum monotonicity.
- Regularity contracts: finite state/action types with supplied measurable
  spaces, all parent MDP/policy/trajectory/optimality/occupancy contracts,
  `Nonempty Action`, `MeasurableSingletonClass State`, a probability initial
  law, zero terminal upper value, and local true optimal-Bellman upper bounds.
  No estimated reward/transition model, confidence event, clipping, episode
  family, cross-episode filtration, or high-probability premise is introduced.
- Retrieval evidence: all parent local RL cards,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, exact local Bellman/occupancy declarations,
  `SCN-RL-MDP`, and the UCB-VI/textbook cards as route evidence only.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds, public checks,
  global-optimism/canonical-compatibility/final-endpoint canaries, zero-horizon
  boundary, and baseline axiom audit pass; full handoff gate required.
- Failure policy: local-to-global optimism and deterministic single-episode
  bonus-regret assembly are closed. Producing the certificate from estimated
  reward/transition confidence and summing episode-indexed regret remain open.

## Compiled Theorem Route: Estimated-Model Optimistic Regret

- Leaf/route id: `RL-FINITE-HORIZON-ESTIMATED-MODEL-OPTIMISTIC-REGRET`.
- Lean statements: `MDP.EstimatedModelPlan`, its exact-model instance,
  estimated `transitionValue`/`bellmanQ`/`optimisticQ`, finite maximizing
  `optimisticAction`, recursive `upperValueRemaining`, `Confidence`,
  `certificate`, global optimism, chronological `optimisticPolicy`, exact
  selector alignment, `selectedRadiusRemaining`, the factor-two policy
  residual theorem, the full residual chain, and the route endpoint
  `optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining`.
- Local APIs/imports: `FiniteHorizonOptimisticCertificate`,
  `Finite.exists_max`, `Kernel.deterministic`, `integral_dirac'`, finite-state
  measurability/integrability, `optimalValueRemaining_le_upperValueRemaining`,
  and `expectedRegret_le_residual_le_occupancyBonusRemaining`.
- Proof route: recurse the optimistic estimated Bellman maximum from terminal
  zero; use both directions of the absolute-error contracts to prove true-Q
  upper confidence and selected-action residual control; package the former
  as the existing certificate; evaluate the deterministic policy Bellman
  integral at the estimated argmax; then feed the pointwise factor-two radius
  bound to the existing true-occupancy theorem.
- Regularity contracts: finite state/action measurable spaces, all parent MDP
  contracts, `Nonempty Action`, `MeasurableSingletonClass State`, measurable
  estimated rewards and radii, a Markov estimated transition at each valid
  stage, and two-sided confidence only for the recursively generated tail
  upper value. A probability initial law is required only by the terminal
  regret theorem.
- Retrieval evidence: all compiled local RL cards,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, `SCN-RL-MDP`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `WEAPON-UCB-OPTIMISM` is route
  inspiration only. Targeted local retrieval found no existing estimated-MDP
  certificate producer.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds, 20 declaration
  checks, exact-model/certificate/residual/final external canaries, zero-
  horizon boundary, placeholder scan, baseline axiom audit, independent
  review, index refresh, and final repository gate pass.
- Failure policy: estimated-model confidence-to-certificate transport,
  estimated-greedy selector alignment, factor-two residual control, and the
  single-episode occupancy regret bound are closed. Do not weaken transition
  confidence into an unjustified uniform bound over arbitrary unbounded
  values. The next route must produce these confidence inequalities from
  empirical episode history; this route does not claim a confidence
  probability, cross-episode filtration, cumulative regret, or complete
  UCB-VI theorem.

## Compiled Theorem Route: Coordinate Model Confidence Regret

- Leaf/route id: `RL-FINITE-HORIZON-COORDINATE-MODEL-CONFIDENCE-REGRET`.
- Lean statements: a finite-measure expectation-difference lemma controlled
  by singleton-mass coordinate radii and a pointwise value envelope;
  `MDP.EstimatedModelPlan.CoordinateConfidence`; its transition-error bridge,
  `toConfidence`, and a route endpoint composing with the compiled global
  optimism and selected-radius expected-regret theorem.
- Local APIs/imports: `FiniteHorizonEstimatedModelCertificate`,
  `integral_fintype`, `integrable_of_fintype`, `Finset.sum_sub_distrib`,
  `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`, `abs_mul`, and the compiled
  `Confidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining`.
- Proof route: expand estimated and true finite-state expectations into sums
  of singleton masses; rewrite the difference as coordinate mass error times
  tail value; use the finite-sum triangle inequality, singleton-error bounds,
  and a recursive-tail absolute envelope; cover the resulting finite sum by
  the plan transition radius; package the reward/transition obligations as
  the existing confidence structure and invoke the compiled route endpoint.
- Regularity contracts: finite state/action measurable spaces, the parent MDP
  and estimated-plan contracts, `Nonempty Action`,
  `MeasurableSingletonClass State`, pointwise reward error, singleton
  transition-mass error radii, an absolute envelope for every recursively
  generated tail upper value, and transition-radius coverage of the finite
  coordinate sum. A probability initial law is required only by the final
  regret theorem.
- Retrieval evidence: all parent local RL cards; no local empirical RL
  transition-count or coordinate-confidence declaration was found;
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`,
  `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `SCN-RL-MDP`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `WEAPON-UCB-OPTIMISM` and
  `WEAPON-TAIL-INEQUALITIES` are route inspiration only.
- Status: `leanCompiled`; focused and `Tests.Basic` builds, public declaration
  checks, generic consumers, a nonzero atomic Bool/Dirac canary, a complete
  horizon-two dependent coordinate-confidence canary, placeholder scan,
  baseline axiom audit, independent review, index refresh, and the full
  repository gate pass.
- Failure policy: preserve the coordinate-to-Bellman route. If compilation
  fails, record the exact integral/sum goal and first audit finite-measure,
  singleton measurability, nonnegativity, or product-order requirements. Do
  not replace the coordinate event by a direct transition-expectation
  assumption, and do not claim empirical counts, confidence probability,
  episode filtration, cumulative regret, or a complete UCB-VI theorem.

## Compiled Theorem Route: Finite-Batch Empirical Model Confidence Regret

- Leaf/route id:
  `RL-FINITE-HORIZON-FINITE-BATCH-EMPIRICAL-MODEL-CONFIDENCE-REGRET`.
- Lean statements: `EpisodeStep`; `EpisodeBatch.visitCount`, `rewardSum`,
  `empiricalReward`, `transitionCount`, and
  `sum_transitionCount_eq_visitCount`; `empiricalTransitionPMF` with explicit
  zero/positive branch lemmas; `empiricalTransitionMass_eq_div_of_visitCount_ne_zero`;
  `empiricalTransitionKernel`, its Markov proof and singleton-mass bridge;
  `MDP.FiniteBatchModel.plan`; `FiniteBatchModel.Confidence` and
  `.toCoordinateConfidence`; and
  `.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining`.
- Local APIs/imports: `FiniteHorizonCoordinateModelConfidence`,
  `Mathlib.Probability.ProbabilityMassFunction.Constructions`,
  `PMF.ofFintype`, `PMF.toMeasure`, `PMF.toMeasure_apply_singleton`,
  `Kernel.ofFunOfCountable`, `Finset.sum_comm`, `ENNReal.add_div`, finite
  indicator/fiber sums, `measurable_of_finite`, and the compiled
  coordinate-confidence endpoint. `Finset.sum_div` was retrieved but is not
  applicable to `ENNReal`; the normalization instead uses finite induction and
  `ENNReal.add_div`.
- Proof route: sum indicator counts over the finite episode family; swap the
  episode/next-state sums to prove that next-state counts partition visits;
  normalize the counts when visits are positive and use a default-state Dirac
  PMF when visits are zero; expose the PMF as a state-action-indexed Markov
  kernel; identify each singleton real mass with the named empirical
  frequency; build the empirical estimated plan; translate empirical reward
  and frequency errors, recursive-tail envelope, and finite coordinate-radius
  coverage into `CoordinateConfidence`; invoke the compiled optimism/regret
  theorem.
- Regularity contracts: finite state/action measurable spaces with
  `DecidableEq`, measurable singletons, and nonempty state/action; a finite
  episode family; a default state used only for zero visits; measurable reward
  and transition radii; explicit empirical reward and singleton-frequency
  errors; generated-tail absolute envelope; finite coordinate-sum coverage;
  and a probability initial law only at the terminal regret theorem. The raw
  finite records are not yet claimed to come from an MDP trajectory law.
- Retrieval evidence: all parent local RL cards; targeted local search found
  no empirical-transition declaration; `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS`,
  `MLIB-ORDER-ALGEBRA`, exact Mathlib PMF/kernel source, `SCN-RL-MDP`, and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `WEAPON-UCB-OPTIMISM` and
  `WEAPON-TAIL-INEQUALITIES` are inspiration only.
- Status: `leanCompiled`; focused/root/`Tests.Basic` builds, public declaration
  checks, zero-visit and positive-count canaries, a complete nonzero-error model
  confidence canary, independent review, axiom audit, index refresh, and the
  full repository gate pass.
- Failure policy: preserve the genuine empirical-model construction. On
  failure, retain the exact count-partition, PMF normalization, singleton-mass,
  or kernel goal and audit zero-count behavior, ENNReal/Real conversion,
  measurable singletons, or missing finite-type instances. Do not replace the
  empirical kernel with a caller-supplied estimated kernel. The deterministic
  finite-record producer is closed. Next identify batches with generated
  episode trajectories and prove a simultaneous reward/singleton-transition
  concentration event. This route does not prove episode-law identification,
  concentration probability, filtration, clipping/range bounds, cumulative
  regret, or a complete UCB-VI theorem.

## Compiled Theorem Route: IID Generated-Trajectory Batch Law

- Leaf/route id: `RL-FINITE-HORIZON-IID-TRAJECTORY-BATCH-LAW`.
- Lean statements: measurable current-state and `EpisodeStep` extraction from a
  full generated trajectory; measurable extraction of a finite trajectory
  family into `EpisodeBatch`; iid finite-product trajectory and mapped batch
  measures with probability instances; episode/stage marginal pushforward law;
  exact visit/reward/transition contribution-sum identities; episode-step,
  arbitrary measurable-statistic, and named-contribution `iIndepFun` theorems
  on the source product law; mapped-batch record/statistic independence; and a
  bundled endpoint whose marginal and independence fields both use the mapped
  batch law.
- Local APIs/imports: compiled `FiniteHorizonTrajectory` and
  `FiniteHorizonEmpiricalModel`; `Mathlib.MeasureTheory.Constructions.Pi`;
  `Mathlib.Probability.Independence.Basic`; `Measure.pi`;
  `MeasureTheory.measurePreserving_eval`; `Measure.map_map`;
  `ProbabilityTheory.iIndepFun_pi`;
  `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`;
  `measurable_pi_apply`; owned measurable `EpisodeStep` projections; and
  `measurable_of_finite`.
- Proof route: reconstruct each stage's current state from the initial state or
  preceding next-state coordinate; form the observed reward from `mdp.reward`;
  prove finite trajectory-to-batch extraction measurable; take the finite
  product of the generated `policy.trajectoryMeasure`; map it to the batch;
  rewrite coordinate maps through `Measure.map_map` and the
  measure-preserving product evaluation; derive episode independence directly
  from `iIndepFun_pi`; transport it to the mapped batch law using the finite
  product characterization; then compose arbitrary measurable statistics.
- Regularity contracts: finite State/Action with measurable spaces, decidable
  equality, measurable singletons, and nonempty types where inherited by the
  empirical layer; a fixed MDP, fixed Markov policy, probability initial-state
  law, and finite episode index. All episodes use the same policy and law.
  This route has deterministic MDP rewards and does not model adaptive policy
  updates across episodes.
- Retrieval evidence: all parent RL local cards;
  `LOCAL-LEAF-IID-REWARD-FAMILY`; `MLIB-PROBABILITY-INDEPENDENCE`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`;
  exact Mathlib finite Pi/evaluation/independence source; `SCN-RL-MDP`; and the
  UCB-VI paper card as route evidence only.
- Status: `leanCompiled`; focused module and `Tests.Basic` builds pass. Public
  checks and Bool/Unit horizon-two canaries cover stage-zero/current-state
  indexing, predecessor next-state indexing, extracted rewards, exact batch
  sums, probability instances, a concrete marginal law, contribution
  independence, source and mapped-batch statistic independence, and the
  bundled route endpoint. Independent review found no P0/P1; its mapped-law P2
  and measurable-owner/canary P3 findings were resolved. Public endpoint axiom
  audit is baseline-only. The full project gate passes with root 3497 jobs,
  Tests 3499 jobs, and 15 CLI tests with one expected skip.
- Failure policy: generated trajectory pushforward identification and
  fixed-policy finite-product contribution independence are closed. Next center
  fixed-stage Real visit/transition indicators around their integrals and prove
  bounded iid finite-sum deviation bounds before visit-conditioned ratios. Do
  not replace the generated law with an assumed batch distribution or infer
  adaptive-policy, confidence-probability, filtration, cumulative-regret, or
  complete UCB-VI claims.

## Compiled Theorem Route: IID Fixed-Coordinate Count Confidence

- Leaf/route id: `RL-FINITE-HORIZON-IID-COUNT-CONFIDENCE`.
- Lean statements: measurable Real-valued visit and transition indicators;
  single-trajectory visit/joint-transition means identified with measurable
  event masses, their `[0,1]` ranges and joint-to-visit domination; mapped
  episode-coordinate integral identities; exact Real cast count-minus-mean
  identities; measurable count deviations and bad events; exact and positive
  iid Bernoulli variance proxy; fixed-coordinate two-sided delta tails for
  visit and joint-transition counts; and a bundled theorem exposing both tails.
- Local APIs/imports: compiled `FiniteHorizonIIDTrajectoryBatch` and
  `ConcentrationSubGaussian`; `EpisodeStep.measurable_state`,
  `.measurable_action`, `.measurable_nextState`; singleton preimages,
  intersections, `Measurable.ite`, `Finset.measurable_sum`, `measurableSet_le`;
  `MarkovPolicy.iidEpisodeBatchMeasure_map_eval` and
  `.iIndepFun_iidEpisodeBatch_statistic`;
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`;
  `Concentration.subGaussian_sum_abs_tail_ennreal_delta_of_iIndepFun`;
  `integral_map`; finite sum/cast algebra.
- Proof route: define `{0,1}` record indicators and their genuine
  single-trajectory means; prove each batch coordinate has that common
  integral using its mapped marginal law; center the iid coordinate family;
  use the `[0,1]` Hoeffding proxy; rewrite the centered sum as the cast named
  count minus `episodes * mean`; invoke the compiled delta-calibrated
  independent-sum theorem separately for visit and transition coordinates;
  package the two conclusions.
- Regularity contracts: finite State/Action with measurable spaces, decidable
  equality, measurable singletons, and inherited nonempty types; one fixed MDP
  and one fixed Markov policy for every episode; probability initial-state
  law; positive finite episode count; `0 < delta <= 1`. Reward regularity is
  not used because both statistics are count indicators.
- Retrieval evidence: all parent local RL cards;
  `TAIL-HOEFFDING-BOUNDED`, `TAIL-SUBGAUSS-SUM`;
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`; exact Mathlib bounded-variable
  Hoeffding and independent finite-sum sources; `SCN-RL-MDP`; UCB-VI paper
  evidence only.
- Status: `leanCompiled`; focused module, root, `Tests.Basic`, CLI, and full
  project gates pass. Public checks expose all layers. Bool/Unit horizon-two
  consumers verify indicator ranges, both mapped integral transports,
  joint-to-visit probability domination, exact `episodes / 4` proxy and its
  positivity, both centered-count identities, both centered independence
  theorems, bad-event measurability, the visit tail, and the bundled endpoint
  at `delta=1/2`. Independent review found no P0/P1/P2 and all P3 findings are
  resolved; the public axiom audit is baseline-only.
- Failure policy: fixed-coordinate mapped-batch visit and joint-transition count
  tails are closed. Next allocate a shared failure budget over the finite
  stage/state/action/next-state registry and prove an explicit simultaneous
  event. Visit-probability lower bounds and positive random denominators remain
  separate prerequisites before empirical transition ratios. Do not interpret
  the current conjunction as a union/shared-budget theorem or infer adaptive
  episode filtration, cumulative regret, or complete UCB-VI.

## Compiled Theorem Route: Eligible Empirical Transition Confidence

- Leaf/route id: `RL-FINITE-HORIZON-IID-ELIGIBLE-EMPIRICAL-TRANSITION-CONFIDENCE`.
- Lean-facing target: under the existing simultaneous-count good event, every
  eligible stage/state/action coordinate and every next state satisfy
  `|empiricalTransitionMass - trueTransitionMass| < 2 * radius / visitCount`;
  the same mapped fixed-policy iid event has mass at most global delta.
- Local APIs/imports: `FiniteHorizonEmpiricalModel`,
  `FiniteHorizonIIDEligibleVisitCountPositivity`,
  `FiniteHorizonStageTransitionJointFactorization`, the empirical count-ratio
  rewrite, both simultaneous count deviations, the positive-denominator
  consumer, `Measure.real`, `abs_div`, `div_lt_div_iff_of_pos_right`, and
  `linarith`.
- Proof route: derive positive realized visit count from each strict expected
  count margin; rewrite the empirical PMF singleton as joint count divided by
  visit count; factor the genuine joint mean as visit probability times the
  true transition singleton mass; combine both strict count errors using
  `0 <= transitionMass <= 1`; divide by the positive realized count; quantify
  over the finite eligible set and all next states without a second union bound.
- Regularity: finite measurable State/Action with decidable equality and
  measurable singletons; one fixed MDP/policy; probability initial law;
  explicit default state; positive episodes and `0 < delta <= 1` for the tail;
  finite eligible coordinates with `radius < expectedCount`. Empty eligible
  sets and horizon zero remain valid. Reward, adaptive episodes, anytime
  confidence, cumulative regret, and complete UCB-VI are not assumed.
- Retrieval: four compiled parent local cards; `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`; exact Mathlib ordered-field
  and absolute-value source; `SCN-RL-MDP`; UCB-VI paper route evidence;
  `WEAPON-UCB-OPTIMISM` inspiration only.
- Status: `leanCompiled`; the fixed-coordinate strict ratio theorem, measurable
  global-delta bundle, root import, direct Unit consumer, complete four-episode
  eligible-set canary, horizon-zero empty-set canary, and concrete Bool-state
  nonzero-error `1/4 < 2*radius/4` consumer compile. Placeholder and baseline
  axiom audits pass. Independent review found no P0-P1; its status, semantic
  canary, and exact regularity/API findings are resolved. Retrieval indexes and
  the full-project gate are refreshed before handoff.
- Failure policy: retain the realized positive denominator and the existing
  simultaneous event. Do not silently replace it by a deterministic occupancy
  lower bound, assume full support, or reinterpret this as reward confidence,
  adaptive-policy confidence, cumulative regret, or complete UCB-VI.

## Compiled Theorem Route: Stage Transition Joint Factorization

- Leaf/route id: `RL-FINITE-HORIZON-STAGE-TRANSITION-JOINT-FACTORIZATION`.
- Lean-facing target: identify the named generated stage joint probability with
  `stageVisitProbability * (mdp.transition (state, action) {nextState}).toReal`.
- Local APIs/imports: recursive `trajectoryKernelRemaining`, `trajectoryMeasure`,
  extracted `episodeStepOfTrajectory`, `Measure.compProd_apply`,
  `Kernel.compProd_apply`, singleton rectangle mass, and `ENNReal.toReal_mul`.
- Proof route: induct through the remaining trace; factor the selected
  action/next-state draw through `actionKernel.compProd mdp.transition`; carry
  the fixed true transition singleton mass through earlier generated layers
  and the initial-state composition product; rewrite the named Real event masses.
- Regularity: structural trace reconstruction has no measurable/finite-space
  contract; kernel event identities use finite measurable State/Action with
  measurable singletons; the named event-probability endpoint also exposes
  decidable equality, a fixed MDP/policy, and a probability initial law. No
  visit positivity, episodes, delta, concentration, reward bound, ratio, or
  adaptivity.
- Retrieval: parent generated-trajectory/count cards; `MLIB-PROBABILITY-KERNEL`;
  `MLIB-MEASURE-INTEGRAL`; `SCN-RL-MDP`; UCB-VI route evidence;
  `WEAPON-UCB-OPTIMISM` inspiration only.
- Status: `leanCompiled`; the remaining-kernel ENNReal identity, initial-law
  transport, named Real endpoint, root import, public declarations, and
  reachable-one, unreachable-zero, and horizon-two stage-one successor canaries
  compile. Placeholder and axiom audits pass. Independent review found no
  P0-P2, and both P3 findings on excess regularity and successor-stage coverage
  are resolved. Retrieval indexes and the full gate are refreshed before handoff.
- Failure policy: this route identifies population masses only. Its eligible
  positive-denominator empirical transition-confidence consumer now compiles;
  this parent theorem alone still supplies no reward or adaptive-policy result.

## Compiled Theorem Route: Stage Visit Factorization

- Leaf/route id: `RL-FINITE-HORIZON-STAGE-VISIT-FACTORIZATION`.
- Lean-facing statements: exact generated-law identities
  `MDP.stageOfRemainingCoordinate`, its successor/full reindexing lemmas,
  `trajectoryKernelRemaining_visitEvent_eq_stateEvent_mul_action`,
  `trajectoryMeasure_visitEvent_eq_stateEvent_mul_action`, and
  `stageStateProbability` plus
  `stageVisitProbability_eq_stageStateProbability_mul_action`.
- Local APIs/imports: `FiniteHorizonStageTransitionJointFactorization`;
  `StepTrace.stateAt/stateActionAt`; `trajectoryKernelRemaining`;
  `actionStateKernel`; `trajectoryMeasure`; `stageVisitProbability_eq_measureReal`;
  Mathlib `Kernel.compProd_apply`, `Measure.compProd_apply`,
  `lintegral_mul_const`, and `ENNReal.toReal_mul`.
- Proof route: induct on remaining trace length. At coordinate zero, map the
  generated head and reduce the state/action event to an action-kernel
  singleton. At successor coordinates, apply the induction hypothesis under
  the recursive `compProd` integral and pull out the fixed singleton mass.
  Integrate over the initial state, rewrite public episode-step events, and
  convert the finite ENNReal product to the named Real probability identity.
- Regularity: stage-coordinate arithmetic requires no measurable or finite
  instances. The event identities use finite measurable state/action spaces,
  measurable singletons, and state decidable equality; the named visit
  endpoint inherits state/action decidable equality and uses a probability
  initial law. No reachability, support, episode count, delta, reward,
  concentration, adaptive-policy, confidence, or regret assumptions.
- Retrieval: targeted memory/local declaration search found no existing visit
  factorization. Reuse `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, the compiled transition-factorization route,
  `SCN-RL-MDP`, and `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; weapon cards are
  inspiration only.
- Status: `leanCompiled`; focused module, root import, public checks, and
  `Tests.Basic` pass. A two-stage Unit-state/Bool-action policy assigns true
  action mass zero at stage zero and one half at stage one; the canary proves
  both visit probabilities, identifies remaining coordinate one with stage
  one, and directly instantiates the recursive kernel theorem there. Placeholder,
  baseline-axiom, independent-review, retrieval-index, and full-gate evidence
  is recorded before handoff.
- Failure policy: the exact factorization remains valid at zero state mass.
  Do not infer reachability from it. The next narrow route may combine an
  independently proved state-mass lower bound with the compiled exploratory
  action floor; automatic calibration, behavior/realized regret, and complete
  UCB-VI remain downstream.

## Compiled Theorem Route: Adaptive Exploratory Empirical Optimistic Confidence

- Leaf/route id:
  `RL-FINITE-HORIZON-ADAPTIVE-EXPLORATORY-EMPIRICAL-OPTIMISTIC-ALL-COORDINATE-CONFIDENCE-RECOMMENDED-REGRET`.
- Lean-facing target: generate every latest-batch iid episode batch with a
  behavior policy that uniformly explores around the current optimistic table;
  expose full action support; construct roundwise
  `EstimatedModelPlan.CoordinateConfidence` witnesses off one global event;
  and sum the expected-regret bounds of the optimistic policies recommended by
  the observed batches.
- Local APIs/imports: the concrete adaptive source and all-coordinate route;
  `PMF.bernoulli`, `PMF.uniformOfFintype`, `PMF.bind_apply`;
  `Kernel.ofFunOfCountable` and `Kernel.comap`; summary/raw PMF and singleton
  kernel bridges; `EmpiricalOptimisticCalibration`; `CoordinateConfidence`;
  `norm_integral_le_of_norm_le_const`; and `Finset.sum_le_sum`.
- Proof route: mix uniform exploration with each deterministic table and prove
  the `explorationRate / card Action` lower bound; construct the table-indexed
  exploratory iid kernel and adaptive source; prove event measurability and
  reuse the global count tail; establish the known-reward value envelope; build
  coordinate confidence for every exploratory batch under calibration; sum
  one-episode bounds for each recommended plan without identifying it with the
  behavior policy.
- Regularity contracts: finite measurable nonempty State/Action with decidable
  equality and measurable singletons; probability initial law;
  `explorationRate <= 1`; positive rounds/episodes; `0 < delta <= 1`; fallback
  state; known reward bound; nonnegative bonus; and state-action expected-visit
  margins plus the coordinate-radius/value-envelope bonus cover for every
  exploratory behavior policy. Standard Borel is not needed.
- Retrieval: no matching local route; direct parent adaptive source/count,
  all-coordinate, coordinate-confidence, empirical-model, and optimism/regret
  cards; `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-FINSET-SUMS`; `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` and `SCN-RL-MDP`;
  weapon cards are inspiration only.
- Status: `leanCompiled`; focused/root/Tests builds and external canaries pass.
  A Bool two-action canary proves exact `1/2` action mass at exploration rate
  one. Initial review exposed the impossible deterministic full-coordinate
  margin; this exploratory redesign resolves it. Axiom/placeholder audits,
  independent re-review, refreshed indexes, and the full gate pass. The gate
  records root build 3508 jobs, Tests build 3510 jobs, and 15 CLI tests with
  one expected skip.
- Failure policy: action support is closed, but state reachability and bonus
  coverage remain explicit. Do not conflate exploratory behavior regret with
  recommended-policy expected regret, or claim realized regret, accumulated
  UCB-VI, an explicit rate, stochastic reward confidence, or complete UCB-VI.

## Compiled Theorem Route: Adaptive Empirical-Transition Optimistic Source

- Leaf/route id:
  `RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-SOURCE-COUNT-CONFIDENCE`.
- Lean-facing target: compress every observed episode batch to all finite
  transition counts; construct a known-reward empirical transition plan and
  its deterministic optimistic policy table; prove the batch-to-table map is
  measurable; use the selected table to generate the next iid batch; and
  expose the exact adaptive conditional law plus the compiled global-delta
  simultaneous count-confidence terminal without caller-supplied source-law or
  selected-event measurability premises.
- Local APIs/imports: compiled adaptive batch-law route;
  `TransitionCountSummary`; `EpisodeBatch.transitionCountSummary`;
  `MeasurableEmbedding.natCast.measurable_comp_iff`;
  `measurable_of_countable`; `PMF.ofFintype`;
  `Kernel.ofFunOfCountable`; `Kernel.comap`; deterministic kernels;
  `EstimatedModelPlan.optimisticPolicy`; finite-table event decomposition;
  parent `trajectoryMeasure_condDistrib_eq_iidEpisodeBatchMeasure` and
  `trajectoryMeasure_adaptiveSimultaneousCountConfidence`.
- Proof route: prove every Nat transition-count coordinate measurable through
  its Real cast and assemble the Pi-valued summary; normalize each count row
  with a fallback Dirac law at zero; build a Markov empirical transition
  kernel and known-reward/fixed-bonus plan; use countability of the summary
  space to make its optimistic action table measurable; index iid generated
  batch laws by the finite deterministic table space; comap that kernel along
  the latest-batch selector; decompose selected bad events over all tables;
  then consume the parent conditional-law and adaptive count terminal.
- Regularity: finite measurable State/Action with decidable equality,
  measurable singletons, and nonempty types; probability initial-state law;
  explicit initial deterministic policy table, fallback state, fixed Real
  transition bonus, positive rounds/batch size, and `0 < delta <= 1` for the
  terminal. The conditional-law theorem separately requires standard Borel
  episode batches. No bonus nonnegativity, confidence calibration, occupancy
  margin, reward bound, or regret premise is used.
- Retrieval: no local memory hit for the concrete source; parent adaptive,
  empirical-model, iid-batch, and count-confidence routes;
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-FINSET-SUMS`, and exact Mathlib countable-measurability,
  `ofFunOfCountable`, PMF, and kernel-comap APIs; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-UCB-OPTIMISM` and `WEAPON-TAIL-INEQUALITIES` as inspiration only.
- Status: `leanCompiled`; the count summary, normalized PMF, empirical kernel,
  optimistic plan/table, measurable batch selector, table-indexed iid kernel,
  concrete adaptive source, exact selected policy/law, selected-event
  measurability, conditional law, and complete count terminal compile. Root
  import, eighteen public checks, an external source/conditional-law/two-round
  `delta = 1/2` terminal canary, and a Bool-state/action horizon-two semantic
  canary pass. The semantic canary covers a genuine `3/4` versus `1/4`
  empirical row, zero-count fallback, opposite empirical transitions,
  computed upper/Q values, distinct selected actions, and unequal optimistic
  policy tables. Placeholder and baseline-axiom audits pass. Independent
  review found no P0-P2; its canary-strength P3 is resolved. Retrieval indexes
  are refreshed, and the full gate passes with root 3507 jobs, Tests 3509 jobs,
  and 15 CLI tests with one expected skip.
- Failure policy: this is a genuine measurable empirical-transition source,
  but rewards are known, only the latest batch is used, and the fixed
  transition bonus is not statistically calibrated. Its downstream
  exploratory all-coordinate confidence/optimism and recommended-policy
  expected-regret route now compiles under explicit reachability/bonus-cover
  calibration. Do not
  infer automatic occupancy coverage, accumulated-data semantics, an explicit
  bonus rate, realized cumulative regret, or complete UCB-VI.

## Compiled Theorem Route: Adaptive Episode-Batch Count Confidence

- Leaf/route id:
  `RL-FINITE-HORIZON-ADAPTIVE-EPISODE-BATCH-COUNT-CONFIDENCE`.
- Lean-facing target: replace the independent finite product of fixed-policy
  batches by a Mathlib Ionescu--Tulcea trajectory. Coordinate zero uses one
  initial policy; after each finite prefix, a history-selected Markov policy
  supplies the exact next iid episode-batch law. Expose that conditional law,
  transport local adapted-event tails through `compProd`, and specialize the
  generic global-delta union to every selected policy's simultaneous count
  event.
- Local APIs/imports: compiled iid episode-batch and simultaneous-count routes;
  `AdaptiveEpisodeBatchSource`; `Kernel.trajMeasure`;
  `Kernel.condDistrib_trajMeasure`;
  `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`;
  `RewardKernel.trajMeasure_map_eval_zero`; `Measure.compProd_apply`;
  `lintegral_mono`; measurable Pi evaluation/restriction;
  `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`.
- Proof route: record the selected policy, history-indexed Markov batch kernel,
  and exact pointwise equality to its `iidEpisodeBatchMeasure`; construct the
  adaptive trajectory; identify the initial marginal and every prefix/next
  recurrence; apply Mathlib's regular conditional-distribution theorem; pull
  measurable initial/successor events to trajectory space; integrate uniform
  fiber bounds against the prefix law; allocate `delta / rounds`; then rewrite
  every selected-policy count-event fiber to the compiled fixed-policy tail and
  recover all coordinate deviations outside the finite union.
- Regularity: finite measurable State/Action with decidable equality and
  measurable singletons; probability initial-state law; positive rounds and
  batch size; `0 < delta <= 1`; a supplied source whose batch kernels are
  Markov and exactly the generated iid laws of the history-selected policies;
  measurability of each in-horizon selected-policy successor count event. The regular
  conditional-law endpoint additionally requires
  `StandardBorelSpace (EpisodeBatch mdp episodes)`; the count-confidence
  terminal itself does not.
- Retrieval: parent iid-batch/simultaneous-count/all-coordinate/offline-
  multibatch cards; Mathlib Ionescu--Tulcea, kernel, compProd/integral,
  finite-union, finite-sum, and order cards; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` as route evidence;
  `WEAPON-TAIL-INEQUALITIES` and `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; the adaptive source, trajectory law, initial marginal,
  exact prefix recurrence, selected-policy conditional law, generic adapted
  event integration/union, selected-policy count-event fibers, and global-delta
  adaptive count-confidence terminal compile. Root import, eighteen public
  checks, a constant-source Unit marginal/recurrence/conditional-law canary,
  and a genuinely history-sensitive Bool `Kernel.piecewise` source with both
  policy branches, measurable selected events, and a full two-round terminal at
  global `delta = 1/2` pass. Placeholder and baseline-axiom audits pass.
  Independent review found no P0-P2; both P3 findings on all-time regularity and
  weak canary semantics are resolved, and re-review found no remaining issue.
  Retrieval indexes are refreshed, and the full gate passes with root 3506
  jobs, Tests 3508 jobs, and 15 CLI tests with one expected skip.
- Failure policy: this theorem is adaptive in the batch-history law but still
  takes a lawful measurable source as input. It does not construct the concrete
  empirical optimistic-policy update, prove adaptive reward consistency,
  positive occupancy margins, full empirical-model confidence, cumulative
  bonus control, realized regret, or complete UCB-VI. A concrete
  known-reward/latest-batch empirical-transition optimistic source now compiles
  downstream; next lift adaptive reward support and calibrated all-coordinate
  confidence without reverting to an independent product law.

## Compiled Theorem Route: IID Multibatch Cumulative Confidence Regret

- Leaf/route id:
  `RL-FINITE-HORIZON-IID-MULTIBATCH-CUMULATIVE-CONFIDENCE-REGRET`.
- Lean-facing target: put `rounds` independent copies of the compiled fixed-policy
  iid episode-batch law under one Mathlib `Measure.pi`; allocate
  `delta / rounds` to each pulled-back simultaneous-count event; prove their
  finite union has mass at most global `delta`; construct all batch-specific
  `FiniteBatchModel.Confidence` witnesses almost everywhere off that union; and
  sum the resulting batch-specific optimistic-policy expected-regret bounds.
- Local APIs/imports: compiled
  `FiniteHorizonIIDAllCoordinateFiniteBatchConfidence`;
  `Measure.pi`; `measurePreserving_eval`; `MeasurePreserving.measure_preimage`;
  `ae_of_ae_map`; `ae_all_iff`; measurable Pi evaluation;
  `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`;
  `Finset.sum_le_sum`; `FiniteBatchModel.Confidence` optimism and selected-radius
  occupancy consumers.
- Proof route: define the finite product batch law and pulled-back roundwise bad
  events; use evaluation measure preservation to identify every marginal event
  mass with the single-batch event at local delta; apply equal-share union; pull
  mapped-batch reward consistency back through every evaluation coordinate and
  intersect the finitely many a.e. facts; outside the union construct one
  confidence witness for every round; apply per-round optimism/regret and sum the
  inequalities over `Fin rounds`.
- Regularity: finite measurable State/Action with decidable equality, measurable
  singletons, and nonempty Action; one fixed MDP, data-generating Markov policy,
  probability initial law, positive training-batch size, positive number of
  product rounds, `0 < delta <= 1`, fallback state, true reward absolute bound,
  nonnegative fixed transition budget, all-coordinate strict margins and the
  deterministic coordinate-radius cover at local budget `delta / rounds`.
  The derived optimistic policy may vary with each sampled batch.
- Retrieval: parent all-coordinate/reward/simultaneous-count/optimism local
  cards; `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`;
  exact local `Measure.pi` evaluation and finite-union APIs; `SCN-RL-MDP` and
  UCB-VI paper route evidence; optimism weapon inspiration only.
- Status: `leanCompiled`; the product law and exact coordinate marginals,
  measurable round/global events, equal-share tail, a.e. reward-consistency
  family, pathwise confidence family, deterministic cumulative consumer, and
  mapped global-delta optimism/cumulative expected-regret endpoint compile.
  Root import, sixteen declaration checks, and two-batch marginal, nontrivial
  local-tail, global-tail, a.e. support, positive-budget confidence, complete
  terminal, and horizon-two generic finite-sum canaries pass. Independent review
  found no production issue; its residual test-strength concern is resolved.
  Placeholder and public baseline-axiom audits pass, indexes are refreshed, and
  the full gate passes with root 3505 jobs, Tests 3507 jobs, and 15 CLI tests
  with one expected skip.
- Failure policy: this is an independent offline multibatch theorem under one
  fixed data-generating policy. It does not identify an adaptive online history
  law, make each round's training data depend on earlier optimistic policies,
  or turn the sum of expected regrets into realized cumulative regret. Preserve
  the local `delta / rounds` radius/cover contracts and do not call this complete
  UCB-VI.

## Compiled Theorem Route: IID All-Coordinate Finite-Batch Confidence

- Leaf/route id: `RL-FINITE-HORIZON-IID-ALL-COORDINATE-FINITE-BATCH-CONFIDENCE`.
- Lean-facing target: define a canonical finite-batch model with zero reward
  radius and one fixed transition budget; define deterministic transition
  coordinate radii from the genuine lower count margin
  `expectedCount - simultaneousCountConfidenceRadius`; prove the recursive
  optimistic value is bounded by `remaining * (rewardBound + transitionBudget)`;
  construct `MDP.FiniteBatchModel.Confidence` outside the existing simultaneous
  event; and expose the confidence producer almost everywhere under the mapped
  iid batch law with the unchanged global-delta tail.
- Local APIs/imports: compiled generated empirical-reward exactness route;
  `FiniteBatchModel`, `.plan`, `.Confidence`; `EstimatedModelPlan.upperValueRemaining`,
  `.optimisticBellman`, `.optimisticQ`, `.transitionValue`;
  `VisitCoordinate.expectedCount`, `.count`;
  simultaneous visit deviation and eligible transition-confidence consumers;
  `norm_integral_le_of_norm_le_const`; probability-kernel section instances;
  ordered-field reciprocal monotonicity; finite coordinate sums.
- Proof route: use the shared count event to prove
  `expectedCount - radius < visitCount`; transport the compiled random-denominator
  transition error to the larger deterministic denominator radius; obtain exact
  empirical rewards at all stage/state/action coordinates from reward consistency
  and full margins; induct on remaining horizon, bounding the empirical-kernel
  continuation integral by the previous envelope and adding the true reward and
  fixed transition budget; fill all four raw confidence fields; then combine the
  mapped-law a.e. reward-consistency support with the existing event tail.
- Regularity: finite measurable State/Action with decidable equality and
  measurable singletons; nonempty Action for optimistic finite maximization;
  fixed MDP/policy and probability initial law; explicit fallback state; positive
  episodes and `0 < delta <= 1` for the probability endpoint; strict expected
  count margin at every `VisitCoordinate`; a nonnegative transition budget;
  true rewards bounded in absolute value by `rewardBound`; deterministic finite coordinate-radius
  cover for each remaining horizon. No stochastic reward, adaptive episodes,
  anytime event, cumulative bonus sum, or complete UCB-VI theorem.
- Retrieval: empirical-model, simultaneous-count, eligible-transition, and
  generated-reward local cards; `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`; `SCN-RL-MDP`;
  UCB-VI paper evidence; optimism weapon inspiration only.
- Status: `leanCompiled`; the canonical model, deterministic lower-margin
  coordinate radius, recursive value envelope, pathwise confidence producer,
  mapped-iid a.e. confidence bundle, and optimism/expected-regret consumer compile.
  Root import, ten declaration checks, Unit/horizon-one direct and mapped-law
  canaries, a complete a.e. terminal payload canary, and a horizon-two nonzero
  envelope canary pass. Independent review findings are resolved; indexes and
  the baseline-only axiom audit pass. The full gate passes with root 3504 jobs,
  Tests 3506 jobs, and 15 CLI tests with one expected skip.
- Failure policy: do not use caller-selected partial eligibility to claim full
  confidence. Preserve the genuine positive denominator
  `expectedCount - radius`, fixed nonnegative transition budget, and explicit
  deterministic radius-cover inequality. Do not make the transition radius
  depend recursively on the upper-value envelope or claim that the cover follows
  without an occupancy/budget calculation. This route is fixed-policy and
  one-batch/one-episode; do not infer adaptive cross-episode or cumulative
  UCB-VI regret.

## Compiled Theorem Route: IID Generated Empirical Reward Exactness

- Leaf/route id: `RL-FINITE-HORIZON-IID-GENERATED-EMPIRICAL-REWARD-EXACTNESS`.
- Lean-facing target: define a reusable reward-consistency contract for finite
  episode batches; prove every batch extracted from genuine trajectories
  satisfies it and that mapped iid batches do so almost everywhere; identify
  its reward sum with visit count times `mdp.reward`;
  identify empirical reward with `mdp.reward` at every positive-count
  coordinate; and combine generated reward exactness with the compiled eligible
  transition bound on the existing simultaneous-count good event.
- Local APIs/imports: `FiniteHorizonIIDTrajectoryBatch`;
  `FiniteHorizonIIDEligibleEmpiricalTransitionConfidence`;
  `EpisodeBatch.visitCount`, `.rewardSum`, `.empiricalReward`;
  `MDP.episodeStepOfTrajectory`, `.episodeBatchOfTrajectories`;
  measurable record projections; `measurableSet_eq_fun`; `ae_map_iff`;
  `MarkovPolicy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent`;
  `.empiricalTransitionMass_abs_sub_transition_lt_of_not_mem_simultaneousCountBadEvent`;
  finite-sum casts/distributivity and positive-denominator field algebra.
- Proof route: record pointwise reward consistency; prove the generated
  instance by reduction; split each finite reward-sum term on the visit
  predicate and use consistency to replace the recorded reward; factor the
  constant reward out of the finite sum; cancel a nonzero visit-count cast in
  `empiricalReward`; obtain positivity for eligible coordinates from the
  existing margin; transport generated consistency through the mapped iid law;
  and package almost-everywhere reward equality together with every next-state
  transition inequality without allocating another failure budget.
- Regularity: the structural sum/exactness layer requires only finite episode
  indexing and decidable equality for State/Action. The generated eligible
  endpoint inherits finite measurable State/Action with measurable singletons,
  one fixed MDP/policy, a probability initial law, explicit fallback state, and
  a strict expected-count margin. Deterministic `mdp.reward` is essential; no
  reward range, variance, sub-Gaussian, integrability, or extra delta premise is
  needed. Zero horizon/empty eligible sets remain valid.
- Retrieval: parent empirical-model, iid-trajectory-batch, eligible-positivity,
  and eligible-transition-confidence local cards; `MLIB-FINSET-SUMS` and
  `MLIB-ORDER-ALGEBRA`; `SCN-RL-MDP`; UCB-VI paper evidence as route context;
  `WEAPON-UCB-OPTIMISM` as inspiration only.
- Status: `leanCompiled`; eleven public interfaces cover measurable reward
  consistency, generated and mapped-law support, exact sums/means, and the
  almost-everywhere eligible reward-plus-transition endpoint. Focused/root/Tests
  and semantic canaries pass; review P2/P3 findings were repaired; declaration,
  leaf, task-memory, and blueprint indexes plus the full repository gate pass.
- Failure policy: exactness applies only to reward-consistent/generated records
  and positive visits. An arbitrary raw `EpisodeBatch` may store unrelated
  rewards, and zero-count `empiricalReward = 0` need not equal `mdp.reward`.
  Do not reinterpret deterministic MDP rewards as noisy samples or claim a full
  `FiniteBatchModel.Confidence`; all-coordinate coverage and a noncircular
  upper-value envelope/radius construction remain downstream.

## Compiled Theorem Route: IID Eligible Visit-Count Positivity

- Leaf/route id: `RL-FINITE-HORIZON-IID-ELIGIBLE-VISIT-COUNT-POSITIVITY`.
- Lean-facing target: for any finite eligible set of stage/state/action
  coordinates satisfying
  `simultaneousCountConfidenceRadius < episodes * stageVisitProbability`,
  every eligible visit count is positive outside the compiled simultaneous
  bad event. The union of eligible zero-count events is measurable, is a
  subset of that bad event, and has mapped-batch measure at most global delta.
- Local APIs/imports: compiled
  `FiniteHorizonIIDSimultaneousCountConfidence`; `EpisodeBatch.visitCount`;
  `measurable_cast_visitCount`;
  `visitCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent`;
  `iidEpisodeBatch_simultaneousCountBadEvent_le`; `measurableSet_eq_fun`;
  `measure_mono`; `Nat.eq_zero_of_not_pos`; `Nat.cast_pos`; `linarith`.
- Proof route: define owned visit coordinates and their count, expected count,
  and zero-count event; form a finite eligible union; prove measurability;
  combine strict simultaneous deviation with the strict occupancy margin to
  rule out zero; prove zero-union subset; inherit the global-delta tail; expose
  a bundled good-event positivity endpoint.
- Regularity: finite measurable State/Action with decidable equality and
  measurable singletons; fixed MDP/policy and probability initial law; finite
  eligible set; positive episodes and `0 < delta <= 1` for the tail; a strict
  margin for each eligible coordinate. Zero horizon and empty eligible sets
  remain valid; reward is unused.
- Retrieval: parent simultaneous-count local card; `MLIB-ORDER-ALGEBRA`,
  `MLIB-FINTYPE-FIN`, `MLIB-MEASURE-INTEGRAL`; `SCN-RL-MDP`; UCB-VI paper
  route evidence; `WEAPON-UCB-OPTIMISM` inspiration only. No missing law
  transport remains because the theorem stays on the same mapped iid law.
- Status: `leanCompiled`; owned visit-coordinate/count/expected-count/zero-event
  APIs, event measurability, exact complement positivity, simultaneous-event
  positivity, zero-event subset, inherited global-delta tail, and bundled
  endpoint compile. Singleton and horizon-zero empty-eligible canaries,
  concrete `delta=1/2` margin/tail, empirical-transition denominator consumer,
  baseline axiom audit, and independent review pass.
- Failure policy: eligible positive denominators are closed under the explicit
  margin and are consumed by the compiled empirical transition-confidence
  route. Unreachable or low-occupancy coordinates remain excluded. Do not infer
  reward/adaptive/anytime/cumulative UCB-VI results.

## Compiled Theorem Route: IID Simultaneous Count Confidence

- Leaf/route id: `RL-FINITE-HORIZON-IID-SIMULTANEOUS-COUNT-CONFIDENCE`.
- Lean-facing target: define one finite index containing every stage/state/action
  visit coordinate and every stage/state/action/next-state joint-transition
  coordinate. At equal share `delta / card`, the union of all two-sided count
  bad events under `iidEpisodeBatchMeasure` has measure at most `ofReal delta`;
  outside it every indexed deviation is strictly below the common radius.
- Local APIs/imports: compiled `FiniteHorizonIIDCountConcentration` and
  `ProbabilityUnionBound`; fixed-coordinate measurable bad events and tails;
  `measure_biUnion_finset_le_of_uniform`; `Fintype.card_pos_iff`;
  `Finset.univ_nonempty`; `MeasurableSet.iUnion`; finite sum-type instances.
- Proof route: define coordinate/deviation/bad-event APIs; prove their
  measurability; dispatch each constructor to the compiled visit or
  joint-transition marginal theorem; split empty/nonempty coordinate types so
  horizon zero remains supported; apply exact equal-share finite union;
  derive coordinatewise strict inequalities outside the union; package both.
- Regularity: finite measurable State/Action with decidable equality,
  measurable singletons, and inherited nonempty instances; fixed MDP and one
  policy across episodes; probability initial law; positive episodes;
  `0 < delta <= 1`; no positive-horizon or reward assumption.
- Retrieval: parent RL cards; `TAIL-HOEFFDING-BOUNDED`, `TAIL-SUBGAUSS-SUM`,
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`; exact finite outer-measure
  union source; `SCN-RL-MDP` and UCB-VI paper route evidence;
  `WEAPON-TAIL-INEQUALITIES`/`WEAPON-UCB-OPTIMISM` inspiration only.
- Status: `leanCompiled`; `CountCoordinate`, its explicit finite-sum
  equivalence/cardinality theorem, deviation/bad-event measurability,
  constructor dispatcher, equal-share global union tail, visit/transition
  good-side consumers, and bundled endpoint compile. Horizon-two and
  zero-horizon canaries, baseline axiom audit, and independent review pass.
- Failure policy: the simultaneous count route is closed and its positivity and
  eligible empirical transition-confidence consumers compile downstream. Do
  not infer reward confidence, adaptive episode filtration, anytime confidence,
  cumulative regret, or complete UCB-VI from this count-only endpoint.

## Mathlib-Ready Leaf Contract

Finite-set, kernel, expectation, measurability, and Bellman recursion support
lemmas should be split into leaf-sized statements.  General probability or
dynamic-programming infrastructure should be marked as Mathlib candidates; the
finite-horizon RL interface itself stays project-local until the dependency
layer is selected.

## Build Gate

```bash
python3 tools/bandit.py check
```
