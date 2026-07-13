# Port the Explore-Then-Commit regret proof route

Task id: `BRL-ETC-PORT-001`
Kind: `literaturePort`
Status: `partial`
Harness: `hierarchical`

## Goal

Formalize or stage the Explore-Then-Commit regret proof route using ABRL's
finite-action surfaces and LML theorem cards.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.ETC.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.ETC`
- Local surface: `BanditRLProof/Algorithms/ETC.lean`
- Textbook/source card: `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-INDEPENDENCE`

## Current Supporting Leaf

`ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` is compiled locally as
`ETC.empMeanAtExploration_eq_of_eq_on_prefix`: equality of two reward traces
at every coordinate strictly before `spec.explorationPulls * K` implies equality
of every fixed-commit exploration empirical mean. It uses only the finite-sum
route (`sumRewards_eq_finset_filter_sum` and `Finset.sum_congr`) and has no
probability or regularity assumptions. This is the exact prerequisite for
reconstructing a commit score from a finite reward history. It neither builds
that history-derived policy nor transports an adaptive reward law, so the final
LML target remains open.

`ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now closes the next interface:
`History.completeRewardTrace` completes a history through state time `t` with
zero afterward, and
`ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le`
proves that it reproduces all fixed-commit exploration scores under
`spec.explorationPulls * K <= t + 1`. This matches the shifted generated action
convention exactly. It does not define the ETC finite-history policy, prove its
action trace equals the ETC trace, prove its measurability, or transport a
reward law.

`ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now closes the policy/action
surface itself. `ETC.explorationArgmaxHistoryPolicy` is measurable over a
completed finite reward history, and
`ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction` proves its
generated trace equals canonical `ETC.explorationArgmaxAction` under
`0 < spec.explorationPulls`. The remaining theorem-route blocker is no longer
the action definition, score reconstruction, or policy measurability; it is an
action-dependent adaptive reward law and conditional reward-law transport.

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now proves that law
for the canonical `RewardKernel.historyStepKernelFamily` trajectory measure:
the ETC policy is instantiated in the existing `trajMeasure` construction and
returns a full generated finite-pair `partialTraj` source. This is a genuine
action-dependent kernel probability law, but it does not identify the kernel
trajectory with the fixed product-coordinate source or an arbitrary adaptive
bandit environment.

`ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now consumes
that canonical law into Mathlib `HasCondSubgaussianMGF` for the successor
reward centered at `model.mean` of the selected arm. It assumes a centered
reward-kernel law and a selected-history variance ceiling. Thus the remaining
abstract gap was centered model-law construction and trajectory/source
transport, plus finite-sum concentration assembly. The bounded finite-arm leaf
below closes the centered-law part for a common interval.

`ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now closes the raw kernel
construction part: `RewardKernel.contextIndependentOfActionLaws` turns
action-indexed probability measures into a context-independent Markov reward
kernel, and its selected measure is the original arm law. The proof uses
`Kernel.ofFunOfCountable` and `Kernel.comap Prod.snd`; for `Fin K`, countability
is automatic. This raw constructor alone does not prove that each arm law has
`model.mean`, bounded support, or a centered sub-Gaussian variance proxy; the
next compiled leaf supplies those fields for common-bounded laws.

`ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now closes that model-law
bridge for the common bounded-reward route. Per-arm probability laws that are
a.s. in `[lo, hi]`, a.e. measurable after casting to Real, and have exact
integral `model.mean arm` construct `ETC.finiteArmBoundedCenteredRewardKernelLaw`.
The direct theorem
`ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws`
then supplies the canonical generated-history conditional MGF at the common
Hoeffding proxy, with no abstract centered-law or variance-ceiling input. The
downstream full-sum leaf now closes the time-zero initial-law MGF and finite-sum
tail for the total selected centered reward process.

`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT` now removes common
bounded support from the canonical concentration layer. Per-arm `Rat`
probability laws with exact model means and direct centered
`HasSubgaussianMGF` witnesses at one common `sigma2` construct the centered
kernel law, the generated-history successor conditional MGF, the initial and
fixed-filtration reward witnesses, and finally
`ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws`. The
process is the existing one-sided masked centered pairwise difference over the
fixed exploration horizon and takes no arm union. Its commit-fiber, canonical
per-arm Bochner, external scheduled-arm, and full-history constant-law
consumers now compile downstream. The action-dependent law adapter, Real
rewards, and exact argmax tie semantics remain separate.

`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET` now
consumes that contract through the concrete non-best commit fiber, finite
ENNReal-to-Real tail conversion, and the measurable per-arm Bochner assembly.
The compiled endpoint
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal`
preserves one gap-weighted direct-MGF tail per arm, removes the best-arm term
with `gap_bestArm`, and assumes no bounded support, max-gap collapse, arm
union, or coordinate independence. Its exploration-prefix, generic
initial/successor `condDistrib`, and scheduled exploration-arm transports now
compile as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
The public scheduled endpoint fixes `Context := Unit`, assumes no bounded
support or arm union, and exposes no local kernel/state/context. Its LML-shaped
full action/reward-history constant-law consumer now compiles as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
Its action-dependent selected-kernel consumer now also compiles as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`,
closing the dependency-light direct-MGF `Rat` law transport. Real rewards,
exact LML constants/pull-count, direct upstream integration, and tie semantics
remain separate.

`ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` fixes the initial trajectory
law to `armLaw (ETC.exploreArm spec 0)`, proves its zeroth coordinate marginal,
and combines the resulting initial MGF with successor conditional MGF witnesses
through Mathlib Azuma-Hoeffding. The sum contains all times in
`Finset.range n`.

`ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now closes the required
empirical-mean comparison route under the same canonical trajectory. Generated
actions agree with the fixed round-robin trace throughout exploration, which
identifies the finite-pair history filtrations. The bounded selected-reward MGF
witnesses therefore instantiate the existing centered pairwise conditional
tail contract and finite non-best-arm union, yielding
`ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws`.

`ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now completes that canonical
assembly. It names the finite ENNReal and Real wrong-commit budgets, proves the
Real probability wrapper by `ENNReal.toReal_mono`, derives commit and wrong-set
measurability from coordinatewise empirical-mean measurability, derives
pseudo-regret integrability from the finite measurable commit selector, and
invokes the generic exploration-plus-`model.maxGap` Bochner consumer. The final
endpoint is
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal`.

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET` now factors that
integrand through the measurable exploration reward prefix
`Finset.Iic (spec.explorationPulls * K - 1)` and transports the canonical
Bochner bound to any external `RewardTrace Rat` probability law with the same
prefix pushforward. Full infinite-trajectory equality and suffix reward laws
are not required.

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET` now discharges
that prefix hypothesis from an explicit external process contract. The generic
`RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib` induction
uses the zeroth reward marginal and `condDistrib` of reward `i+1` given the
prefix through `i`; the ETC consumer needs these laws only for
`i < spec.explorationPulls * K - 1` and pulls the resulting integral back to
the original sample space. No suffix law or full trajectory equality is used.

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET`
now removes the project-local step kernel from the environment contract.
During exploration the policy-selected `historyStepKernelFamily` reduces to
`armLaw (ETC.exploreArm spec (i+1))`, so callers state only the initial
exploration-arm law and the scheduled exploration-arm conditional laws. The
next law bridge is from a concrete environment source or LML `IsAlgEnvSeq` to
those conditional laws.

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
now closes the local conditioning-variable transport matching the LML feedback
fields. A constant scheduled-arm law conditioned on the full finite
action/reward history and next action is projected to the reward-only prefix;
the time-zero constant conditional law supplies the initial reward marginal.
At seed `19dc3ab`, the remaining LML-specific adapter is precisely to combine
`IsAlgEnvSeq.hasCondDistrib_feedback(_zero)`, `stationaryEnv`, and
`ETC.arm_of_lt` so the action-dependent kernel becomes this constant law.

`ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
now closes that adapter in dependency-light form. Raw action-selected kernels
plus a.e. exploration action identities are converted to constant scheduled-
arm laws with `ae_map_iff`, then consumed by the full-history theorem. A direct
`IsAlgEnvSeq` wrapper is now only a toolchain integration task; the mathematical
law transport no longer blocks the bounded Rat theorem route.

The recorded LML seed statement has also been audited exactly. Its conclusion
is a per-arm gap-weighted pull-count bound for arbitrary Real-valued arm laws
with a common `HasSubgaussianMGF` proxy under `IsAlgEnvSeq` and
`stationaryEnv`. Thus law transport is not the only LML mismatch: the local
bounded Rat model, fold-argmax tie rule, and max-gap finite-union RHS are strict
specializations that still require separate ports.

## Lean Target

```lean
-- compiled fixed-product endpoint:
-- ETC.integral_real_pseudoRegret_explorationArgmaxAction_le_explorationMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_exploreMean
-- compiled canonical generated-history kernel endpoint:
-- ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal
-- compiled external exploration-prefix-law endpoint:
-- ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq
-- future exact Real/sub-Gaussian/per-arm theorem compatible with Bandits.ETC.regret_le
```

## Proof Obligations

- [x] Prove round-robin exploration counts and exploration/actionWithCommit alignment.
- [x] Map the finite empirical-mean argmax commit.
- [x] Prove fixed-product bounded-reward wrong-commit probability and Bochner regret assembly.
- [x] Connect the fixed-product source to a canonical round-robin exploration expected-regret endpoint.
- [x] Reconstruct fixed-commit exploration scores from a finite reward history once it covers the exploration horizon.
- [x] Construct a measurable finite-history ETC policy and prove its generated action trace equals the canonical ETC action generator.
- [x] Construct the canonical action-dependent Markov-kernel `trajMeasure` partial-trajectory law for that ETC policy.
- [x] Derive canonical trajectory conditional sub-Gaussian MGF at the selected finite-bandit model mean under a centered kernel law and selected-history variance ceiling.
- [x] Construct a context-independent Markov reward kernel from finite-arm probability laws and expose selected-measure equality.
- [x] Construct its bounded centered model-mean law and derive the canonical generated-history successor conditional MGF directly from arm laws.
- [x] Replace bounded support at the canonical concentration layer by direct common-proxy per-arm `HasSubgaussianMGF` witnesses and compile the full pairwise empirical-mean tail contract.
- [x] Consume the direct common-sub-Gaussian pairwise contract into concrete commit-fiber probabilities, finite Real tails, and the canonical gap-weighted per-arm Bochner expected-regret theorem.
- [x] Align the initial arm law and prove a canonical one-sided finite-horizon tail for the full centered reward sum including time zero.
- [x] Build the canonical pairwise empirical-mean tail contract and wrong-commit finite-union probability directly from bounded finite-arm laws.
- [x] Assemble the canonical `trajMeasure` Bochner expected-regret endpoint from the compiled wrong-commit probability, commit measurability, probability conversion, and integrability consumers.
- [x] Transport the bounded canonical result to an arbitrary external reward-trace law under equality of the finite exploration-prefix pushforwards.
- [x] Derive the exploration-prefix pushforward identity from an explicit initial marginal plus successor `condDistrib` environment contract.
- [x] Expose a practical stationary exploration-arm `condDistrib` contract with no caller-visible local step kernel, state, policy kernel, or trajectory measure.
- [x] Coarsen LML-shaped full action/reward-history constant feedback laws to the scheduled-arm reward-prefix contract and derive the initial marginal.
- [x] Combine action-selected feedback kernels and exploration action a.e. equality into constant full-history scheduled-arm laws.
- [x] Assemble Bochner ETC regret with a separate gap-weighted probability term for every commit arm.
- [ ] Optionally add a direct newer-toolchain `IsAlgEnvSeq` wrapper translating `HasCondDistrib` and `ETC.arm_of_lt` into the compiled dependency-light hypotheses.
- [x] Bound each concrete non-best commit event by its corresponding pairwise empirical-mean tail.
- [x] Convert the canonical armwise ENNReal tails to Real and substitute them termwise into the per-arm Bochner assembly.
- [x] Transport the canonical per-arm Bochner integral through equality of the finite exploration-prefix pushforwards.
- [x] Derive the external per-arm theorem from an initial reward marginal plus successor `condDistrib` laws through the exploration prefix.
- [x] Expose the per-arm theorem directly from the stationary laws of the scheduled exploration arms.
- [x] Coarsen LML-shaped full action/reward-history constant feedback laws to the scheduled-arm per-arm theorem.
- [x] Combine action-selected feedback kernels and exploration action a.e. equality into the full-history per-arm theorem.
- [x] Transport the canonical direct common-sub-Gaussian per-arm Bochner theorem through exploration-prefix equality, initial/successor conditional laws, and scheduled exploration-arm conditional laws.
- [x] Coarsen LML-shaped full action/reward-history constant feedback laws to the scheduled-arm direct common-sub-Gaussian per-arm theorem.
- [x] Combine action-selected feedback kernels and exploration action a.e. equality into the full-history direct common-sub-Gaussian per-arm theorem.
- [x] Compile exact constants, per-arm pull counts, cast-pushforward Real-kernel gaps, and the canonical finite-sum regret endpoint.
- [x] Compile native Real finite-prefix law transport and the scheduled initial/successor `condDistrib` external exact-regret endpoint.
- [ ] Map the actual upstream `IsAlgEnvSeq (etcAlgorithm ...) (stationaryEnv nu)` fields to the compiled `hzero`, `hcond`, and finite-horizon action-equality premises, then prove upstream/local argmax tie equivalence; optionally add the direct newer-toolchain LML wrapper separately.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-ETC-PORT-001.md`.  Generic finite-cycle arithmetic and
regularity lemmas should be treated as Mathlib candidates; ETC-specific
algorithm wrappers stay project-local.  Do not change the proof route without
recording the missing assumption, counterexample, or source mismatch.

## Build Gate

```bash
python3 tools/bandit.py check
```

## Current Supporting Leaf: Real Mean-Regret Pull-Count Decomposition

- Lean statements: `realMeanGap`, `realMeanRegret`,
  `realMeanRegret_eq_finset_sum_gap`,
  `realMeanRegret_eq_sum_gap_mul_pullCount`,
  `integrable_realMeanRegret_of_integrable_pullCount`, and
  `integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount`.
- Local APIs/imports: `BanditRLProof.RealMeanRegretPullCount`, `ActionTrace`,
  `pullCount_eq_finset_filter_card`, `Finset.sum_fiberwise'`,
  `IntegrabilitySums.integrable_univ_sum`, and
  `ExpectationBochnerSums.integral_univ_sum`.
- Proof route: rewrite `n * iSup mean - sum mean(action)` to the finite
  selected-gap sum, group its fibers by arm, and exchange the finite arm sum
  with the Bochner integral.
- Regularity contracts: arbitrary measure on a measurable sample space,
  `mean : Fin K -> Real`, and integrability of each Real-cast pull count. No
  probability, reward kernel, environment law, concentration, or tie premise.
- Retrieval evidence: exact LML seed scalar gap/regret/pull-count declarations,
  Mathlib finite-sum/integral APIs, and compiled local pull-count wrappers. The
  LML source is target evidence, not an imported proof.
- Status: `leanCompiled`; focused module and external `Tests.Basic` canary pass.
- Failure policy: the stationary-kernel identity-integral specialization now
  compiles downstream. Do not coerce back
  through `FiniteBanditModel`'s `Rat` means or claim `Bandits.ETC.regret_le`
  before kernel, constants, concentration, and measurableArgmax contracts
  compile.

## Independent Review

The read-only local review found no Lean, mathematical, canary, or leaf-card
contract defect in `REAL-MEAN-REGRET-PULLCOUNT`. It specifically checked the
empty-`Fin` boundary, the `iSup` semantics against the exact LML seed, arm-fiber
regrouping, and pull-count integrability. The one P2 finding was unrelated to
the theorem: bounded blueprint snapshots were cut in the middle of lines and
the structured route JSON was truncated. `tools/bandit.py` now emits explicit
line-safe head/tail Markdown snapshots and embeds the full structured roadmap;
`tools/test_bandit_cli.py` covers the line-boundary behavior, and the regenerated
roadmap JSON parses successfully.

## Current Supporting Leaf: Real Kernel Regret Pull-Count Decomposition

- Lean statements: `realKernelMean`, `realKernelGap`, `realKernelRegret`,
  `realKernelGap_nonneg`, `realKernelRegret_eq_finset_sum_gap`,
  `realKernelRegret_eq_sum_gap_mul_pullCount`,
  `integrable_realKernelRegret_of_integrable_pullCount`, and
  `integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount`.
- Local APIs/imports: `Mathlib.Probability.Kernel.Integral` and
  `BanditRLProof.RealMeanRegretPullCount`.
- Proof route: define each arm mean as `integral (nu a) id`, specialize the
  compiled Real mean-regret definitions, use `le_ciSup` for gap nonnegativity,
  and reuse the deterministic and Bochner pull-count theorems.
- Regularity contracts: `nu : Kernel (Fin K) Real`, an arbitrary measure on a
  measurable action sample space, and integrability of every Real-cast pull
  count. Only `realKernelGap_nonneg` needs `Nonempty (Fin K)`. No Markov or
  probability-kernel instance, identity integrability, environment law,
  concentration, independence, or argmax premise is used.
- Retrieval evidence: Mathlib `Kernel.Integral`, the exact LML seed's
  identity-integral gap/regret definitions, the prior Real mean leaf, and
  `LML-BANDIT-REGRET-PULLCOUNT`. LML remains card-only.
- Status: `leanCompiled`; focused module and exact external `Tests.Basic`
  endpoint canary pass.
- Failure policy: kernel scalar bookkeeping is closed, and the downstream
  count-to-commit-probability expected-count endpoint now compiles. The next
  route leaf must prove the exact Real exponential commit-fiber probability
  bound or isolate its first missing empirical-reward/independence law. Do not
  add another Rat transport wrapper or report `Bandits.ETC.regret_le` before
  that producer and measurableArgmax alignment compile.
- Independent review: no mathematical, Lean, canary, or metadata finding. It
  confirmed identity-integral equivalence with the fixed LML seed, honest lack
  of an integrability premise at this algebraic layer, finite-`Fin` boundedness
  for `le_ciSup`, and sufficient pull-count integrability. The new module is
  intentionally still Git-untracked in the current dirty worktree; any later
  commit must include it together with the umbrella import.

## Current Supporting Leaf: Real ETC Expected Pull Count

- Lean statements:
  `ETC.integrable_real_pullCount_actionWithCommit_choice_of_measurable_commit`,
  `ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_suffix_mul_commit_prob`,
  `ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob`,
  and
  `ETC.integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le`.
- Local APIs/imports: Mathlib Bochner set integrals and probability-measure
  typeclasses, `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`,
  `measurable_natCast_pullCount`, `pullCount_le_time`, `integral_indicator`,
  `setIntegral_const`, and `Measure.real`.
- Proof route: derive timewise measurability of the finite-valued ETC action,
  prove arbitrary-horizon Real pull-count integrability by `pullCount <= n`,
  rewrite the suffix count as a constant plus the indicator of `{commit=a}`,
  integrate exactly, normalize the horizon to `n - K*m`, and multiply the
  supplied commit-fiber probability bound by the nonnegative suffix.
- Regularity contracts: a measurable sample space, a probability measure,
  measurable `commit : Omega -> Fin K`, and `K * explorationPulls <= n` for
  the LML-shaped endpoint. Integrability alone only needs a finite measure.
  No reward law, empirical mean, independence, MGF, concentration constant,
  optimal-arm assumption, or argmax/tie rule is used.
- Retrieval evidence: exact LML `ETC.pullCount_of_ge` and
  `ETC.expectation_pullCount_le` route, `MLIB-MEASURE-INTEGRAL`, the compiled
  ETC suffix count and measurable pull-count leaves, and
  `REAL-KERNEL-REGRET-PULLCOUNT`. LML remains theorem-card evidence only.
- Status: `leanCompiled`; focused module and exact external `Tests.Basic`
  endpoint canary pass.
- Failure policy: counting, integrability, and commit-fiber integration are
  closed. The next leaf must prove the exact Real exponential bound on
  `mu.real {omega | commit omega = a}` from empirical reward laws and
  measurable argmax semantics. Do not hide concentration in this consumer or
  report `Bandits.ETC.regret_le` before that producer compiles.
- Independent review: no mathematical, Lean regularity, horizon-arithmetic,
  canary, or metadata finding. The reviewer checked `K = 0` exclusion through
  `ETC.Spec.hK`, the `m = 0` and zero-suffix boundaries, indicator integration,
  and the absence of hidden concentration assumptions. Residual work is the
  concrete Real reward-law/sub-Gaussian commit-fiber bound, actual ETC trace
  alignment, measurableArgmax tie semantics, and the later `m != 0` premise
  needed by empirical-mean concentration.

## Current Supporting Leaf: Exact Common-Sub-Gaussian Per-Arm Expected Pull Count

- Lean statements:
  `ETC.sum_centeredPairwiseRewardDiffVarianceProxy_const_eq_two_mul`,
  `ETC.centeredPairwiseGapThreshold_eq_explorationPulls_mul_gap`,
  `ETC.canonicalSubGaussianArmPairwiseTailReal_eq_exp_neg_explorationPulls_mul_gap_sq_div_four_mul`,
  `ETC.real_measure_explorationArgmaxCommit_eq_arm_le_exp_neg_explorationPulls_mul_gap_sq_div_four_mul_of_armLaws`,
  and
  `ETC.integral_real_pullCount_explorationArgmaxAction_le_exploration_add_remaining_mul_exp_of_armLaws`.
- Local APIs/imports: the canonical direct-MGF commit-fiber theorem in
  `ETCFiniteArmRewardLaw`, the abstract Bochner count consumer in
  `ETCExpectedPullCount`, masked pairwise variance proxies, exact exploration
  pull counts, `Finset.filter` cardinalities, `Mathlib.Tactic.FieldSimp`, and
  `Mathlib.Tactic.Ring`.
- Proof route: partition the pairwise proxy into candidate-arm and best-arm
  indicators, replace both cardinalities by `m`, rewrite the non-best
  threshold as `m * gap`, normalize the Real exponent with a separate
  `sigma2 = 0` branch, apply the canonical fiber theorem, and compose with the
  expected-count consumer.
- Regularity contracts: `0 < m`, `K*m <= n`, a non-best arm, per-arm `Rat`
  probability laws with exact means after casting to Real, centered Real
  `HasSubgaussianMGF` witnesses at one common `NNReal` proxy, and a measurable
  generated-history context. The random variables are the existing masked
  centered pairwise reward differences. The event is one-sided, fixed-horizon,
  and for one arm; there is no union over arms. Internally, the canonical
  context-independent reward kernel derives successor conditional MGFs from
  the arm-law MGFs and transports them to `historyFiltrationSucc` through the
  exploration-prefix measurable-space equality. This does not cover an
  arbitrary adaptive reward kernel.
- Retrieval evidence: exact LML `ETC.expectation_pullCount_le` exponent and
  constant, the compiled direct-MGF Rat arm-law chain, Mathlib finite-sum and
  measure/concentration APIs, and `REAL-ETC-EXPECTED-PULLCOUNT`. LML remains
  theorem-card evidence rather than a local import.
- Status: `leanCompiled`; focused module and exact external `Tests.Basic`
  endpoint canary pass.
- Failure policy: exact common-proxy arithmetic and the canonical Rat-arm-law
  per-arm expected-count endpoint are closed. The next route leaf must
  transport this producer to a native Real reward kernel/`IsAlgEnvSeq` law and
  kernel gap, then align the actual upstream action and measurableArgmax tie
  semantics. Do not report `Bandits.ETC.regret_le` as ported from this leaf.
- Independent review: no P0/P1 finding. One P2 ledger omission was fixed by
  recording the internal successor conditional-MGF and
  exploration-prefix-to-`historyFiltrationSucc` transport route. The reviewer
  confirmed the exact constant algebra, zero-proxy total-division branch,
  positive-exploration/non-best/horizon premises, canary, and Rat/Real claim
  boundary. Residual blockers are native Real kernel/`IsAlgEnvSeq` transport,
  upstream action/tie alignment, and then-pending finite-arm kernel-regret
  assembly; the latter is now closed by the following leaf.

## Current Supporting Leaf: Rat Arm-Law Real-Kernel Exact Regret

- Lean statements: `ETC.ratArmLawRealKernel`, its application and Markovness
  theorems, the two kernel-mean identification theorems,
  `ETC.ciSup_modelMean_cast_eq_bestArm`,
  `ETC.realKernelGap_ratArmLawRealKernel_eq_modelGap`, and
  `ETC.integral_realKernelRegret_explorationArgmaxAction_le_exact_sum_of_armLaws`.
- Local APIs/imports: `Measure.map`, `Measure.isProbabilityMeasure_map`,
  `integral_map`, `Kernel.ofFunOfCountable`, `ciSup_le`, `le_ciSup`, finite
  model best-arm/gap invariants, `RealKernelRegretPullCount`, and the exact
  common-sub-Gaussian per-arm count endpoint.
- Proof route: push each Rat arm law through the cast to Real; prove the kernel
  is Markov and its identity integral is the original cast mean; identify the
  finite mean `iSup` at `model.bestArm` and hence every kernel gap; apply the
  kernel regret expected-pull-count equality; discharge count integrability
  from measurable commit; remove the zero best-arm summand; and use every
  non-best exact expected-count bound under `Finset.sum_le_sum`.
- Regularity contracts: `0 < m`, `K*m <= n`, per-arm Rat probability laws,
  exact Real-cast means, centered Real `HasSubgaussianMGF` witnesses with one
  common `NNReal` proxy, and a measurable canonical history context. The Real
  kernel is specifically the cast pushforward of the Rat laws and the sample
  trajectory remains the canonical generated Rat history. It is not an
  arbitrary native Real stationary environment or `IsAlgEnvSeq` process.
- Retrieval evidence: exact LML `Bandits.ETC.regret_le` finite-sum RHS,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
  `REAL-KERNEL-REGRET-PULLCOUNT`, and the exact per-arm count leaf. LML remains
  theorem-card evidence rather than an imported proof.
- Status: `leanCompiled`; focused module and full endpoint `Tests.Basic`
  canary pass.
- Failure policy: canonical kernel mean/gap identification and finite-arm
  exact regret assembly are closed. The downstream native Real product and
  finite-prefix/conditional-law leaves now close the arbitrary external-law
  transport. Do not report this Rat pushforward theorem itself as native Real
  or as the final LML port.
- Independent review: no P0-P2 finding. The reviewer verified the `Measure.map`
  and `integral_map` direction, `Kernel.ofFunOfCountable` Markov proof,
  conditional-`iSup` nonempty/bounded contracts, exact kernel-gap equality,
  best/non-best finite-sum branches, LML constant shape, canary, and Rat/native
  Real claim boundary. Its then-open native law and regret-integral transport
  now compile downstream; upstream `IsAlgEnvSeq` field extraction and
  action/`measurableArgmax` tie alignment remain.

## Current Supporting Leaf: Native Real Empirical Mean, Argmax, And Count

- Lean statements: `ETC.realEmpMeanAtExploration`, its denominator rewrite and
  measurability theorem, `ETC.realArgmaxCommit` and maximality certificate,
  direct finite-fold measurability, the reward-dependent commit/action, and
  exact plus upper expected pull-count consumers.
- Local APIs/imports: `measurable_sumRewards`, `Finset.measurable_sum`,
  `measurableSet_eq_fun`, `measurableSet_lt`, `Measurable.ite`, finite
  `List.foldl`, exact exploration counts, and `ETCExpectedPullCount`.
- Proof route: form exploration means in Real; prove the finite fold selects a
  maximum; express a dynamically selected coordinate as a finite indicator
  sum; induct through comparison/selection measurability; instantiate the
  generic count integration theorem.
- Regularity contracts: timewise measurable Real reward coordinates and
  positive `K`; the exact count endpoint additionally needs a probability
  measure and `K*m <= n`. No law, conditional MGF, concentration, kernel, best
  arm, or `IsAlgEnvSeq` premise is used.
- Retrieval evidence: exact LML empiricalMean/measurableArgmax/action route,
  Mathlib measurable finite sums/comparisons, and the compiled local
  measurable-sum and expected-count leaves. LML remains card-only.
- Status: `leanCompiled`; focused module build and external maximality/count
  canaries pass.
- Failure policy: native Real empirical means, local deterministic tie rule,
  selector measurability, and count consumption are closed. Downstream native
  concentration, prefix-law, selected feedback-law exact-regret transport,
  least-encoded tie semantics, and three-piece action assembly now compile.
  This leaf alone is not the final ETC theorem; downstream leaves now close the
  source-shaped `empMean'`/history score bridge and faithful local field
  compatibility, leaving only actual cross-toolchain LML symbol import.

## Current Supporting Leaf: Native Real External Prefix-Law Exact Regret

- Lean statements: `ETC.realExplorationRewardPrefix`,
  `ETC.realKernelRegretOfExplorationPrefix`,
  `ETC.real_trajMeasure_const_eq_infinitePi`,
  `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_prefixLaw_eq_infinitePi`,
  and
  `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib`.
- Local APIs/imports: `ETCRealInfinitePiTail`,
  `RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib`,
  `History.finiteRewardHistoryOfTrace`, `Measure.map_map`, `integral_map`,
  constant `Kernel.trajMeasure`, `Measure.infinitePiNat`, the infinite-product
  projective-limit uniqueness APIs, and the native Real regret/count surface.
- Proof route: factor empirical means, the local finite-fold commit, the ETC
  action, and finite-horizon kernel regret through `Fin (m*K)` rewards; prove
  the resulting regret functional measurable; transport its integral across
  equal prefix pushforwards; identify the constant Ionescu-Tulcea trajectory
  measure with `Measure.infinitePi`; then derive the prefix equality from the
  zeroth marginal and successor finite-reward-history `condDistrib` laws.
- Regularity contracts: arbitrary measurable external sample space with a
  probability measure, coordinate-measurable Real rewards, a Markov Real arm
  kernel, common centered `HasSubgaussianMGF` proxy, `0 < m`, `K*m <= n`, the
  scheduled zeroth arm law, scheduled successor laws through exploration, and
  a.e. agreement of the external action with the local action only for
  `t < n`. No `StandardBorelSpace Omega`, external action measurability, full
  trajectory law, or infinite-horizon action equality is required.
- Retrieval evidence: exact upstream LML `IsAlgEnvSeq` field shape and
  `Bandits.ETC.regret_le` route, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, Mathlib
  projective-limit APIs, the compiled native Real `infinitePi` exact theorem,
  and the generic finite-prefix conditional-law uniqueness theorem. LML is
  source/card evidence, not a local dependency.
- Status: `leanCompiled`; focused module build and both public `Tests.Basic`
  canaries pass.
- Failure policy: native Real prefix factorization, prefix-law transport, and
  scheduled initial/successor conditional-law transport to the exact external
  finite-sum regret bound are closed. The source adapter below now maps the
  upstream-shaped feedback fields to `hzero` and `hcond`, and the later
  least-encoded action leaf closes tie/action assembly. Do not reopen
  concentration, demand full trajectory-law equality, or report this wrapper
  as `Bandits.ETC.regret_le`.

## Current Supporting Leaf: Native Real Action-Dependent Source Exact Regret

- Lean statement:
  `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib`.
- Local APIs/imports: `ETCRealPrefixLawTransport`,
  `RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected`,
  `RewardKernel.map_eq_of_condDistrib_ae_eq_const`,
  `RewardKernel.condDistrib_ae_eq_const_of_comp`,
  `RewardKernel.contextIndependentOfActionLaws`, full finite pair histories,
  and their measurable reward projection.
- Proof route: use a.e. round-robin exploration actions to turn the initial and
  successor action-selected feedback kernels into scheduled constant arm laws;
  extract the zeroth reward marginal; coarsen every full pair-history/next-
  action condition to the finite reward prefix; invoke the native Real exact
  scheduled-law theorem without changing its finite-sum RHS.
- Regularity contracts: arbitrary measurable probability space, measurable
  action and Real reward coordinates, Markov Real arm kernel, common centered
  `HasSubgaussianMGF` proxy, `0 < m`, `K*m <= n`, exploration action equality,
  upstream-shaped initial and successor selected feedback laws, and a.e.
  equality with the local native ETC action only for `t < n`. No
  `StandardBorelSpace Omega`, full trajectory law, independence premise, or
  infinite-horizon action equality is added.
- Retrieval evidence: pinned LML seed
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, exact `IsAlgEnvSeq` feedback
  fields, `stationaryEnv`, `ETC.arm_of_lt`, Mathlib condDistrib/map APIs, and
  the prior native Real prefix-law leaf. LML remains source/card evidence.
- Status: `leanCompiled`; focused module, umbrella, and exact public canary
  builds pass.
- Failure policy: mathematical feedback-field mapping to `hzero` and `hcond`
  is closed. The downstream least-encoded action adapter now closes local tie
  semantics and three-piece action assembly. Do not add stronger law
  assumptions or claim the upstream declaration is locally imported.

## Native Real Least-Encoded Action Exact Regret

- Leaf id: `ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET`.
- Lean statements:
  `ETC.realLeastEncodedArgmax_eq_realArgmaxCommit`,
  `ETC.eventually_realExplorationArgmaxAction_eq_of_roundRobin_leastEncodedCommit_persist`,
  and
  `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_leastEncodedCommit_persist`.
- Local APIs/imports: `Mathlib.Data.List.MinMax`, `List.argmax`,
  `List.index_of_argmax`, `List.idxOf_finRange`, `Nat.find_spec`,
  `Nat.find_min'`, `Encodable.encode_injective`, `ETCRealEmpiricalMean`,
  `ETCTrace`, and `ETCRealSourceAdapter`.
- Proof route: identify the strict-update fold with first-occurrence
  `List.argmax`; use `idxOf_finRange` to prove least-encode selection; build the
  LML-shaped `Nat.find` selector and prove equality by encode injectivity;
  combine round-robin exploration, the commit action at `K*m`, and persistence
  into all-time equality with `realExplorationArgmaxAction`; invoke the source
  adapter without a caller-supplied horizon action equality.
- Regularity contracts: arbitrary measurable probability space, measurable
  action and Real reward coordinates, Markov Real arm kernel, common centered
  MGF proxy, positive exploration, horizon fit, exploration action laws,
  least-encoded local-score commit, persistence, and selected initial/successor
  feedback laws. No sample-space standard-Borel, full trajectory law,
  independence, preassembled horizon equality, or extra infinite equality is
  assumed.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, the `measurableArgmax`
  least-`Encodable.encode` `Nat.find` definition, `ETC.arm_of_lt`,
  `ETC.arm_mul`, `ETC.arm_of_ge`, Mathlib `List.MinMax`, and the compiled source
  adapter. LML remains card-only.
- Status: `leanCompiled`; focused module and two public canaries pass.
- Failure policy: local tie semantics and exploration/commit/persistence action
  assembly are closed. The downstream history-score source leaf now proves the
  `empMean'`-shaped finite-history equality, and the faithful local field
  consumer compiles downstream. Only actual cross-toolchain LML symbol import
  remains.

## Native Real History-Score Source Exact Regret

- Leaf id: `ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET`.
- Lean statements: `ETC.realHistoryPullCount`,
  `ETC.realHistorySumRewards`, `ETC.realHistoryEmpMean`, their three
  `finitePairHistoryOfTrace` equalities,
  `ETC.realHistoryEmpMean_exploration_eq_realEmpMeanAtExploration`, and
  `ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_historyLeastEncodedCommit_persist`.
- Local APIs/imports: `ETCRealArgmaxTie`,
  `History.finitePairHistoryOfTrace`, `pullCount_eq_finset_filter_card`,
  `sumRewards_eq_finset_filter_sum`, `Finset.sum_coe_sort`, `Finset.Iic`,
  `Finset.range`, `ae_all_iff`, and the compiled least-encoded source endpoint.
- Proof route: express inclusive finite-history counts and sums as finite sums;
  identify `Iic n` with `range (n+1)`; rewrite the history mean to trace
  count/sum at `n+1`; at `K*m-1`, use positive exploration and round-robin
  action equality to identify that score with `realEmpMeanAtExploration`;
  combine all finite exploration equalities on one a.e. event and consume the
  prior exact-regret endpoint.
- Regularity contracts: arbitrary measurable probability space, measurable
  action/Real-reward coordinates, Markov Real arm kernel, common centered MGF
  proxy, positive exploration, horizon fit, round-robin exploration laws,
  finite-history least-encoded commit, persistence, and selected initial/full-
  history feedback laws. No standard-Borel sample space, full trajectory law,
  independence, local-score commit premise, preassembled horizon equality, or
  infinite-horizon equality is added.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, `Learning.history`,
  `pullCount'`, `sumRewards'`, `empMean'`, `ETC.arm_mul`, measurableArgmax's
  least-encode `Nat.find`, Mathlib finite-sum APIs, and the prior compiled leaf.
  LML remains source/card evidence, not a dependency.
- Status: `leanCompiled`; focused module and score/exact-regret public canaries
  pass.
- Failure policy: source-shaped history score mapping is closed, and the
  downstream local field-compatibility theorem now compiles. Only a true
  cross-toolchain import of the actual LML symbols remains. Do not claim
  `Bandits.ETC.regret_le` is imported.

## Native Real LML Field Compatibility Exact Regret

- Leaf id: `ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET`.
- Lean statements: `ETC.RealStationaryETCSequence` and
  `ETC.regret_le_of_realStationaryETCSequence`.
- Local APIs/imports: `ETCRealHistoryScore`, Mathlib `Measure`, `Kernel`, and
  `condDistrib`, `History.finitePairHistoryOfTrace`,
  `ETC.realLeastEncodedArgmax`, and
  `RewardKernel.contextIndependentOfActionLaws`.
- Proof route: package exactly the measurable-action, measurable-reward,
  exploration, history-score commit, persistence, and stationary feedback-law
  consequences consumed from the pinned source; project those fields into the
  compiled history-score exact-regret endpoint.
- Regularity contracts: probability measure, Markov Real arm kernel, common
  centered `HasSubgaussianMGF` proxy, positive exploration pulls, and horizon
  fit. The structure records action/reward measurability, the three ETC action
  phases, and initial/full-history feedback laws. No `StandardBorelSpace
  Omega`, full trajectory law, independence, local-score premise, or
  preassembled horizon action equality is added.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, `IsAlgEnvSeq`, `stationaryEnv`,
  `ETC.arm_of_lt`/`arm_mul`/`arm_of_ge`, and `Bandits.ETC.regret_le`. The audit
  records ABRL Lean/mathlib `v4.29.1` versus LML Lean `v4.32.0-rc1` and mathlib
  commit `9ca31d8b72cf8c317e49c301bfdbfbe91fc49136`.
- Status: `leanCompiled`; focused module and external theorem canary pass.
- Failure policy: the exact mathematical theorem now compiles through a
  faithful local field bundle. The upstream LML declaration remains
  `card-only`, not `imported`, because its checkout uses a different
  Lean/mathlib toolchain. Do not upgrade the whole repository in this leaf or
  report symbol identity that has not compiled.
