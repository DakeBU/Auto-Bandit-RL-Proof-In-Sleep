# Bandit And RL Proof Backlog

| Problem id | Area | Target | Current status | Next leaf |
| --- | --- | --- | --- | --- |
| `BRL-OP-UCB-MATHLIB-001` | stochastic bandit | UCB regret bound compatible with LML | active local port | native Real random-width index/history and generic fixed-count peeling plus complete-stream `IdentDistrib` transport compile. Next construct the actual generated-UCB `FixedArmPrefixSource` and canonical stationary/product arm-stream law (or an equivalent conditional-MGF source), then one-sided tails, expected pull counts, and final regret |
| `BRL-OP-ETC-SUBGAUSS-001` | stochastic bandit | ETC wrong-commit probability and regret route | local faithful theorem compiled | native Real exact concentration/counts/sum, selected feedback-law transport, least-encoded tie/action assembly, source-shaped `empMean'` mapping, and a faithful local `IsAlgEnvSeq`-field bundle theorem now compile. Remaining work is only a true cross-toolchain import over the actual LML symbols; the upstream declaration is not imported |
| `BRL-OP-TS-BAYES-001` | Bayesian bandit | Thompson sampling Bayesian regret | theorem-card | posterior action-law construction/import after the compiled ledger and countable best-action measurability wrapper |
| `BRL-OP-CONTEXTUAL-001` | contextual bandit | finite contextual bandit regret interface | planned | define context/action/reward model |
| `BRL-OP-RL-BELLMAN-001` | finite-horizon RL | Bellman/value/regret interface | typed contract | define finite MDP surface |
| `BRL-OP-CONCENTRATION-001` | concentration | reusable Hoeffding/sub-Gaussian/variance cards | partial compiled wrappers | `TAIL-HOEFFDING-BOUNDED`, `TAIL-SUBGAUSS-SUM`, `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, `TAIL-COND-SUBGAUSS`, and `TAIL-VARIANCE-ROBUST` compiled; next work is theorem-specific martingale/heavy-tailed estimator specialization, not another generic import wrapper |
| `BRL-OP-TSALLIS-FTRL-001` | best-of-both-worlds bandit | Tsallis-INF/FTRL formalization route | planned | simplex and Tsallis regularizer API |

## Current Notes

- `BRL-ETC-PORT-001`: the fixed-product Bochner route now has the canonical
  round-robin endpoint
  `ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET`.  Its public source
  contracts are indexed by `ETC.exploreArm`, not an arbitrary base commit arm;
  the compiled theorem is
  `ETC.integral_real_pseudoRegret_explorationArgmaxAction_le_explorationMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_exploreMean`.
  It remains fixed-product/fixed-exploration.  The next main-route blocker is
  an action-dependent adaptive environment law plus the conditional
  reward-law/predictability transport needed for an LML-compatible ETC theorem.
  The compiled support leaf `ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` now
  establishes that every fixed-commit exploration empirical mean is determined
  by the reward coordinates below `spec.explorationPulls * K`. It is the
  finite-history reconstruction prerequisite, not the generated-policy or
  adaptive-law transport itself.
  `ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now makes that prerequisite
  consumable at the shifted generated-action state: when the state history
  through `t` contains the exploration horizon (`m * K <= t + 1`), its
  default-completed trace has exactly the ambient exploration scores. The
  remaining next leaf is policy/action-trace alignment, not another score law.
  `ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now discharges that action
  leaf: the finite-history measurable policy generates exactly
  `ETC.explorationArgmaxAction` under positive exploration pulls. The precise
  remaining route is an action-dependent adaptive reward law for this generated
  trace and transport into the existing conditional reward-law consumers.
  `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now supplies that
  law for the canonical Markov-kernel trajectory: it packages full generated
  finite-pair `partialTraj` under `RewardKernel.historyStepKernelFamily`.
  Remaining work is the nontrivial identification/transport from this canonical
  kernel law to the fixed product-coordinate source or a genuine adaptive
  finite-bandit environment.
  `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now turns a
  centered kernel law with `mean (_, arm) = model.mean arm` plus a selected
  history variance ceiling into the conditional sub-Gaussian MGF required by
  the concentration layer. It does not construct those model/kernel contracts
  or transport them to the fixed product-coordinate source.
  `ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now constructs the raw
  context-independent Markov kernel from per-arm probability laws and proves
  selected-measure equality.
  `ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now closes the common
  bounded model bridge: a.s. arm bounds plus exact `model.mean` integrals build
  the centered kernel law and directly produce the canonical successor
  conditional MGF.
  `ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` now aligns the time-zero arm
  law and proves the full selected centered-reward sum tail under canonical
  `trajMeasure`.
  `ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now closes the next
  concentration stage: exploration-prefix action equality and finite-pair
  filtration equality transport the selected-reward conditional MGF into the
  existing centered pairwise witness and finite wrong-commit union.
  `ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now converts that finite
  ENNReal tail to Real, proves the empirical-mean argmax commit and wrong event
  measurable, derives finite-valued pseudo-regret integrability, and yields a
  Real expected-regret theorem for `explorationArgmaxGeneratedAction` under the
  canonical bounded-arm `trajMeasure`. The new external-prefix theorem factors
  the regret integrand through the `m*K` exploration rewards and transports the
  same bound under any external law with an equal prefix pushforward. The new
  generic finite-prefix induction derives that equality from the zeroth
  marginal and successor `condDistrib` laws, and the ETC specialization pulls
  the bound back to an arbitrary external sample space. The next law
  scheduled exploration-arm adapter now rewrites those laws directly as
  `armLaw (exploreArm spec (i+1))`, without exposing local step kernels. The
  remaining obligation is a concrete source or LML `IsAlgEnvSeq` bridge. The
  new full action/reward-history consumer closes the local coarsening from the
  LML feedback conditioning variable to reward-only prefixes. The residual
  seed adapter's action-dependent-to-constant kernel reduction using
  exploration action a.e. equality is now compiled. The
  exact upstream LML theorem also remains open for the independent Real,
  common-sub-Gaussian, tie-breaking, and per-arm RHS mismatches.

- `BRL-OP-ETC-SUBGAUSS-001`: the reward-only canonical law leaf
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP`
  is now compiled.  It registers the existing
  `RewardKernel.historyStepKernelFamily` Markov proof as an instance and uses
  Mathlib `Kernel.condDistrib_trajMeasure` plus the local countable-target
  bridge to prove the selected-reward `condExpKernel.map` law at the finite
  reward prefix.  This is a real canonical trajectory-law proof, not a source
  contract.  The generated finite-pair-prefix versus reward-prefix conditioning
  alignment is now compiled as
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-FINITEPAIR-CONDITIONING`,
  including the `historyFiltrationSucc` rewrite and the canonical law on the
  generated finite-pair surface.  The trim strengthening and selected-source
  construction are now compiled as
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-TRIM-SELECTED-SOURCE`: measurable
  singleton event probabilities justify `ae_eq_trim_of_measurable`, the
  canonical law is transported to the generated finite-pair trim, and
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource` is constructed
  without a selected-reward source assumption.  The downstream endpoint
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-PARTIALTRAJ-LAW` now
  converts this into `GeneratedActionPartialTrajectoryPairLawSource` and proves
  the full successor finite-pair `condExpKernel.map` equality on the canonical
  reward-only process, again without an ambient law source.  The canonical
  centered successor reward now also has ordinary conditional mean zero through
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-MEAN-ZERO`, under
  `CenteredRewardKernelLaw` and the exact ambient integrability premise.  This
  route deliberately avoids pointwise bounds on every `Nat -> Rat` trace.
  The integrated transfer
  `COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER` now combines
  target-wise exponential integrability and a common MGF bound through
  `Measure.integrable_comp_iff`, so conditional-MGF consumers no longer require
  an ambient `h_integrable_exp` premise.  The canonical concentration witness
  is compiled as
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-COND-MGF`: measurable mean,
  a finite-history variance ceiling, and the selected kernel MGF laws produce
  `HasCondSubgaussianMGF` through the canonical full pair law with no ambient
  law-source or exponential-integrability hypothesis.  The downstream leaf
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-SUM-TAIL` now defines a
  zero-initialized successor centered-reward process, proves it strongly
  adapted to generated history, and applies the Mathlib conditional-MGF sum
  wrapper to obtain an ENNReal Azuma-Hoeffding bound for rewards `1..n-1`.
  `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-AVERAGE-TAIL` then
  rewrites that canonical sum tail to an aggregate average tail for `m > 0`,
  using `Finset.range (m + 1)` and the threshold `m * eps`.  This is not yet an
  arm-wise empirical-mean or confidence-radius event.  The retrieval index
  currently names `COND-EXPECT-REWARD` conversion-window and proof-obligation
  files which are absent from the worktree; restore or regenerate them before
  using their route metadata.  Arm-wise confidence-event specialization,
  arbitrary ambient transport, independent pair-valued process construction,
  and the generic pair-law theorem card remain open.

- `BRL-OP-ETC-SUBGAUSS-001`: the source-level generated `partialTraj`
  mean-zero consumer is now compiled as
  `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO`.
  The canonical Mathlib `trajMeasure` full-prefix law is also available in the
  project `History.finitePairHistoryOfTrace` notation as
  `COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP`.
  The generated history sigma-algebra has now been aligned with that finite
  pair-prefix notation by
  `HISTORY-FILTRATION-FINITEPAIR-COMAP`: finite pair histories are measurable
  at later generated-history filtration levels and
  `History.historyFiltration ... (n + 1)` is exactly the comap of
  `History.finitePairHistoryOfTrace ... n`.  Use this bridge before trying to
  transport canonical `trajMeasure` or selected-reward laws into ambient
  generated-history `condExpKernel` statements.
  The source-layer adapter
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW`
  is now compiled as well: a selected-reward `condExpKernel.map` law stated
  directly at the finite-pair comap conditioning sigma-algebra constructs the
  generated selected-reward finite-pair-history source, the full generated
  finite-pair `partialTraj` source, and the theorem-card-shaped full finite-pair
  `partialTraj`/`condExpKernel` law.  The source now accepts both the existing
  generated-history trim filter and the Mathlib-facing comap-trim filter at
  the selected-source, partialTraj-source, and theorem-wrapper layers.
  The same comap selected-reward law now also constructs the practical
  raw-range/measurable-mean-range bounded source directly after supplying the
  measurable mean, centered kernel law, and raw/mean range contracts.
  The selected-reward canonical law now has the same finite-pair-history
  notation wrapper as
  `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP`.
  Its reward-history projection is compiled as
  `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP`,
  and the generated ambient selected-reward law is now isolated as the source
  contract
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT`.
  The same source now projects directly to the full generated finite-pair
  `partialTraj` law surface as
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW`.
  Definitional actual-action reward-map sources now convert into that
  finite-pair-history source through
  `COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`.
  The practical definitional raw-range/measurable-mean-range generated
  random next-pair package, including its uniform-variance and
  selected-history-variance wrappers, now projects into the same
  finite-pair-history source through
  `COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`,
  so selected-source mean-zero and conditional-MGF consumers can start from
  the practical package surface.  This still consumes the packaged random
  next-pair law.
  The composed selected-source theorem surface now compiles as
  `COND-EXPECT-REWARD-PRACTICAL-SOURCE-VIA-SELECTED-FINITEPAIRHISTORY-COND-MGF`:
  the practical base package yields conditional mean-zero and the
  uniform/history variance packages yield conditional MGF witnesses by first
  constructing the selected finite-pair-history source.  This still consumes
  the packaged random next-pair law and the variance/proxy contracts.
  A packaged full finite-pair `GeneratedActionPartialTrajectoryPairLawSource`
  now projects directly to the same selected-reward finite-pair-history source
  via
  `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION`,
  in addition to its theorem-card-shaped full `partialTraj` law and actual
  reward-map source projections.
  That source now has a direct raw/mean range conditional mean-zero consumer as
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO`,
  and the finite-pair comap selected-reward law can now enter that same
  mean-zero surface directly through the local comap-to-source adapter, using
  either the generated-history trim filter or the direct comap-trim filter.
  The same selected-reward finite-pair-history source now has direct
  conditional MGF consumers as
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-COND-MGF`,
  covering global variance ceilings, coarser global proxies, selected-history
  variance ceilings, and coarser selected-history proxies.
  The same comap selected-reward law now also feeds the uniform-variance
  conditional MGF consumer with either the generated-history trim filter or the
  direct comap-trim filter, provided raw/mean range regularity and a global
  variance ceiling are supplied; this is still a consumer route, not a proof of
  the selected-reward law itself.
  The coarser-proxy uniform-variance MGF route now accepts the same direct
  comap-trim filter when the deterministic domination proof
  `varianceCeiling <= c` is supplied.
  It also now constructs the packaged uniform-variance practical source
  directly, so downstream source consumers no longer need to re-thread the
  full finite-pair source after assuming the same comap selected-reward law;
  either the generated-history trim filter or direct comap-trim filter can be
  used as the law surface.
  The uniform route also has a coarser-proxy comap consumer when a deterministic
  domination proof `varianceCeiling <= c` is supplied.
  It now also feeds the selected-history-variance conditional MGF consumer with
  either the generated-history trim filter or the direct comap-trim filter when
  the time-indexed selected-history variance ceiling contract is supplied.
  It also constructs the packaged selected-history-variance practical source
  directly under that same time-indexed ceiling contract, with either the
  generated-history trim filter or direct comap-trim filter accepted as the law
  surface.
  The selected-history route also has a coarser-proxy comap consumer with
  either the generated-history trim filter or the direct comap-trim filter when
  `varianceCeiling i <= c` is supplied.
  The conditional reward-law transfer, ambient trajectory-to-`condExpKernel`
  identification, and final adaptive ETC theorem assembly remain open.

## ETC Direct Common-Sub-Gaussian Route

`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT` is now
`leanCompiled`. Its endpoint
`ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws` consumes
per-arm `Rat` probability laws, exact model means, and direct centered
`HasSubgaussianMGF` witnesses at one common `sigma2`. It reuses the canonical
kernel trajectory, maps the initial law to coordinate zero, transports
successor MGFs to the fixed exploration filtration, and produces the masked
one-sided pairwise empirical-mean contract without bounded support or an arm
union.

The concrete non-best commit-fiber bounds, finite Real tails, and canonical
gap-weighted per-arm Bochner theorem now compile as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET`.
Its exploration-prefix equality transport, generic initial/successor
conditional-law consumer, and `Context := Unit` scheduled exploration-arm
consumer now compile as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
Its LML-shaped full action/reward-history constant-law consumer now compiles as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
Its action-dependent selected-kernel consumer now compiles as
`ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET`.
Dependency-light direct-MGF `Rat` law transport is closed. Downstream native
Real product, exact count/regret, finite-prefix, and scheduled conditional-law
transport and the upstream-shaped selected feedback-law adapter now also
compile. The unfinished route is action-only: horizon equality from the
upstream exploration/commit/persistence lemmas plus fold/`measurableArgmax`
tie equivalence. Failure policy: the external theorem is not yet
`Bandits.ETC.regret_le`.

## Rule

Backlog entries are not proof claims.  Promote one entry into `tasks/` when a
run is ready to work on it.

## Real Mean-Regret Pull-Count Leaf

`REAL-MEAN-REGRET-PULLCOUNT` is no longer open. The compiled declarations
`realMeanRegret_eq_sum_gap_mul_pullCount` and
`integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount` use Real arm means
and the exact supremum-minus-mean gap, with only per-arm pull-count
integrability at the expectation layer. Evidence is the exact LML seed scalar
definitions, local Mathlib-backed pull-count/Finset wrappers, and Bochner
finite-sum integration; the external canary passes.

The stationary Real reward-kernel identity-integral specialization is compiled
as `REAL-KERNEL-REGRET-PULLCOUNT`, and the count/integration half of the next
step is compiled as `REAL-ETC-EXPECTED-PULLCOUNT`. The new endpoint derives the
exact per-arm expected pull-count bound from an abstract Real
`P(commit=a) <= p` premise. The exact common-proxy canonical producer is now
compiled as `ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT`: it proves
the LML exponential constant and feeds the fiber probability bound into that
consumer for existing Rat arm laws with Real centered MGFs. The follow-on
`ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` leaf now pushes those laws to a
Markov Real kernel, proves exact kernel-gap equality, and compiles the complete
finite-arm LML-shaped sum. The subsequent
`ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` leaf now closes direct Real
exploration means, deterministic finite argmax measurability, and exact
expected-count consumption. The follow-on
`ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET` leaf now compiles the native Real
canonical independent-coordinate commit tail, expected count, exact kernel
gap, and complete finite-arm LML-shaped regret sum for a Markov kernel with a
common centered MGF proxy. Finite exploration-prefix law transport is now
compiled as
`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET`: finite-prefix law equality
transports the complete regret integral, and scheduled-arm zeroth/successor
conditional laws derive the prefix equality through generic Ionescu-Tulcea
uniqueness. The follow-on
`ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` leaf now maps the exact
upstream-shaped action-selected initial and full pair-history successor
feedback laws to the scheduled reward-prefix surface. The subsequent
`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` leaf identifies the local
fold with the least-encode Nat.find selector, assembles upstream-shaped
exploration/commit/persistence behavior, and removes the explicit horizon
action-equality premise from the strongest exact-regret consumer. The follow-on
`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` leaf now identifies
source-shaped inclusive history counts/sums/means with the local exploration
score and accepts the history-shaped commit law directly. The next open leaf
is actual LML `measurableArgmax`/`IsAlgEnvSeq` symbol-and-field compatibility.
Do not weaken the target, add
`StandardBorelSpace Omega`, demand full trajectory-law equality, or relabel an
external adapter as the upstream theorem.
