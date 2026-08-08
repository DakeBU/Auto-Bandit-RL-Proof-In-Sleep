# Bandit And RL Proof Backlog

| Problem id | Area | Target | Current status | Next leaf |
| --- | --- | --- | --- | --- |
| `BRL-OP-UCB-MATHLIB-001` | stochastic bandit | UCB regret bound compatible with LML | local faithful theorem compiled | native Real index/history, recursive canonical process, tails/counts/exact regret, observable trajectory uniqueness, split action/feedback law composition, and the faithful `RealStationaryUCBSequence` field-bundle theorem all compile. Remaining work is an actual imported-LML or separately defined concrete external producer for the bundle; no mathematical law assembly, concentration, trajectory uniqueness, or unused-arm reconstruction remains |
| `BRL-OP-ETC-SUBGAUSS-001` | stochastic bandit | ETC wrong-commit probability and regret route | local faithful theorem compiled | native Real exact concentration/counts/sum, selected feedback-law transport, least-encoded tie/action assembly, source-shaped `empMean'` mapping, and a faithful local `IsAlgEnvSeq`-field bundle theorem now compile. Remaining work is only a true cross-toolchain import over the actual LML symbols; the upstream declaration is not imported |
| `BRL-OP-TS-BAYES-001` | Bayesian bandit | Thompson sampling Bayesian regret | local stationary theorem compiled | canonical/reference samplers, recursive density, global prior-mixture probability matching, clipped-UCB decomposition, both concentration expectations, and the stationary final bound `(2*K+1)*(u-l)+8*sqrt(sigma2*K*n*log n)` compile. Remaining work is literal LML symbol import or an explicitly stated nonstationary/contextual adapter |
| `BRL-OP-EXP3-ADVERSARIAL-001` | adversarial bandit | EXP3 expected regret | the generated predictable-trajectory route compiles through adaptive moments, integrability, the unoptimized bound, deterministic tuning, realized selected-loss transport, and the all-horizon clipped-rate `min(T,4*sqrt(|A|*T*log|A|))` theorem | next choose one narrow extension such as high-probability regret, stochastic rewards, or a broader adversary contract without reopening the compiled expectation-law route |
| `BRL-OP-CONTEXTUAL-001` | contextual bandit | finite contextual bandit regret interface | planned | define context/action/reward model |
| `BRL-OP-RL-BELLMAN-001` | finite-horizon RL | Bellman/value/regret interface | typed contract | define finite MDP surface |
| `BRL-OP-CONCENTRATION-001` | concentration | reusable Hoeffding/sub-Gaussian/variance cards | partial compiled routes | `TAIL-HOEFFDING-BOUNDED`, `TAIL-SUBGAUSS-SUM`, `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, `TAIL-COND-SUBGAUSS`, `TAIL-VARIANCE-ROBUST`, fixed-tilt predictable compensation, quadratic delta optimization, and a consumed finite-prefix maximal union route compile; next work is a new model's one-step MGF producer or a sharper Ville/mixture anytime theorem, not another import-only wrapper |
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
  law now also transports to an arbitrary standard-Borel ambient sample space
  under a complete reward-trace `IdentDistrib` contract through
  `COND-EXPECT-REWARD-AMBIENT-IDENTDISTRIB-TRAJMEASURE-SELECTED-SOURCE`.
  The proof composes `IdentDistrib` with finite-prefix/next-reward maps,
  transports the canonical joint `compProd` factorization, recovers ambient
  `condDistrib` by uniqueness, and constructs the generated selected source;
  the existing adapter then reaches the full ambient generated `partialTraj`
  source.  The weaker recursive route is now compiled as
  `COND-EXPECT-REWARD-AMBIENT-RECURSIVE-CONDDISTRIB-PARTIALTRAJ-SOURCE`:
  the initial reward law and every successor `condDistrib` law imply the full
  canonical trajectory `IdentDistrib`, selected source, and generated
  `partialTraj` source.  The route now continues through
  `COND-EXPECT-REWARD-AMBIENT-RECURSIVE-CONDDISTRIB-CENTERED-SUM-TAIL`:
  the full source yields successor conditional MGF witnesses without raw/mean
  range bounds, the initial marginal yields ambient probability, generated
  history supplies strong adaptedness, and the Mathlib-backed wrapper proves an
  ENNReal Azuma-Hoeffding finite-sum tail.  What remains upstream is to prove
  the recursive laws from a concrete algorithm/environment, or to prove the
  finite prefix/next joint factorization directly.  The canonical
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
  using their route metadata.  Arm-wise confidence-event specialization of the
  new ambient tail,
  concrete production of recursive conditional laws, independent pair-valued process construction,
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
## UCB Split-Law Compatibility Update

Closed locally: composing `IsAlgEnvSeq`-shaped initial/successor action and
feedback laws into joint observable pair laws, complete trajectory
`IdentDistrib`, and exact canonical UCB regret. Open next leaf: prove those four
split laws for one concrete external sequence, or resolve the pinned LML/current
ABRL toolchain boundary. Failure policy: no unused-arm reconstruction, no
marginal-only substitute, and no claim that theorem-card LML symbols are local.

Follow-on closed locally: `RealStationaryUCBSequence` packages those split
fields and `regret_le_of_realStationaryUCBSequence` proves the exact theorem.
The next open item is strictly a concrete upstream producer/toolchain import.

## Thompson Algorithm-Density Process Update

Closed locally: recursive finite pair-history density transport from
LML-shaped split process laws and pointwise initial/policy absolute
continuity. The compiled theorem is
`Thompson.finitePairHistory_map_eq_withDensity`; it uses a shared feedback
environment and requires no pointwise RN-density finiteness.

Follow-on closed locally: the environment-indexed source over
`condDistrib id` sample measures now yields the a.e. conditional-history
density law and finite-prefix Thompson probability matching. The split-source
layer records the four `IsAlgEnvSeq`-shaped conditional law families and
assembles both process contracts with `ae_all_iff`. The canonical trajectory
leaf now constructs each fixed-environment pair `trajMeasure`, proves its
combined process law, recovers all four split laws, proves the full-sample
  disintegration of `prior compProd trajectoryKernel`, and closes finite-prefix
  probability matching for supplied Markov trajectory-kernel families with those
  canonical pointwise values. The measurable trajectory leaf now constructs the
  actual/reference `Env -> PairTrace` Markov kernels from jointly measurable
  feedback data with Mathlib `Kernel.traj`, proves the initial and shifted
  successor pair laws, derives pointwise canonical equality, and closes
  finite-prefix probability matching without supplied process-law premises.
  Open next leaf: couple the finite-pair per-time policy samplers into one
  recursive TS trace. Failure policy: do not re-assume supplied trajectory
  kernels, full canonical equality, combined/split process laws, density, or
  probability matching, and do not claim Bayesian regret is closed.

## Thompson Clipped-UCB Concentration Expectations

Closed locally: `TS-STATIONARY-EMPIRICAL-MEAN-TAIL-TRANSPORT`. The compiled
endpoints on `stationaryLatentArmStreamCanonicalTrajectoryMeasure` bound each
fixed-arm lower- and upper-confidence failure by
`(n : ENNReal) * ENNReal.ofReal delta`. Evidence includes Mathlib
`Measure.compProd_apply`, `Measure.compProd_assoc`, `Measure.map_apply`, local
adaptive-count `IdentDistrib` tails, clipped threshold algebra, and external
declaration canaries.

Open next leaf: derive the selected-action and best-action clipped-score
expectation bounds using finite arm/time unions and event-to-integral
conversion. Failure policy: do not weaken the score, replace fixed-arm tails
with selected-reward conditional MGF, or re-assume stream support, positive
count peeling, prior mixing, or product-associativity transport.

Closed locally: `TS-STATIONARY-SELECTED-ARM-HORIZON-LOWER-TAIL`. The compiled
canonical endpoint takes any measurable environment-dependent arm selector and
bounds its finite-horizon lower-confidence failure event by
`((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta`. Evidence includes selected
arm measurability, latent-stream reward support, the pull-count-to-prefix
identity, finite union over `Finset.Icc 1 (n - 1)`, prior mixing, and canonical
product transport.

This horizon event's best-action-minus-clipped-UCB expectation consumer is now
compiled. Its downstream selected-action expectation and stationary final
theorem are also compiled; preserve the completed `(n - 1) * delta`
lower-event cost if this route is generalized.

Closed locally: `TS-CLIPPED-UCB-BEST-ACTION-EXPECTATION`. The exact
decomposition-facing theorem bounds the best-action mean minus clipped-UCB
finite-sum integral by `(u-l) * (n-1) * n * delta`. Evidence is the compiled
selected-arm horizon lower tail, clipped score/mean `[l,u]` bounds, finite-sum
integrability, measurable bad-event splitting, and ENNReal-to-Real probability
conversion.

The selected-action clipped-UCB-minus-mean expectation is now closed using the
deterministic clipped-UCB sum bound and the finite-arm horizon upper-confidence
event bounded by `K * (n-1) * delta`. Preserve the pinned square-root and event
constants; do not replace the count-collapsed horizon event with a sum of
fixed-time `t * delta` bounds.

Closed locally: the deterministic clipped-UCB sum, exact all-arm horizon upper
event, selected-action expectation, general-`delta` decomposition join, and
stationary `TS-FINAL`. The final endpoint has the pinned RHS
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)` and is compiled under the local
stationary Markov reward-kernel contracts.

The Thompson backlog now moves outside this stationary theorem: literal LML
symbol import across the toolchain boundary, or a separately stated
nonstationary/contextual model adapter. Failure policy: do not add another
stationary wrapper, weaken the existing theorem, or present it as a general RL
result.

## EXP3 Deterministic Hedge Regret Update

Closed locally: `EXP3-HEDGE-DETERMINISTIC-REGRET`. The module
`BanditRLProof.Exp3HedgeRegret` defines cumulative-loss exponential weights and
their finite normalization, proves the quadratic exponential and one-step
log-potential inequalities, and telescopes them into the second-order pathwise
comparator bound
`log |A| / eta + eta * sum_t <p_t, loss_t^2>`. For losses in `[0,1]`, the
compiled endpoint is `log |A| / eta + eta*T`.

The deterministic theorem now also has a generalized endpoint for arbitrary
nonnegative losses under `eta > 0`, using the global bound
`exp(-x) <= 1-x+x^2` for `x >= 0`. This is the endpoint needed by unbounded
importance-weighted estimates.

## EXP3 Importance-Weighted Moments Update

Closed locally: `EXP3-IMPORTANCE-WEIGHTED-MOMENTS`. The module
`BanditRLProof.Exp3ImportanceWeighted` defines the sampled-coordinate loss
estimate and proves its armwise finite-sum cancellation, the pathwise identity
between the mixed estimate and selected loss, the probability-weighted
mixed-loss identity, and the exact weighted mixed-square identity
`sum_a loss(a)^2`. Under losses in
`[0,1]`, the latter is at most the number of arms.

Regularity is explicit finite support, decidable equality at theorem call sites,
and nonzero sampling mass for every supported arm. Normalization and
nonnegativity are not needed for the algebraic cancellation itself, but are
  required before the weights represent an action law. No measure, filtration,
  or conditional distribution is used in this algebraic leaf.

## EXP3 Conditional Moment Transport Update

Closed locally: `EXP3-CONDITIONAL-MOMENT-TRANSPORT`. The module
`BanditRLProof.Exp3ConditionalMoments` realizes a normalized finite action
distribution as a sum of scaled Dirac measures and transports one-round
importance-weighted first/second moments through an actual history-conditional
`condDistrib` law. The generic theorem reduces a measurable integrable
history/action score to its finite conditional weighted sum; the specialized
theorems prove armwise unbiasedness and exact mixed-loss/mixed-square
Bochner-integral identities. Since the ambient measure is only finite, these
are unnormalized integrals unless a probability-measure instance is supplied.

The downstream generated-process leaf now proves the kernel and `condDistrib`
equalities. Score measurability/integrability and recursive finite-horizon
generation remain separate. Failure policy: do not replace the adaptive policy
with a fixed independent distribution, and do not report finite-horizon EXP3
regret before expectation assembly and `eta` optimization compile.

## EXP3 Generated Action Process Update

Closed locally: `EXP3-GENERATED-ACTION-PROCESS`. The module
`BanditRLProof.Exp3ActionProcess` turns measurable history-indexed finite
probability vectors into a Markov kernel, composes an arbitrary finite history
law with that policy, proves the history marginal is preserved, and identifies
the sampled action's `condDistrib` a.e. with the generated policy. Its canonical
armwise and mixed first/second moment wrappers discharge the external policy,
finite-law, and conditional-law premises of the previous transport.

The downstream score-regularity leaf now derives score measurability,
reciprocal-floor bounds, and integrability from measurable bounded losses and a
uniform positive probability floor, and the downstream recursive-trajectory
leaf constructs the multi-round adaptive process from a measurable history
score. Failure policy: this one-round `compProd` law alone is not the recursive
algorithm and does not justify expected regret or parameter optimization.

## EXP3 Score Regularity Update

Closed locally: `EXP3-SCORE-REGULARITY`. The module
`BanditRLProof.Exp3ScoreRegularity` packages measurable supported `[0,1]`
losses and a uniform positive probability floor. It proves all three
importance-weighted score surfaces measurable, bounds their norms by
`1/epsilon`, `1/epsilon`, and `(1/epsilon)^2`, derives generated-law
integrability, and exposes canonical one-round moment identities without
manual positivity, measurability, or integrability premises.

The score-driven recursive action/loss trajectory now compiles downstream.
Failure policy: the uniform floor is a real regularity contract, and this leaf
does not define the sampled importance-weighted history score, assemble
expected regret, or optimize `eta`/`gamma`.

## EXP3 Exploration-Mixed Recursive Trajectory Update

Closed locally: `EXP3-EXPLORATION-MIXED-RECURSIVE-TRAJECTORY`. The module
`BanditRLProof.Exp3RecursiveTrajectory` turns any measurable cumulative score
on inclusive finite action/loss histories into positive exponential weights,
normalized exploration-mixed probabilities, and the uniform lower bound
`gamma / arms.card`. It packages the policy as a stochastic history algorithm,
constructs the complete Mathlib-backed recursive action/loss trajectory, and
identifies every successor action conditional law with the explicit finite
action kernel.

Regularity contracts are a nonempty finite arm support, measurable score
coordinates, `0 <= gamma <= 1`, the measurable/Standard-Borel hypotheses used
by the trajectory and `condDistrib` APIs, and a finite prior for the mixed law.
Retrieval evidence is `LOCAL-LEAF-EXP3-SCORE-REGULARITY`,
`LOCAL-LEAF-EXP3-GENERATED-ACTION-PROCESS`, Mathlib finite sums, exponential
measurability, Ionescu-Tulcea trajectories and conditional distributions,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`;
`WEAPON-EXP3-POTENTIAL` is inspiration only. The downstream concrete sampled
history-score producer now compiles. Failure policy: retain this generic route
for other measurable scores, but use the concrete theorem for EXP3 and do not
claim expected regret before the feedback-law and expectation layers compile.

## EXP3 Sampled History Score Recursive Trajectory Update

Closed locally: `EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`. The module
`BanditRLProof.Exp3SampledHistoryScore` recursively defines the cumulative
importance-weighted score from the actual Real action/loss pairs. Time zero
uses the initial distribution; each successor restricts to the previous
prefix, computes the exact exploration-mixed probability from the previous
score, and adds the selected loss divided by that probability. The recursion
equations, score measurability, probability floor, stochastic algorithm,
complete trajectory kernel, and exact successor action `condDistrib` compile.

Local APIs/imports are `Exp3RecursiveTrajectory`, finite pair histories,
`measurable_pi_lambda`, `measurable_pi_apply`, measurable `ite/div/add/comp`,
`importanceWeightedLoss`, the generic history-distribution source, and the
generic trajectory conditional-law theorem. Regularity is Real feedback,
measurable action singletons, decidable equality, nonempty finite arms,
`0 <= gamma <= 1`, a measurable history environment, Standard Borel
environment/action, and a finite prior. Retrieval evidence is the compiled
generic EXP3 trajectory/moment leaves, Mathlib finite-sum/measure/kernel cards,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`; the weapon card is
inspiration only. Failure policy: the next missing law is not score recursion.
It requires an initial `Env -> Action -> Real` loss vector and successor
`Env -> FinitePairHistory ... n -> Action -> Real` vectors measurable before
the current action, bounded in `[0,1]`, with Dirac chosen-coordinate feedback.
The downstream `EXP3-PREDICTABLE-ADVERSARY` leaf now supplies these contracts.

## EXP3 Predictable Adversary Update

Closed locally: `EXP3-PREDICTABLE-ADVERSARY`. The module
`BanditRLProof.Exp3PredictableAdversary` defines jointly measurable initial
`Env -> Action -> Real` and successor
`Env -> FinitePairHistory Action Real n -> Action -> Real` loss vectors with
pointwise `[0,1]` bounds. `PredictableLossVector.environment` realizes their
selected coordinates as deterministic Markov feedback kernels, and the
initial/successor apply theorems identify those kernels exactly as Dirac laws.

The same module proves a prior-mixture conditional-law transport that retains
the environment coordinate. Its concrete specialization,
`sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment`,
identifies the sampled EXP3 next-action law given `(Env,prefix)` with the
exploration-mixed finite action kernel. The proof uses measurable sections,
`Measure.ext_prod`, `Measure.lintegral_compProd`, and the fixed-environment
canonical trajectory law. Regularity is joint pre-action measurability,
pointwise `[0,1]`, measurable action singletons and decidable equality,
nonempty finite arms, `0 <= gamma <= 1`, Standard Borel environment/action,
and a finite prior. Retrieval evidence is the compiled sampled-score and
conditional-moment leaves, `MLIB-PROBABILITY-KERNEL`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`; the weapon card is
inspiration only. Failure policy: this closes the action-reactive-adversary
gap, but it does not yet assemble the Dirac feedback and action law into
roundwise conditional moment identities or prove finite-horizon regret.

### Closed leaf: EXP3-PREDICTABLE-OBSERVED-MOMENTS

Closed locally in `BanditRLProof.Exp3PredictableMoments`. Lean-facing output
now includes the prior-mixed environment/prefix/next-pair joint law and
`condDistrib`, time-zero and successor selected-feedback a.e. laws, a measurable
sampled distribution source on `(Env,prefix)`, the positive exploration-floor
regularity package, and
`sampledPredictableObservedSuccessor_first_second_moment`. The latter proves
the observed-scalar armwise unbiased first moment and exact probability-mixed
estimator-square moment against the predictable loss vector. Retrieval:
`LOCAL-LEAF-EXP3-PREDICTABLE-ADVERSARY`,
`LOCAL-LEAF-EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`,
`LOCAL-LEAF-EXP3-CONDITIONAL-MOMENT-TRANSPORT`,
`MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`; the weapon card is
inspiration only. Failure policy: do not reinterpret these integral identities
as conditional expectations or regret. Their finite-horizon consumer now
compiles; the next missing proof is the sampled-score/Hedge-potential join.

### Closed leaf: EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS

Closed locally in `BanditRLProof.Exp3PredictableMoments`. The theorem
`sampledPredictableObserved_finiteHorizon_first_second_moment` sums the observed
armwise first-moment and probability-mixed estimator-square identities over
`Finset.range horizon`, i.e. over `t < horizon` and including time zero when the
horizon is positive, on the common prior-mixed full trajectory law. Supporting APIs provide uniform actual-time probabilities and
predictable losses, measurable distribution/floor regularity, finite-measure
integrability, a.e. observed-to-predictable score transport, and the every-time
moment theorem. Retrieval: `LOCAL-LEAF-EXP3-PREDICTABLE-OBSERVED-MOMENTS`,
`LOCAL-LEAF-EXP3-CONDITIONAL-MOMENT-TRANSPORT`,
`LOCAL-LEAF-EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-KERNEL`,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`; the weapon card is
inspiration only. Failure policy: no sampled-score/Hedge pathwise inequality,
exploration-bias bound, eta/gamma optimization, or final regret is claimed.

### Closed leaf: EXP3-SAMPLED-HEDGE

Closed locally in `BanditRLProof.Exp3SampledHedge`. The module proves the exact
index bridge
`sampledHistoryScore n (frestrictLe n trajectory) = cumulativeLoss observed (n+1)`,
transports it through the finite exponential-weight denominator, and rewrites
the actual sampled probability as the exploration mixture of the resulting
pure Hedge distribution. Nonnegative sampled probabilities turn nonnegative
scalar observations into nonnegative importance-weighted loss vectors, so the
compiled deterministic second-order Hedge theorem yields
`sampledHistoryScore_hedge_regret_le` on every qualifying finite trajectory
prefix. Contracts are finite nonempty arms, decidable equality, positive eta,
`0 <= gamma <= 1`, supported comparator, and pathwise nonnegative observations.
Retrieval: `LOCAL-LEAF-EXP3-HEDGE-DETERMINISTIC-REGRET`,
`LOCAL-LEAF-EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`,
`LOCAL-LEAF-EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS`,
`MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-ORDER-ALGEBRA`,
`PPR-AUER-CFS-2002-EXP3`, and `TXT-BUBECK-CESABIANCHI-2012`; the weapon card is
inspiration only. Failure policy: the next leaf must build the finite-horizon
a.e. reward-support and exploration-bias/integration bridge, not jump directly
to an optimized final regret theorem.

### Closed leaf: EXP3-PREDICTABLE-HEDGE-AE

Closed locally in `BanditRLProof.Exp3PredictableHedge`. The time-zero reward
law and every successor selected-feedback law are rewritten through the
pointwise `[0,1]` contracts, producing every-time observed reward
nonnegativity almost surely. `ae_all_iff` aggregates these facts before a
finite horizon, after which `sampledTrajectory_hedge_regret_le` and
`sampledHistoryScore_hedge_regret_le` give generated-law a.e. inequalities.
The score-shaped public endpoint is `sampledPredictableScoreHedge_ae`.
Regularity is finite nonempty arms, positive eta, `0 <= gamma <= 1`, supported
comparator, predictable measurable `[0,1]` loss vectors, Standard Borel
environment/action with measurable action singletons and decidable equality,
and a finite prior. Retrieval: `LOCAL-LEAF-EXP3-SAMPLED-HEDGE`,
`LOCAL-LEAF-EXP3-PREDICTABLE-OBSERVED-MOMENTS`,
`LOCAL-LEAF-EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, and
the EXP3 paper/textbook cards; the weapon card is inspiration only. Failure
policy: this a.e. inequality is not expected regret by itself. Its
pure-`q`/explored-`p` comparison, integrability, and integrated expected-regret
consumer now compile downstream.

### Closed leaf: EXP3-EXPLORATION-BIAS

Closed locally in `BanditRLProof.Exp3ExplorationBias`. The concrete mixture
identity gives `q_t(a) <= p_t(a)/(1-gamma)` under `0 <= gamma < 1`; multiplying
by nonnegative estimator squares and summing yields the pure-q/explored-p
second-moment comparison. The predictable `[0,1]` contract separately gives
`p_t dot loss_t <= q_t dot loss_t + gamma`. The public endpoint
`sampledTrajectory_finiteHorizon_explorationBias_secondMoment` sums both over
any finite horizon. Regularity is finite nonempty arms, decidable equality,
measurable spaces carried by the predictable-loss structure, and
`0 <= gamma < 1`; no eta positivity, prior, probability law, integrability,
or comparator is used. Retrieval: predictable-Hedge, sampled-Hedge,
finite-horizon-moment, and importance-weighted local cards; Mathlib finite
sums/order algebra; EXP3 paper/textbook cards; weapon card as inspiration
only. Failure policy: do not call this pathwise leaf expected regret. Its
adaptive pure-q moment, integrability, and integrated expected-regret consumer
now compile downstream, including the tuned square-root theorem.

### Closed theorem route: EXP3-PREDICTABLE-EXPECTED-REGRET

Closed locally in `BanditRLProof.Exp3PredictableIntegration`. The public
theorem `sampledPredictable_expectedRegret_le` proves the generated-trajectory
bound `log|A|/eta + eta|A|T/(1-gamma) + gamma T` against every supported arm.
Supporting Lean declarations provide a cross-weight importance estimator,
the exact `E_p[q dot hat-loss]=q dot loss` finite-sum identity, measurable and
integrable score surfaces, conditional-law transport, measurable pure-Hedge
sources, finite-horizon adaptive first moments, integrated a.e. Hedge control,
integrated exploration bias, and the `|A|T` second-moment bound.

Contracts are a probability prior, Standard Borel Env/Action, measurable
singletons, decidable finite nonempty arms, predictable measurable `[0,1]`
losses, a supported comparator, `eta>0`, and `0<gamma<1`. Independence,
stationarity, an oblivious adversary, concentration, and supplied integrability
are not assumed. Retrieval: the compiled exploration-bias, predictable-Hedge,
finite-horizon-moment, conditional-moment, and score-regularity cards; Mathlib
measure/kernel/finite-sum/order APIs; `PPR-AUER-CFS-2002-EXP3`;
`TXT-BUBECK-CESABIANCHI-2012`; and inspiration-only `WEAPON-EXP3-POTENTIAL`.
Status: `leanCompiled`, root imported, with an external final-theorem canary.
Failure policy: this is expected predictable regret but not the optimized
classical EXP3 statement by itself; its tuned, realized selected-loss, and
uniform-horizon clipped-rate consumers now compile. Preserve this p-mixed
endpoint for broader theorem routes.

### Closed theorem route: EXP3-TUNED-EXPECTED-REGRET

Closed locally in `BanditRLProof.Exp3ExpectedRegret`. The route first proves
the deterministic `4*gamma*T` budget under `eta=gamma/K`, `gamma<=1/2`, and
`K*log K<=gamma^2*T`. It then defines the square-root exploration and learning
rates, proves their positivity/cap/budget identities, and exposes
`sampledPredictable_expectedRegret_le_four_mul_sqrt` with bound
`4*sqrt(K*T*log K)` on the generated predictable trajectory.

Regularity is the compiled predictable EXP3 theorem contract plus `2<=K`,
`0<T`, and `4*K*log K<=T`; no stochastic-law, concentration, stationarity, or
integrability premise is added. Retrieval is the compiled expected-regret
local card, Mathlib Real log/sqrt and order algebra, the EXP3 paper/textbook
cards, and inspiration-only weapon card. Status is `leanCompiled`, root
imported, with a full external theorem canary. Failure policy: this is the
large-horizon expected mixed predictable-loss theorem; its realized and
uniform-horizon clipped-rate consumers now compile downstream.

### Closed theorem route: EXP3-REALIZED-EXPECTED-REGRET

Closed locally in `BanditRLProof.Exp3RealizedRegret`. The generated scalar
reward is almost surely the predictable loss at the sampled action. The
compiled initial/successor sampled-action `condDistrib` laws and generic
finite-action conditional integral theorem then give
`E[realizedLoss_t]=E[p_t dot loss_t]` for every time. Finite-horizon Bochner
summation transports that equality into the existing expected-regret endpoints.

`sampledPredictable_realizedExpectedRegret_le` exposes the unoptimized budget,
and `sampledPredictable_realizedExpectedRegret_le_four_mul_sqrt` exposes
`4*sqrt(K*T*log K)` for actual generated scalar losses under `2<=K`, `0<T`, and
`4*K*log K<=T`. Regularity is unchanged from the compiled predictable route;
there is no independence, stationarity, obliviousness, concentration, or new
integrability premise. Retrieval uses the predictable/tuned expected-regret,
conditional-moment, predictable-adversary, Mathlib measure/kernel/finite-sum,
EXP3 paper/textbook cards, and inspiration-only weapon card. Status is
`leanCompiled`, root imported, with declaration and full external theorem
canaries. Failure policy: the realized transport is reusable for legal rates;
its all-horizon clipped-rate consumer now compiles, while high-probability and
broader-adversary routes remain separate.

### Closed theorem route: EXP3-UNIFORM-HORIZON-REALIZED-REGRET

Closed locally in `BanditRLProof.Exp3UniformRegret`. The support theorem
`sampledPredictable_realizedExpectedRegret_le_horizon` uses `[0,1]` losses and
the compiled realized-to-explored expectation transport to prove the trivial
expected-regret bound `E[R_T] <= T` for arbitrary legal EXP3 rates. The module
then defines `clippedExplorationRate=min(1/2,tunedExplorationRate)`, pairs it
with `clippedLearningRate=gamma/K`, and constructs a generated trajectory kernel
that is valid for every natural horizon, including zero.

The final theorem `sampledPredictable_clippedRealizedExpectedRegret_le_min`
proves `E[R_T] <= min(T,4*sqrt(K*T*log K))`. On
`4*K*log K<=T`, the clipped rate equals the tuned rate and the compiled
large-horizon realized theorem applies. Otherwise, `Real.sq_sqrt` and ordered
algebra give `T<=4*sqrt(K*T*log K)`, so the trivial bound is the minimum.

Contracts are a probability prior, Standard Borel Env/Action, measurable
singletons, decidable nonempty finite arms with `2<=K`, predictable measurable
`[0,1]` losses, and a supported comparator. No positive-horizon, independence,
stationarity, obliviousness, concentration, or manual-integrability premise is
used. Retrieval uses the realized/tuned local cards, Mathlib Real log/sqrt,
measure, finite-sum, and order cards, EXP3 paper/textbook cards, and the weapon
card as inspiration only. Status is `leanCompiled`, root imported, with
declaration canaries and a full external final-theorem canary. Failure policy:
this closes the all-horizon expected realized-regret presentation for the
generated predictable-adversary model, not high-probability regret, stochastic
rewards, arbitrary non-predictable adversaries, or all EXP3 variants.

### Closed support leaf: COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE

Closed locally in `BanditRLProof.ConditionalExpectationReward`. For finite
`mu`, `mcond <= mOmega`, and `Measurable[mcond] X` into any countably generated
target, the conditional-expectation kernel pushed forward by `X` is trim-a.e.
the deterministic kernel at `X`, equivalently `Measure.dirac (X omega)`.

The proof uses `compProd_trim_condExpKernel`, `Measure.compProd_map`,
`Measure.compProd_deterministic`, `trim_eq_map`, `Measure.map_map`, and
`Kernel.ae_eq_of_compProd_eq`. This supports Standard Borel Real-valued history
prefixes without a `Countable` or measurable-singleton assumption. Status is
`leanCompiled` with kernel and pointwise Dirac canaries. Failure policy: do not
infer a next-coordinate distribution or a conditional MGF from this freeze
law alone. The generated EXP3 action-law and bounded centered-loss MGF transport
now compile in the adjacent successor concentration leaf; initial-time and
finite-sum process assembly remain open.

### Closed support leaf: EXP3-REALIZED-DEVIATION-SUCC-COND-MGF

Closed locally in `BanditRLProof.Exp3RealizedConcentration`. On the joint
generated predictable-EXP3 measure, conditioning on `(Env, finite pair prefix)`
gives a successor realized-loss deviation `HasCondSubgaussianMGF` witness at
`intervalVarianceProxy 0 1`. The route uses the compiled successor action
`condDistrib`, finite-support singleton-to-measure reconstruction, measurable
state freezing, exact finite-action mean, bounded-centered Hoeffding, and the
generated feedback a.e. equality.

Contracts are finite prior, Standard Borel nonempty Env/Action, measurable
singletons, decidable nonempty finite arms, legal gamma, and predictable
measurable unit-interval losses. No `Countable Action`, independence,
stationarity, probability prior, or supplied exponential integrability is
needed. Status is `leanCompiled` with root import and external canary. Next
open leaf: prove the initial action/deviation conditional MGF relative to the
Env sigma-algebra and package the zero-shifted finite-horizon process as
strongly adapted; only then consume Azuma. Do not infer a high-probability
regret theorem from this one-step successor result. Its initial-time and
finite-sum consumers now compile in the closed leaf below.

### Closed support leaf: EXP3-REALIZED-DEVIATION-SUM-TAIL

Closed locally in `BanditRLProof.Exp3RealizedDeviationTail`. The generated
predictable EXP3 trajectory now satisfies the complete one-sided finite-horizon
tail for realized loss minus exploration-mixed predictable loss, with proxy
`horizon * intervalVarianceProxy 0 1` and an ENNReal exponential RHS.

The proof obtains the time-zero conditional MGF from the initial action law,
uses the existing successor MGF for later rounds, and assembles both through a
shifted Env/finite-prefix filtration with deterministic zeroth coordinate.
Explicit finite-prefix factorization closes `StronglyAdapted`; the local
Mathlib-backed Azuma wrapper then yields the tail after process/proxy sum
normalization. Contracts are a probability prior, Standard Borel nonempty
Env/Action, measurable action singletons, decidable nonempty finite arms,
legal gamma, predictable measurable unit-interval losses, and a nonnegative
threshold. Status is `leanCompiled`, root imported, with an external full
theorem canary. Remaining open work is deterministic confidence-event assembly
with the EXP3 potential/comparator bound and a user-facing delta radius; do not
label this leaf alone as complete high-probability regret. Its delta-radius
consumer now compiles below.

### Closed support theorem: EXP3-REALIZED-DEVIATION-DELTA-CONFIDENCE

Closed locally in `BanditRLProof.Exp3RealizedConfidence`. For positive horizon
and delta, the cumulative generated realized-minus-exploration-mixed deviation
exceeds `sqrt(2 * horizon * intervalVarianceProxy 0 1 * log(1/delta))` with
probability at most `ENNReal.ofReal delta`. The route is a direct consumer of
the finite-horizon ENNReal Azuma theorem plus compiled Real sqrt/log algebra.

Statement audit for the intended high-probability regret route found a precise
remaining obstruction. The available pathwise Hedge theorem compares the
pure-`q` importance-weighted estimate against the comparator importance-weighted
estimate and includes a random estimator-square sum. It does not pathwise
compare exploration-mixed predictable loss against true comparator loss.
Required next obligations are therefore: (1) conditional concentration of the
comparator estimator around true comparator loss; (2) conditional concentration
of the pure-`q` cross-weight estimator around predictable pure-`q` loss; and
(3) high-probability control of the random second-moment sum, or an explicit
EXP3.P-style biased estimator route. Do not replace these with unsupported
deterministic event algebra.

### Closed support theorem: EXP3-COMPARATOR-ESTIMATOR-DELTA-CONFIDENCE

Closed locally in `BanditRLProof.Exp3ComparatorConfidence`. For a fixed
supported comparator, positive horizon, and positive delta, the cumulative
observed importance-weighted comparator estimator minus its true predictable
loss has the delta tail with Hoeffding proxy
`horizon * intervalVarianceProxy 0 (1 / (gamma / |arms|))`.

The route compiles a generic finite-action conditional-MGF bridge from the
positive exploration floor, identifies the raw estimator mean by exact finite
unbiasedness, instantiates the generated zero/successor action laws, transports
to scalar observed feedback, and applies the shifted strongly-adapted sum-tail
theorem. This closes obligation (1) above. Obligation (2) now compiles in the
next leaf; obligation (3) remains. No full high-probability regret theorem is
claimed.

### Closed support theorem: EXP3-PURE-CROSS-WEIGHT-DELTA-CONFIDENCE

Closed locally in `BanditRLProof.Exp3PureConfidence`. For positive horizon and
delta, cumulative `sampledTrajectoryPurePredictableLossAt` minus
`sampledTrajectoryPureObservedLossAt` has the delta tail with Hoeffding proxy
`horizon * intervalVarianceProxy 0 (1 / (gamma / |arms|))`; the opposite tail
is retained as a symmetric helper.

The route proves the missing generic `p`-sampled/`q`-weighted conditional MGF
from exact cross-weight cancellation, instantiates pure `q` at generated zero
and successor rounds, transports to observed scalar feedback, negates the MGF
for the sign required by the Hedge regret decomposition, and proves the shifted
finite-sum process strongly adapted. This closes obligation (2) above.
Obligation (3) now compiles in the downstream predictable high-probability
regret theorem. The current Hoeffding proxy still scales as
`(|arms|/gamma)^2` per round, so a variance-sensitive/Freedman route may be
needed for an ideal final rate.

### Closed theorem route: EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3HighProbabilityRegret`. Generated rewards
belong to `[0,1]` almost surely and the exact scalar-feedback square is
`reward^2 / p(chosen)`, so the exploration floor gives the pathwise bound
`sum_t observedMixedSquaredImportanceWeightedLossAt <=
horizon / (gamma / |arms|)` without a third concentration theorem.

The primary endpoint
`sampledPredictable_highProbabilityRegret_tail_total_delta` combines this a.e.
bound with sampled Hedge, exploration bias, the pure-`q`
predictable-minus-observed confidence event, and the comparator
observed-minus-true event. The bad pseudo-regret event is a.e. contained in the
union of those two confidence events. Assigning `delta / 2` to each event gives
total failure probability `ENNReal.ofReal delta`; the raw two-event union
wrapper is also exposed. This closes generated predictable high-probability
pseudo-regret. The generated realized selected-loss consumer now compiles
downstream; ideal-rate EXP3 remains a variance-sensitive/Freedman or EXP3.P
route.

### Closed theorem route: EXP3-REALIZED-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3RealizedHighProbabilityRegret`. The key
pathwise identity rewrites cumulative scalar generated loss minus the true
predictable comparator as predictable pseudo-regret plus cumulative
realized-minus-exploration deviation. This makes the bad realized-regret event
a subset of the union of the compiled predictable-regret bad event and the
compiled realized-deviation bad event.

The endpoint
`sampledPredictable_realizedHighProbabilityRegret_tail_total_delta` assigns
`delta / 3` to each underlying pure-`q`, comparator-estimator, and
realized-deviation event. Its budget is
`sampledPredictableRealizedHighProbabilityRegretBudget arms eta gamma horizon
(delta / 3)`, and its total failure probability is `ENNReal.ofReal delta`.
This closes generated realized selected-loss high-probability regret for the
current range-Hoeffding radii. It does not close tuned or ideal-rate EXP3:
the importance-weighted proxy remains quadratic in `|arms|/gamma`, so a
variance-sensitive/Freedman argument or EXP3.P modification remains open.

### Closed support leaf: CONCENTRATION-FIXED-TILT-CONDITIONAL-MGF-SUM-TAIL

Closed locally in `BanditRLProof.ConcentrationFixedMGF`. The generic theorem
`measure_sum_ge_le_of_hasCondMGFUpperBoundAt` composes one unconditional and
successive conditional fixed-tilt MGF budgets along a strongly adapted process,
then bounds the finite-sum upper tail by
`exp (-tilt * eps + sum_i psi_i)` for `tilt >= 0`.

The proof uses kernel `compProd`, `condExpKernel`, diagonal-map transport,
finite-range induction, and `measure_ge_le_exp_mul_mgf`. Each witness requires
exponential integrability at every real multiple because the composition proof
uses `MemLp`; MGF domination is only at the selected tilt. This closes the
generic composition and Chernoff layer, not a Bernstein/Freedman theorem.

The fixed-comparator one-step budget and generated finite-horizon consumer now
compile in the adjacent route leaf, and the analogous pure-cross budget now
compiles as well. Downstream improved-regret consumers remain open. Local Mathlib
search found no existing Freedman, Bernstein, sub-gamma, or predictable-
quadratic-variation tail primitive; do not substitute range-Hoeffding and
label it variance-sensitive.

### Closed route leaf: EXP3-COMPARATOR-BERNSTEIN-FIXED-TILT

Closed locally in `BanditRLProof.Exp3ComparatorBernstein`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_fixedTilt` gives the
generated fixed-comparator tail
`exp (-tilt * threshold + horizon * tilt^2 / (gamma / |arms|))` for
`0 <= tilt <= gamma / |arms|`.

The proof closes the previously named one-step blocker: it combines
`Real.abs_exp_sub_one_sub_id_le` with the exact finite-action centered second
moment, transports that MGF through `condExpKernel`, instantiates every
generated round, and invokes the compiled fixed-tilt sum theorem. The remaining
work is no longer the scalar or law-transport source. The optimized delta
corollary and pure-cross analogue are compiled in adjacent route leaves;
comparator union and downstream improved EXP3 high-probability regret remain.
Do not call the current result a full Freedman theorem.

### Closed route leaf: EXP3-COMPARATOR-BERNSTEIN-DELTA-CONFIDENCE

Closed locally in `BanditRLProof.Exp3ComparatorBernstein`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta` bounds
the generated fixed-comparator bad event at radius
`2*sqrt(T*budget/epsilon)+budget/epsilon` by `ENNReal.ofReal delta`, with
`epsilon=gamma/|arms|` and `budget=max(log(1/delta),0)`.

The scalar proof splits at `budget <= epsilon*T`, selecting the unconstrained
square-root tilt below the boundary and `tilt=epsilon` above it. It then
specializes the fixed-tilt generated tail and converts `Measure.real` to
ENNReal. Contracts permit `T=0` and require only `delta>0`, not `delta<=1`.
The pure-cross variance-sensitive delta theorem in the sign required by the
Hedge decomposition is compiled in the adjacent route leaf below; comparator
union and full improved regret assembly remain downstream.

### Closed route leaf: EXP3-PURE-CROSS-BERNSTEIN-DELTA-CONFIDENCE

Closed locally in `BanditRLProof.Exp3PureBernstein`. The endpoint
`sampledPurePredictableMinusObserved_sum_tail_bernstein_delta` bounds the
generated pure-Hedge predictable-minus-observed cross-weight event at radius
`2*sqrt(T*budget/epsilon)+budget/epsilon` by `ENNReal.ofReal delta`, with
`epsilon=gamma/|arms|` and `budget=max(log(1/delta),0)`.

The source proof uses the exact sampled-coordinate formula and the bound
`sum_a q(a)^2 loss(a)^2 / p(a) <= 1/epsilon`, proves the fixed-tilt MGF in the
required negative-estimator sign, and reuses compiled law transport,
adaptedness, finite-sum Chernoff, and scalar optimization APIs. Contracts allow
`T=0` and every `delta>0`; there is no comparator or eta premise. The next
consumer is now compiled below. Its assembly retains the deterministic
`T/epsilon` Hedge-square contribution; do not label either result a general
Freedman theorem.

### Closed theorem route: EXP3-PREDICTABLE-BERNSTEIN-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3BernsteinHighProbabilityRegret`. The
endpoint
`sampledPredictable_bernsteinHighProbabilityRegret_tail_total_delta` combines
the variance-sensitive pure-cross and fixed-comparator confidence events with
sampled Hedge, exploration bias, and the existing pathwise estimator-square
bound. It evaluates both confidence radii at `delta/2` and gives total failure
probability `ENNReal.ofReal delta`; the raw two-event wrapper is also exposed.

The event signs match the Hedge decomposition: pure predictable minus observed
cross-weighted loss and observed comparator estimator minus true comparator
loss. Contracts permit `T=0` and every `delta>0`, with no independence,
stationarity, countability, supplied integrability, or separate square-tail
premise. Its realized selected-loss consumer is compiled below. The retained
`T/epsilon` square term means this does not close an ideal-rate EXP3/EXP3.P or
general Freedman route.

### Closed theorem route: EXP3-RANDOM-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3RandomSquareHighProbabilityRegret`. The
supporting Markov endpoint controls the generated finite-horizon sum of observed
mixed importance-weighted estimator squares at threshold
`|arms|*T/deltaSquare`. It reuses the compiled expectation upper bound
`|arms|*T`, after proving pointwise nonnegativity and the required finite-sum
measurability/integrability, and applies Mathlib
`Integrable.measure_le_integral`.

The primary total-delta theorem adds this square event to the pure-cross and
fixed-comparator Bernstein bad events. Each receives `delta/3`, so generated
exploration-mixed predictable regret is controlled by a budget whose square
term is `eta/(1-gamma) * (3*|arms|*T/delta)` rather than
`eta/(1-gamma) * (|arms|*T/gamma)`. Contracts require positive horizon and
delta in addition to the existing predictable EXP3 regularity; no independence,
stationarity, countability, supplied integrability, or law transport is added.

Failure policy: reciprocal `gamma` is removed from the Hedge-square term, but
Markov has polynomial `1/delta` cost and the two confidence radii still contain
the exploration floor. Its generated realized consumer compiles below; ideal
logarithmic-confidence `sqrt(K*T)` still needs stronger variance-process
concentration or EXP3.P.

### Closed theorem route: EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET

Closed locally in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret`. The
endpoint
`sampledPredictable_randomSquareBernsteinRealizedHighProbabilityRegret_tail_total_delta`
controls cumulative generated scalar loss minus a supported comparator's true
predictable cumulative loss. Its budget adds the random-square predictable
budget to the realized-deviation radius.

The proof reuses the exact pathwise realized-regret decomposition and contains
the target event in the union of the compiled three-event predictable bad set
and the realized-deviation bad set. The raw endpoint exposes all four failure
allocations; the public theorem assigns `delta/4` to each and proves total
failure `ENNReal.ofReal delta`. Contracts require a probability prior, Standard
Borel nonempty Env/Action, measurable singletons, nonempty finite arms,
`eta>0`, `0<gamma<1`, predictable `[0,1]` losses, a supported comparator,
positive horizon, and positive allocations. No independence, stationarity,
countability, supplied integrability, or new law transport is added.

Failure policy: the generated realized consumer is closed without restoring
reciprocal `gamma` in the Hedge-square term. Markov still costs `1/delta`, both
Bernstein radii retain exploration-floor dependence, and the realized radius
remains Hoeffding/Azuma. A general Freedman theorem and ideal
logarithmic-confidence `sqrt(K*T)` EXP3.P rate remain open. Its
learning-rate-only tuning compiles below.

### Closed theorem route: EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-TUNING

Closed locally in `BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning`. The
learning rate
`randomSquareHighProbabilityLearningRate K T delta` is
`sqrt(log K*(delta/4)/(T*K))`. The deterministic theorem balances entropy and
the unamplified Markov-square term exactly, uses `gamma<=1/2` for the stability
factor, and bounds their sum by `3*sqrt(4*K*T*log K/delta)`.

The complete threshold adds `gamma*T`, both Bernstein confidence radii at
`delta/4`, and the realized-deviation radius at `delta/4`. The final theorem
`sampledPredictable_tunedRandomSquareBernsteinRealizedRegret_tail` transfers
the compiled generated realized tail to this threshold. Contracts are `K>=2`,
`T>0`, `0<gamma<=1/2`, `delta>0`, the standard probability/Standard-Borel
generated-trajectory assumptions, predictable `[0,1]` losses, and a supported
comparator. No `delta<=1`, cubic/quadratic dominance, independence,
stationarity, countability, supplied integrability, or new law transport is
required.

Failure policy: eta tuning is closed and exposes the honest
`sqrt(K*T*log K/delta)` Markov contribution. The explicit large-horizon gamma
schedule compiles below, while this theorem preserves the weaker caller-chosen
surface. Do not claim general Freedman or ideal logarithmic-confidence EXP3.P.

### Closed theorem route: EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING

Closed locally in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning`. The route first
normalizes every `delta/4` confidence budget to `log(4/delta)`, bounds each of
the two Bernstein radii by `3*gamma*T`, and bounds the realized radius by
`gamma*T`. The resulting characterized generated tail has threshold
`3*sqrt(4*K*T*log K/delta)+8*gamma*T`.

The final endpoint
`sampledPredictable_explicitRandomSquareBernsteinRealizedRegret_tail` sets
`gamma=min(1/2,max((K*log(4/delta)/T)^(1/3),
sqrt(2*v*log(4/delta)/T)))`. Under `0<delta<=1`, `K>=2`, `T>0`,
`8*K*log(4/delta)<=T`, and `8*v*log(4/delta)<=T`, the raw scale is at most
`1/2`, clipping is inactive, and the exact cubic/quadratic contracts follow.
The usual probability, Standard-Borel, measurable-singleton, predictable
`[0,1]` loss, and supported-comparator contracts remain; no independence,
stationarity, countability, supplied integrability, or new law transport is
introduced.

Retrieval evidence is the compiled random-square realized tuning route, the
generic root/dominance lemmas in `Exp3BernsteinExplicitTuning`, Mathlib
`Real.rpow`/`Real.sqrt` and max/min order APIs, the Auer EXP3 paper card, and
the inspiration-only potential weapon. Failure policy: large-horizon gamma
tuning is closed, but the Markov term still scales with `1/sqrt(delta)` and the
realized radius remains Hoeffding/Azuma. The active-clipping branch is handled
by the coarse all-horizon consumer below. Do not relabel either result as
general Freedman or ideal EXP3.P.

### Closed theorem route: EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON

Closed locally in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedAllHorizon`. The exact regime
predicate contains `8*K*log(4/delta)<=T` and `8*v*log(4/delta)<=T`. The
threshold uses the explicit random-square bound in that regime and `T+1`
otherwise. The final generated theorem performs the regime split internally,
invoking the explicit tail in the positive branch and the compiled
zero-probability trivial tail in the negative branch.

Contracts are `K>=2`, `T>0`, `0<delta<=1`, the usual probability and
Standard-Borel generated-trajectory assumptions, predictable `[0,1]` losses,
and a supported comparator. It requires no large-horizon proof from the caller,
independence, stationarity, countability, supplied integrability, or new law
transport. Retrieval evidence is the explicit random-square route, the generic
all-horizon pathwise `regret<=T` leaf, Mathlib a.e./measure-zero and finite-sum
order APIs, the Auer EXP3 card, and the inspiration-only potential weapon.

Failure policy: all positive horizons are covered, but the negative branch is
the intentionally coarse `T+1` fallback. The refined branch retains Markov
`1/sqrt(delta)` and Hoeffding/Azuma realized deviation. A sharp active-clipping
rate, general Freedman theorem, and ideal EXP3.P remain open.

### Closed theorem route: EXP3-REALIZED-BERNSTEIN-HIGH-PROBABILITY-REGRET

Closed locally in
`BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret`. The endpoint
`sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_total_delta`
controls cumulative generated scalar loss minus the true predictable loss of
one supported comparator. Its budget adds the predictable Bernstein regret
budget and the realized-deviation radius at `delta/3`; the raw theorem exposes
the pure-cross Bernstein, fixed-comparator Bernstein, and realized-deviation
failure terms separately.

The proof reuses the exact finite-sum identity between realized regret,
predictable regret, and realized-minus-predictable deviation, followed by set
inclusion and `measure_union_le`. Contracts require positive horizon and delta,
with no `delta<=1`, independence, stationarity, countability, supplied
integrability, or new law transport. This closes the generated selected-loss
consumer for the Bernstein predictable route. It does not close a fully
Bernstein/Freedman variance-process theorem or ideal tuned rate: the realized
radius remains Hoeffding/Azuma and the Hedge-square term remains `T/epsilon`.

### Closed theorem route: EXP3-BERNSTEIN-TUNED-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3BernsteinTuning`. The endpoint
`sampledPredictable_tunedBernsteinRealizedHighProbabilityRegret_tail` uses
`eta=sqrt(log K * gamma/(T*K))` and proves failure probability at most
`ENNReal.ofReal delta` for the generated realized-regret threshold
`11*gamma*T`.

The regularity and rate premises are explicit: `2<=K`, `T>0`,
`0<gamma<=1/2`, `0<delta<=1`, `K*log K<=gamma^3*T`,
`K*log(3/delta)<=gamma^3*T`, and the analogous quadratic realized-variance
budget. The scalar proof balances the entropy and pathwise square terms,
bounds both Bernstein radii and the realized radius, and consumes the prior
three-event tail by set inclusion. This is a characterized `T^(2/3)`-type
corollary, not the ideal EXP3.P rate. Open next: construct a concrete
cube-root/max `gamma` satisfying these contracts; this consumer is now closed
below. The active-clip branch is also closed by the all-horizon fallback below.
Open beyond that: replace the deterministic square term/algorithm to support a
`sqrt(K*T)` route.

### Closed theorem route: EXP3-EXPLICIT-BERNSTEIN-HIGH-PROBABILITY-REGRET

Closed locally in `BanditRLProof.Exp3BernsteinExplicitTuning`. The primary
endpoint `sampledPredictable_explicitBernsteinRealizedHighProbabilityRegret_tail`
chooses the clipped maximum of two cube-root scales and one realized
square-root scale, chooses the balanced learning rate from that `gamma`, and
proves the generated selected-loss regret threshold `11*gamma*T` with failure
probability at most `ENNReal.ofReal delta`.

Local APIs are `Real.rpow_inv_natCast_pow`, `Real.sqrt_le_iff`, power
monotonicity, max/min order lemmas, and the compiled characterized tuned tail.
The proof derives clip inactivity and every dominance contract from the three
displayed factor-eight horizon inequalities. Contracts require `K>=2`,
`T>0`, `0<delta<=1`, the existing generated predictable-loss regularity, and
a supported comparator; no caller-supplied cubic/quadratic proofs remain.
Failure policy: this closes the large-horizon explicit schedule and is consumed
by the all-horizon leaf below. Ideal `sqrt(K*T)` still needs stronger
random-square/variance control or EXP3.P.

### Closed theorem route: EXP3-ALL-HORIZON-BERNSTEIN-REALIZED-REGRET

Closed locally in `BanditRLProof.Exp3BernsteinAllHorizon`. Supporting
statements prove predictable comparator losses nonnegative, each generated
realized loss at most one almost surely, their finite-horizon aggregation, and
realized regret at most `T` almost surely. The strict `T+1` tail therefore has
measure zero.

The primary endpoint
`sampledPredictable_allHorizonBernsteinRealizedRegret_tail` uses
`bernsteinAllHorizonRegretThreshold`: `11*gamma*T` under the three explicit
factor-eight inequalities and `T+1` otherwise. Local APIs are the generated
realized-to-selected a.e. law, the selected `[0,1]` contract, `ae_all_iff`,
finite-sum order, `measure_eq_zero_iff_ae_notMem`, and the compiled explicit
Bernstein tail. Contracts require a probability prior, Standard Borel
nonempty Env/Action, measurable action singletons, decidable arms with `K>=2`,
predictable measurable `[0,1]` losses, a supported comparator, `T>0`, and
`0<delta<=1`; no large-horizon premise is exposed to the caller.

Failure policy: the active-clipping gap is closed, but the fallback is a coarse
all-horizon presentation, not an ideal `sqrt(K*T)` theorem. Stronger random
estimator-square or variance-process control remains open.

## Compiled leaf: EXP3 mixed-square exponential confidence

Lean statement:
`Exp3.sampledPredictableObservedMixedSquared_sum_tail_delta` gives failure
at most `ENNReal.ofReal delta` above
`K*T + sampledMixedSquaredConfidenceRadius arms gamma T delta`.

Local APIs/imports: `Exp3MixedSquareConfidence`,
`mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div`, the exact
probability-weighted mixed-square identity, finite-action measures,
`condExpKernel` action-map/frozen-history transport,
`boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`,
`sampledPredictableDeviationFiltration`, the strongly-adapted conditional
sum tail, and `observedAt_eq_predictableAt_ae`.

Proof route: bound the raw score by `1/epsilon`; center by
`sum_a loss(a)^2`; construct the conditional MGF from the finite action law;
sum the shifted adapted process; bound conditional means by `K*T`; transport
the latent sum to observed feedback a.e.; specialize the exponential budget
to `log(1/delta)`.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `0<gamma<=1`;
predictable measurable `[0,1]` losses; positive horizon and delta. No
comparator, eta positivity, `delta<=1`, independence, stationarity,
countability, supplied integrability, or new reward-law premise.

Retrieval/status: local random-square and comparator-confidence leaves,
Mathlib probability MGF/kernel/finite-sum/integral/order APIs, Auer EXP3 card,
and inspiration-only potential weapon; `leanCompiled`, root imported, with a
full external delta-theorem canary.

Failure policy: logarithmic confidence replaces the Markov `1/delta`
threshold, but the proxy is still order `(K/gamma)^2` per round. The
predictable, realized, and learning-rate-tuned consumers now compile below;
gamma scheduling, sharper variance-process/Freedman control, and ideal EXP3.P
remain open.

## Compiled leaf: exponential-square predictable EXP3 regret

Lean statements:
`Exp3.sampledPredictableExponentialSquareBernsteinHighProbabilityRegretBudget`,
`Exp3.sampledPredictable_exponentialSquareBernsteinHighProbabilityRegret_tail`,
and its `_tail_total_delta` wrapper. The primary theorem bounds generated
exploration-mixed predictable regret against a supported comparator and
allocates `delta/3` to the square, pure-cross, and comparator events.

Local APIs/imports: `Exp3MixedSquareConfidence`, the observed mixed-square
delta tail, sampled pathwise Hedge inequality, exploration-bias inequality,
pure-cross and comparator Bernstein delta tails, `measure_mono_ae`,
`measure_union_le`, `ENNReal.ofReal_add`, finite sums, and linear order
arithmetic.

Proof route: define three bad events; use `K*T + squareRadius` for the square
event; apply all three tails; outside their union combine Hedge, exploration,
and strict good-event bounds; prove the regret-event inclusion a.e.; union
bound; normalize three `delta/3` allocations.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon and delta. No `delta<=1`, independence, stationarity,
countability, supplied integrability, or new law transport.

Retrieval/status: exponential mixed-square confidence, prior random-square
regret assembly, pure/comparator Bernstein leaves, Mathlib finite-sum/order/
measure APIs, Auer EXP3 card, inspiration-only potential weapon;
`leanCompiled`, root imported, full external total-delta canary.

Failure policy: the predictable budget no longer contains Markov
`K*T/delta`, but the square interval radius remains proportional to
`K/gamma * sqrt(T log(1/delta))`. The realized consumer now compiles; new
learning-rate tuning also compiles, while gamma scheduling, general Freedman,
and ideal EXP3.P remain open.

## Compiled leaf: mixed-square Bernstein realized explicit tuning

Status: `leanCompiled`, root imported, focused build, external full-theorem
canary. The Lean-facing endpoint
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail` uses eta
balanced against `K*T+sampledMixedSquaredBernsteinConfidenceRadius(delta/4)`
and the existing conservative four-scale clipped gamma; its threshold is
`14*gamma*T`.

Local APIs/imports are the Bernstein-square realized eta-tuning module, the
exponential-square explicit schedule and its contract package, the exact
mixed-square Bernstein variance coefficient/radius, reusable Bernstein and
realized radius bounds, `Real.sqrt`, field/ring/nonlinear arithmetic, and
`measure_mono`. The proof identifies the coefficient as `K^2/gamma`, controls
the radius after multiplying by `log K`, bounds the balanced root by
`2*gamma*T`, characterizes the full threshold, transports the four schedule
contracts, and invokes the generated characterized tail.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable singletons; decidable arms with `K>=2`; predictable
`[0,1]` losses; supported comparator; `T>0`; `0<delta<=1`; arm factor-four,
mixed factor-64, confidence factor-eight, and realized factor-eight horizon
contracts. Retrieval evidence is the Bernstein realized tuning/confidence
rows, the exponential explicit schedule, Mathlib log/sqrt/order/finite-sum
APIs, the Auer EXP3 card, and inspiration-only potential weapon.

Failure policy: the schedule is reused conservatively and is not a claimed
fifth-root/coupled optimum. The current linear `log_+/epsilon` correction is
controlled by this leaf; eliminating or improving it, Hoeffding/Azuma
replacement, random predictable quadratic variation, general Freedman, and
ideal EXP3.P remain open. The active-clipping complement now compiles below
through a coarse `T+1` fallback.

## Compiled leaf: mixed-square Bernstein realized all horizon

Status: `leanCompiled`, root imported, focused build, external full-theorem
canary. The Lean-facing endpoint
`sampledPredictable_allHorizonBernsteinSquareRealizedRegret_tail` uses the
explicit variance-sensitive threshold under the exact four large-horizon
contracts and strict `T+1` otherwise.

Local APIs/imports are the Bernstein-square explicit tuning module,
`Exp3BernsteinAllHorizon`, the explicit generated tail, the generic
`sampledPredictable_trivialRealizedRegret_tail`, classical `if`/`by_cases`,
and the compiled finite-sum/order/measure-zero fallback APIs. The proof
branches on the exact regime, invoking the explicit theorem in the positive
branch and the zero-probability fallback with the same eta and gamma in the
negative branch.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable singletons; decidable arms with `K>=2`; predictable
`[0,1]` losses; supported comparator; `T>0`; and `0<delta<=1`. No caller
regime proof, independence, stationarity, countability, supplied
integrability, or new law transport is required. Retrieval evidence is the
explicit Bernstein mixed-square row, generic and exponential all-horizon
rows, Mathlib measure/finite-sum/order APIs, the Auer EXP3 card, and the
inspiration-only potential weapon.

Failure policy: all positive horizons are covered, but the negative branch is
deliberately coarse. The refined branch retains the controlled linear
`log_+/epsilon` term and Hoeffding/Azuma realized deviation; do not claim
sharp active clipping, a sharper coupled schedule, random quadratic
variation, general Freedman, or ideal EXP3.P.

## Compiled leaf: mixed-square Bernstein confidence

Lean statement:
`Exp3.sampledPredictableObservedMixedSquared_sum_tail_bernstein_delta` gives
failure at most `ENNReal.ofReal delta` above `K*T` plus
`2*sqrt(T*(K/epsilon)*log_+(1/delta)) + log_+(1/delta)/epsilon`, with
`epsilon=gamma/K`.

Local APIs/imports: `Exp3MixedSquareBernstein`, exact finite-action mixed-square
moments, `HasMGFUpperBoundAt`/`HasCondMGFUpperBoundAt`, existing generated
action-law and frozen-history transport, strongly-adapted fixed-tilt sums,
observed/predictable equality, and finite-sum/order/exponential algebra.

Proof route: derive the centered `K/epsilon` second-moment bound and
`1/epsilon` range cap; prove and transport the one-step fixed-tilt MGF; package
generated zero/successor rounds; sum the process; apply the `K*T` mean bound;
transfer to observed feedback; optimize separate variance and cap parameters.

Regularity/status: probability prior; Standard Borel nonempty Env/Action;
measurable singletons; decidable nonempty arms; arbitrary eta;
`0<gamma<=1`; predictable `[0,1]` losses; every natural horizon; `delta>0`;
`leanCompiled`, root imported, focused build, external delta-theorem canary.
No comparator, eta positivity, positive horizon, `delta<=1`, independence,
stationarity, countability, supplied integrability, or new law transport.

Failure policy: this is variance-sensitive fixed-tilt control but still uses a
deterministic per-round bound, not a random predictable quadratic variation.
Anytime/self-normalized Freedman and ideal EXP3.P remain open.

## Compiled leaf: mixed-square predictable variance process

Lean statements: `Exp3.mixedSquaredEstimatorCenteredSecondMoment`, its
finite-action integral identity and `K/epsilon` bound,
`Exp3.sampledPredictableMixedSquaredVarianceProcess_isPredictable`, and
`Exp3.sampledPredictableMixedSquaredVariance_sum_le`. The shifted process is
zero at time zero and uses the actual round-`i` finite-law centered second
moment at index `i+1`; the cumulative actual-time bound is
`T*(K/(gamma/K))`. The generic name intentionally avoids calling this a
variance when a supplied finite law can give an arm zero mass; generated EXP3
has strict supported positivity from the exploration floor.

Local APIs/imports and proof route: `Exp3MixedSquareBernstein`, Mathlib
predictable processes, generated probability sources, predictable-loss
regularity, finite-action measure integrals, finite-prefix filtration
factorization, and finite sums. Status is `leanCompiled`, root imported, with
external predictability and cumulative-bound canaries. Contracts are
measurable Env/Action, measurable singletons, decidable nonempty arms,
arbitrary eta, `0<gamma<=1`, predictable `[0,1]` losses, and any horizon; no
prior, Standard Borel, comparator, delta, or supplied integrability is needed.

Failure policy: the finite-action row alone is not an ambient `condExpKernel`
conditional-square identity, but the adjacent compiled row supplies that
transport and the following row now supplies its fixed-horizon random-variance
tail. Maximal/anytime control and regret integration remain separate.

## Compiled leaf: mixed-square predictable variance conditional square law

Lean statements:
`mixedSquaredEstimatorDeviation_condExpKernel_map_eq_finiteActionMeasure_of_condDistrib`,
`integral_sq_mixedSquaredEstimatorDeviation_condExpKernel_eq_of_condDistrib`,
the generated zero/successor wrappers, and
`sampledPredictableMixedSquaredDeviationProcess_condExpKernel_integral_sq_eq_varianceProcess`.
The final theorem identifies the ambient conditional square of process
increment `n+1` given `F_n` with the shifted predictable variance `V_(n+1)`.

Local APIs/imports and proof route: generated action `condDistrib` laws,
finiteActionKernel/finiteActionMeasure, action and frozen-history
`condExpKernel` pushforwards, `Measure.map_map`, `Measure.map_congr`, two
`integral_map` rewrites, finite-prefix restrictions, and filtration
zero/successor equations. Freeze the history, map the selected action through
the centered score, integrate the square, instantiate zero/successor, and
normalize shifted indexing.

Regularity/status: finite prior; Standard Borel nonempty Env/Action; measurable
singletons; decidable nonempty arms; arbitrary eta; `0<gamma<=1`; predictable
`[0,1]` losses; any process index; `leanCompiled`, root imported, focused and
external full-theorem builds. No probability prior, comparator, horizon,
delta, independence, stationarity, or supplied integrability is required.

Failure policy: exact ambient conditional-square identification is closed and
consumed by the fixed-horizon predictable-variance tail below. This row alone
is not maximal/anytime/self-normalized control or ideal EXP3.P.

## Compiled leaf: mixed-square predictable-variance tail

Lean statements include the exact finite-law MGF and compensated MGF,
`mixedSquaredEstimator_compensated_hasCondMGFUpperBoundAt_of_condDistrib`,
generated zero/successor wrappers, the shifted compensated process and sum
identity, the fixed-tilt joint-event theorem, and
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta`.
The primary endpoint bounds the event
`sum X >= 2*sqrt(v*log_+(1/delta))+log_+(1/delta)/(gamma/K)` together with
`sum V <= v` by `ENNReal.ofReal delta`.

Local APIs/imports and proof route: exact finite-action centered second moment,
support bound `|X|<=1/epsilon`, `HasMGFUpperBoundAt.compensated`, frozen-history
conditional-kernel pushforward, generated action laws, strongly adapted
deviation process, predictable variance process, fixed-MGF sum iteration,
finite-sum shift identities, measure monotonicity, and the quadratic tilt
optimizer. Retain `V` in the one-step exponent, subtract it, iterate, prove
joint-event containment, then optimize the tilt.

Regularity/status: probability prior; Standard Borel nonempty Env/Action;
measurable singletons; decidable nonempty arms; arbitrary eta;
`0<gamma<=1`; predictable `[0,1]` losses; any horizon; positive variance
budget and delta for the optimized theorem. No comparator, independence,
stationarity, countability, caller integrability, or deterministic variance
envelope is required. Status is `leanCompiled`, root imported, focused-built,
and externally canaried.

Retrieval evidence: the predictable-variance and conditional-square leaves,
fixed-tilt conditional-MGF iteration, Mathlib conditional expectation/kernel/
integral/martingale/MGF/finite-sum cards, Auer EXP3 paper card, and
inspiration-only tail-inequality weapon.

Failure policy: fixed-horizon predictable-variance Bernstein/Freedman control
is closed for this generated process. Maximal/Ville, peeling/stitching,
anytime/self-normalized control, an unconditional tail without `sum V<=v`,
realized-loss replacement, and ideal EXP3.P remain open. The next consumer
must integrate the random variance event into regret without silently using
the deterministic `K/(gamma/K)` envelope.

## Compiled leaf: mixed-square Bernstein predictable EXP3 regret

Lean statements:
`Exp3.sampledPredictableBernsteinSquareHighProbabilityRegretBudget` and
`Exp3.sampledPredictable_bernsteinSquareHighProbabilityRegret_tail_total_delta`.
The latter allocates `delta/3` to the new square event and the existing
pure-cross/comparator Bernstein events.

Proof route and contracts: reuse the pathwise sampled Hedge and exploration
bias inequalities, prove a.e. containment in the three-event union, and apply
the compiled tails. Contracts are the generated predictable-adversary surface
with `eta>0`, `0<gamma<1`, a supported comparator, positive delta, and any
natural horizon; no independence, stationarity, supplied integrability, or
new law transport. Status is `leanCompiled`, root imported, with an external
total-delta canary.

Failure policy: generated predictable regret now consumes the improved square
radius. Its realized assembly now compiles; eta/gamma tuning remains open. Do
not claim general Freedman or ideal EXP3.P.

## Compiled leaf: mixed-square Bernstein realized EXP3 regret

Lean statements:
`Exp3.sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget`,
`Exp3.sampledPredictable_bernsteinSquareRealizedHighProbabilityRegret_tail`,
and its `_tail_total_delta` wrapper. The primary theorem bounds generated
realized selected-loss regret against a supported comparator and allocates
`delta/4` to the mixed-square, pure-cross, comparator, and realized events.

Local APIs/imports: `Exp3MixedSquareBernsteinHighProbabilityRegret`,
`Exp3RealizedConfidence`, the compiled predictable Bernstein-square tail,
`sampledPredictableRealizedDeviation_sum_tail_delta`,
`sampledTrajectoryRealizedDeviationAt`, `Finset.sum_sub_distrib`, `ring`,
`linarith`, `measure_mono`, `measure_union_le`, and `ENNReal.ofReal_add`.

Proof route: identify realized regret pathwise with exploration-mixed
predictable regret plus cumulative realized deviation; define the two
aggregate bad sets; apply both compiled tails; prove event containment from
their strict complements; union bound; normalize four `delta/4` allocations.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon and delta. No `delta<=1`, independence, stationarity,
countability, supplied integrability, or new law transport.

Retrieval/status: mixed-square Bernstein predictable regret,
realized-deviation delta confidence, exponential-square realized assembly,
Mathlib order/finite-sum/probability APIs, and the EXP3 paper card;
`leanCompiled`, root imported, focused builds, external total-delta canary.

Failure policy: the sharper deterministic `K/epsilon` square radius now
reaches generated realized regret. Learning-rate tuning now compiles;
exploration tuning remains open. This is not random predictable quadratic
variation, anytime/general Freedman, or ideal EXP3.P, and the realized radius
remains Hoeffding/Azuma.

## Compiled leaf: mixed-square Bernstein realized eta tuning

Lean statements include `Exp3.bernsteinSquareHighProbabilityScale`,
`Exp3.bernsteinSquareHighProbabilityLearningRate`,
`Exp3.bernsteinSquareRealizedTunedThreshold`, the complete-budget comparison,
and `Exp3.sampledPredictable_tunedBernsteinSquareRealizedRegret_tail`. The
primary endpoint uses `S=K*T+mixedSquareBernsteinRadius(delta/4)` and
`eta=sqrt(log K/S)` and controls generated realized regret at
`3*sqrt(log K*S)+gamma*T` plus the two action-confidence and realized radii.

Local APIs/imports: the Bernstein-square realized total-delta tail and budget,
mixed-square Bernstein radius/variance coefficient, `Real.sqrt_pos`,
`Real.sq_sqrt`, `Real.log_pos`, `field_simp`, `ring`, `nlinarith`, `linarith`,
positivity/order algebra, and `measure_mono`.

Proof route: prove epsilon and the variance coefficient positive from
`K>=2` and `gamma>0`; prove both pieces of the Bernstein radius nonnegative
and hence `S>0`; establish eta positivity and `eta^2*S=log K`; identify entropy
with `eta*S` and `sqrt(log K*S)`; use `gamma<=1/2` to bound stability by twice
entropy; compare full budgets and tighten the compiled total-delta event.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable singletons; decidable arms with `K>=2`; predictable measurable
`[0,1]` losses; supported comparator; positive horizon and delta; and
`0<gamma<=1/2`. No `delta<=1`, dominance premise, independence, stationarity,
countability, supplied integrability, or new law transport.

Retrieval/status: Bernstein-square realized/confidence routes,
exponential-square eta template, Mathlib real log/sqrt/order/finite-sum APIs,
Auer EXP3 card, and inspiration-only potential weapon; `leanCompiled`, root
imported, focused builds, and an external full-theorem canary.

Failure policy: eta tuning is closed against the deterministic `K/epsilon`
scale; explicit gamma scheduling and the all-horizon fallback now compile.
The linear `log_+/epsilon` term remains visible; eliminating it, random
predictable quadratic variation, general Freedman, bounded-loss
Hoeffding/Azuma realized radius, and ideal EXP3.P remain separate.

## Compiled leaf: exponential-square realized EXP3 regret

Lean statements:
`Exp3.sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget`,
`Exp3.sampledPredictable_exponentialSquareBernsteinRealizedHighProbabilityRegret_tail`,
and its `_tail_total_delta` wrapper. The primary theorem bounds generated
realized selected-loss regret against a supported comparator and allocates
`delta/4` to the square, pure-cross, comparator, and realized events.

Local APIs/imports: `Exp3MixedSquareExponentialHighProbabilityRegret`,
`Exp3RealizedConfidence`, the compiled predictable three-event tail,
`sampledPredictableRealizedDeviation_sum_tail_delta`,
`sampledTrajectoryRealizedDeviationAt`, `Finset.sum_sub_distrib`, `ring`,
`linarith`, `measure_mono`, `measure_union_le`, and `ENNReal.ofReal_add`.

Proof route: decompose realized regret pathwise into exploration-mixed
predictable regret plus realized deviation; define the two aggregate bad
sets; apply the predictable three-event tail and realized-deviation tail;
prove set inclusion from both strict complements; union bound; normalize four
`delta/4` allocations.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon and delta. No `delta<=1`, independence, stationarity,
countability, supplied integrability, or new law transport.

Retrieval/status: exponential-square predictable regret, realized-deviation
delta confidence, prior random-square realized assembly, Mathlib order/
finite-sum/sub-Gaussian APIs, Auer EXP3 card, inspiration-only potential
weapon; `leanCompiled`, root imported, full external total-delta canary.

Failure policy: Markov square dependence is removed from generated realized
regret, but the interval radius remains proportional to
`K/gamma * sqrt(T log(1/delta))` and the realized radius remains
Hoeffding/Azuma. Learning-rate tuning compiles below; gamma scheduling,
Freedman, and ideal EXP3.P remain open.

## Compiled leaf: exponential-square realized EXP3 learning-rate tuning

Lean statements: `Exp3.exponentialSquareHighProbabilityScale`,
`Exp3.exponentialSquareHighProbabilityLearningRate`, their positivity and
square-balance lemmas,
`Exp3.exponentialSquareHighProbabilityHedgeBudget_le_three_mul_sqrt`,
`Exp3.exponentialSquareBernsteinRealizedTunedThreshold`, the full-budget
comparison, and
`Exp3.sampledPredictable_tunedExponentialSquareBernsteinRealizedRegret_tail`.

Local APIs/imports: exponential-square realized total-delta tail,
`Real.sqrt_pos`, `Real.sq_sqrt`, `Real.log_pos`, `field_simp`, `ring`,
`nlinarith`, `linarith`, and `measure_mono`.

Proof route: define `S=K*T+squareRadius(delta/4)`; prove `S>0`; choose
`eta=sqrt(log K/S)`; prove `eta^2*S=log K`; rewrite entropy as `eta*S`;
use `gamma<=1/2` to bound stability by twice entropy; identify entropy with
`sqrt(log K*S)`; compare budgets and tighten the compiled realized tail.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable singletons; decidable arms with `K>=2`; predictable measurable
`[0,1]` losses; supported comparator; `T>0`; `0<gamma<=1/2`; `delta>0`.
No `delta<=1`, independence, stationarity, countability, supplied
integrability, dominance premise, or new law transport.

Retrieval/status: exponential-square realized/confidence leaves, prior
random-square tuning route, Mathlib log/sqrt/order/finite-sum APIs, Auer EXP3
card, inspiration-only potential weapon; `leanCompiled`, root imported, full
external theorem canary.

Failure policy: eta is now balanced against the exact exponential-square
scale, but gamma remains caller-selected and the threshold retains the
`K/gamma` square radius, two exploration-floor Bernstein radii, and
Hoeffding/Azuma realized radius. The explicit large-horizon gamma and its
all-horizon consumer now compile; the coarse fallback, Freedman, and ideal
EXP3.P remain separate.

## EXP3 mixed-square exponential realized explicit tuning

Status: `leanCompiled`, root imported, external full-theorem canary.

The explicit large-horizon gamma leaf now compiles. Its schedule is the clipped
maximum of `sqrt(K log K/T)`, the sixth root
`(K^2 (log K)^2 log(4/delta)/(2 T^3))^(1/6)`, the Bernstein confidence cube
root, and the realized-deviation square root. The generated realized tail has
threshold `14*gamma*T`. The proof uses the exact
`sampledMixedSquaredVarianceProxy=(K/(2*gamma))^2` identity and four explicit
horizon contracts to discharge quadratic, sixth-power, cubic, and realized
quadratic dominance.

Failure policy: do not describe the result as a sharp EXP3.P rate. The sixth
root is forced by the current interval Hoeffding proxy but contributes a
square-root horizon term after multiplying by `T`; the Bernstein confidence
cube root is what leaves the overall `T^(2/3)` limitation. The all-horizon
active-clip fallback now compiles below; a sharper route requires
variance-sensitive mixed-square Freedman control. The theorem assumes no
independence, stationarity, caller gamma, supplied integrability, or additional
law transport.

## EXP3 mixed-square exponential realized all horizon

Status: `leanCompiled`, root imported, focused build, external full-theorem
canary.

The all-horizon leaf defines the exact conjunction of the arm factor-four,
mixed factor-64, confidence factor-eight, and realized factor-eight contracts.
It uses the explicit exponential-square threshold in that regime and strict
`T+1` otherwise. The proof invokes the compiled `14*gamma*T`-characterized
tail in the positive branch and the generic generated pathwise
`regret<=T`/zero-probability theorem in the negative branch. It requires a
probability prior, Standard Borel nonempty Env/Action, measurable singletons,
decidable arms with `K>=2`, predictable `[0,1]` losses, a supported comparator,
`T>0`, and `0<delta<=1`; it adds no independence, stationarity, caller regime
proof, supplied integrability, or law transport.

Failure policy: every positive horizon is covered, but the negative branch is
deliberately a coarse presentation. The refined branch retains the Bernstein
confidence cube-root `T^(2/3)` limitation and Hoeffding/Azuma realized
deviation. Sharp active clipping, variance-sensitive mixed-square Freedman,
and ideal EXP3.P remain open.

## Compiled leaf: predictable-variance EXP3 regret with overflow residual

Lean statements:
`sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_delta`,
`sampledPredictableVarianceSquareHighProbabilityRegretBudget`, the raw and
total-delta joint regret theorems, and
`sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_total_delta`.
The primary endpoint proves
`P(regret>=budget(v,delta))<=ofReal(delta)+P(sum V>v)`.

Local APIs/imports: `Exp3MixedSquarePredictableVarianceTail`, the observed/
predictable square a.e. law, centered deviation identity, predictable mean
bound, sampled Hedge inequality, exploration bias, pure-cross and comparator
Bernstein tails, `measure_mono_ae`, `measure_union_le`, and
`ENNReal.ofReal_add`.

Proof route: transport the centered predictable-variance tail to the observed
mixed-square sum; assemble Hedge regret on the variance-good event; union the
square, pure-cross, and comparator failures; split the unconditional regret
event into variance-good and variance-overflow branches; normalize thirds.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
any horizon; positive variance budget and delta. No `delta<=1`, independence,
stationarity, countability, supplied integrability, deterministic variance
envelope, or new law transport.

Retrieval/status: predictable-variance tail/conditional-square rows,
deterministic Bernstein regret assembly, Mathlib measure/finite-sum/order/MGF
cards, Auer EXP3 card, inspiration-only potential/tail weapons;
`leanCompiled`, root imported, focused build, external primary canary.

Failure policy: the regret assembly gap is closed, but the theorem deliberately
exposes `P(sum V>v)` and is consumed by the realized route below. General
Freedman, anytime control, and ideal EXP3.P remain open.

## Compiled leaf: realized predictable-variance EXP3 regret with overflow residual

Lean statements:
`sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget`, the raw
joint and residual theorems, and the primary total-delta endpoints
`sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_joint_total_delta`
and
`sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_total_delta`.
They prove respectively
`P(realized regret>=budget(v,delta) and sum V<=v)<=ofReal(delta)` and
`P(realized regret>=budget(v,delta))<=ofReal(delta)+P(sum V>v)`.

Local APIs/imports: the predictable-variance regret route, realized-deviation
delta confidence, `sampledTrajectoryRealizedDeviationAt`, finite-sum
subtraction, real ring/order algebra, measure monotonicity and union bounds,
and `ENNReal.ofReal_add`.

Proof route: identify realized selected-loss regret as predictable
exploration-mixed regret plus cumulative realized deviation; union the
predictable joint event with the realized-deviation event; retain `sum V<=v`
on the predictable branch; split the unconditional event using strict
variance overflow; normalize four `delta/4` failures.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon, variance budget, and confidence allocations. No
`delta<=1`, independence, stationarity, countability, supplied integrability,
deterministic variance envelope, or new law transport.

Retrieval/status: predictable-variance regret, realized-deviation confidence,
comparable Bernstein realized assembly, Mathlib measure/finite-sum/order/
sub-Gaussian/MGF cards, Auer EXP3 card, inspiration-only potential/tail
weapons; `leanCompiled`, root imported, focused build, external primary
residual canary.

Failure policy: realized transport is closed while preserving the overflow
residual, and this row is consumed by the Markov route below. General Freedman,
anytime control, and ideal EXP3.P remain open.

## Compiled leaf: Markov-closed realized predictable-variance EXP3 regret

Lean statements: `sampledPredictableMixedSquaredVarianceSum`, its measurable
and nonnegative wrappers,
`sampledPredictableMixedSquaredVarianceLIntegral`,
`measure_sampledPredictableMixedSquaredVarianceSum_gt_le_lintegral_div`, the
raw lintegral consumer, the five-event budget, and
`sampledPredictable_predictableVarianceSquareRealizedMarkovHighProbabilityRegret_tail_total_delta`.
The generic tail is
`mu{sum V>v}<=lintegral(ofReal(sum V))/ofReal(v)`. Under
`lintegral(ofReal(sum V))<=ofReal(M)`, the primary endpoint sets
`v=M/(delta/5)` and proves
`P(realized regret>=budget(M,delta))<=ofReal(delta)`.

Local APIs/imports: the prior realized residual module, Mathlib Lebesgue
Markov, `meas_ge_le_lintegral_div`, finite-sum measurability,
`ENNReal.measurable_ofReal`, measure monotonicity, ENNReal division/order,
`ofReal_div_of_pos`, `div_div_cancel`, and `ofReal_add`.

Proof route: package cumulative V as a measurable nonnegative function; apply
Markov to its ENNReal lift; contain strict real overflow in the weak threshold
event; substitute the mean budget; consume the residual regret theorem; divide
failure across four confidence events and overflow.

Regularity contracts: arbitrary measure for the generic leaf; measurable
Env/Action and action singletons; decidable nonempty arms; `0<gamma<=1`;
predictable measurable `[0,1]` losses; positive threshold. The primary route
adds a probability prior, Standard Borel nonempty spaces, `eta>0`,
`0<gamma<1`, supported comparator, positive horizon, `M>0`, `delta>0`, and the
displayed lintegral contract. No `delta<=1`, independence, stationarity,
countability, separate integrability witness, deterministic envelope, or new
law transport.

Retrieval/status: prior predictable-variance realized row,
`MLIB-MEASURE-INTEGRAL`/Mathlib Markov, finite-sum/order cards, Auer EXP3 card,
inspiration-only tail and potential weapons; `leanCompiled`, root imported,
focused/root built, and externally canaried.

Failure policy: Markov closes the probability residual, and the loss-energy
row below discharges its abstract mean contract when a pathwise armwise
loss-square budget is available. Markov still yields the `M/delta` variance
threshold. Sharper scenario-specific loss energy or a stronger exponential/
self-normalized overflow theorem is needed for general Freedman, anytime
control, or ideal EXP3.P.

## Compiled leaf: loss-energy Markov realized predictable-variance EXP3 regret

Lean statements:
`sum_prob_mul_sq_mixedSquaredEstimatorDeviation_le_inv_floor_mul_sum_loss_sq`,
the centered-second-moment and generated-time wrappers,
`sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossSquaredSum`,
`sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossSquaredSum_le`, the
loss-energy budget definition, and
`sampledPredictable_predictableVarianceSquareLossEnergyRealizedMarkovHighProbabilityRegret_tail_total_delta`.
They prove
`sum V <= (1/(gamma/K))*sampledPredictableLossSquaredSum`; under a pathwise
budget `sampledPredictableLossSquaredSum<=L2`, the prior Markov route receives
mean budget `(1/(gamma/K))*L2` and closes realized selected-loss regret at total
failure `delta`.

Local APIs/imports: prior Markov realized route, existing predictable
loss-square sum, exact finite mixed-square first/second moments,
`FiniteActionDistribution.sum_eq_one`, generated probability and loss
regularity sources, finite-sum/order/ring arithmetic, `lintegral_mono`,
`ENNReal.ofReal_le_ofReal`, and probability-measure integration of constants.

Proof route: expand finite centered variance, use `loss^4<=loss^2`, apply the
positive probability floor termwise, discard the nonnegative squared mean,
transport to generated time, factor the horizon sum, integrate the pathwise
energy bound, and invoke the five-event Markov theorem.

Regularity contracts: positive probability floor and `[0,1]` losses for the
generic finite-law theorem. The primary route additionally requires a
probability prior, Standard Borel nonempty spaces, measurable action
singletons, decidable nonempty arms, `eta>0`, `0<gamma<1`, supported comparator,
positive horizon, `L2>0`, `delta>0`, and the pathwise loss-square energy bound.
No `delta<=1`, independence, stationarity, countability, separate
integrability, new law transport, or deterministic `K*T` premise.

Retrieval/status: prior Markov and predictable-variance rows, mixed-square
Bernstein confidence, Mathlib finite-sum/order/measure cards, Auer EXP3 card,
inspiration-only tail/potential weapons; `leanCompiled`, root imported,
focused/root built, and externally canaried.

Failure policy: the small-loss row below derives `L2<=L1` and replaces the
Hedge `K*T` mean upper bound by `L1`. Markov still costs `(L2/epsilon)/delta`; exponential/
self-normalized overflow, maximal/anytime control, general Freedman, and ideal
EXP3.P remain open.

## Compiled theorem: armwise small-loss predictable-variance EXP3 regret

Lean statements: `predictableLossAt_mem_unitInterval`,
`sampledPredictableLossMassSum`, the pointwise and cumulative `L2<=L1`
theorems, variance sum/lintegral wrappers, the L1 observed-square bridge,
`sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget`, its
predictable joint theorem, the realized budget/joint theorem, the five-event
Markov budget, and
`sampledPredictable_predictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegret_tail_total_delta`.

The primary theorem assumes a universal pathwise bound on
`L1=sum_t sum_a predictableLoss_t(a)`. Its Hedge square mean is `L2`, bounded
above by `L1` instead of `K*T`; its variance mean is bounded above by
`(1/(gamma/K))*L1`; and it chooses
`v=((1/(gamma/K))*L1)/(delta/5)`. Mixed-square, pure-cross, comparator,
realized-deviation, and overflow failures each receive `delta/5`.

Local APIs/imports: loss-energy route, predictable loss interval contracts,
finite sums and nonlinear order algebra, centered predictable-variance tail,
observed/predictable square transport, sampled Hedge, exploration bias,
pure-cross/comparator Bernstein tails, realized-deviation confidence,
variance lintegral, Mathlib Markov, measure unions, and ENNReal algebra.

Proof route: prove `l^2<=l`; sum to `L2<=L1`; use this both for the observed
mixed-square predictable mean and variance mean; rebuild predictable and
realized joint-event consumers; split unconditional regret into variance-good
and strict-overflow branches; normalize five equal allocations.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable `[0,1]` losses; supported comparator; positive
horizon, armwise `L1`, and delta; universal pathwise loss-mass bound. No
`delta<=1`, independence, stationarity, countability, supplied integrability,
new law transport, deterministic `K*T`, supplied `L2`, or supplied lintegral.

Retrieval/status: prior loss-energy and predictable/realized variance rows,
Mathlib finite-sum/order/measure cards, `SCN-ADVERSARIAL-FINITE`, Auer EXP3,
inspiration-only tail/potential weapons; `leanCompiled`, root imported,
focused/root built, and externally canaried.

Failure policy: the result is armwise aggregate small loss, not a standard
best-arm first-order regret theorem. Its generic pathwise `L1` input is
consumed by the sparse-loss theorem below. Eta/gamma are caller-selected and
Markov retains `1/delta`. L1-aware tuning, best-arm conversion, exponential/
self-normalized overflow, anytime control, general Freedman, and ideal EXP3.P
remain open.

## Compiled theorem: sparse-loss predictable-variance EXP3 regret

Lean statements: `sampledPredictableLossSupport` defines the active-arm
nonzero predictable-loss support;
`sampledPredictableLossMassAt_le_supportCard` bounds one-round loss mass by
its cardinality;
`sampledPredictableLossMassSum_le_sparsity_mul_horizon` derives
`L1<=(s:Real)*T` from a uniform natural support cap; the sparse realized budget
specializes the small-loss budget; and
`sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta`
proves the generated realized selected-loss tail at `ofReal(delta)`.

Local APIs/imports: the compiled small-loss total-delta theorem,
`sampledPredictableLossMassSum`, predictable unit-interval loss regularity,
`Finset.filter`, `Finset.filter_subset`, `Finset.sum_subset`,
`Finset.sum_le_sum`, range membership, natural-to-real order casts, and
finite-sum/order algebra.

Proof route: filter each round to nonzero loss coordinates; remove zero terms
from the full arm sum; bound every retained loss by one; sum the pathwise
support cap over the finite horizon; establish positivity of `s*T`; instantiate
the small-loss theorem with `lossMassBudget=s*T`.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable action singletons; decidable nonempty arms; positive eta; gamma in
`(0,1)`; predictable measurable `[0,1]` losses; supported comparator; positive
horizon, natural sparsity, and delta; uniform pathwise support-cardinality cap
for all generated samples and `t<horizon`. No `s<=K`, `delta<=1`,
independence, stationarity, countability, separate integrability, new law
transport, supplied `L1`/`L2`/lintegral premise, or deterministic `K*T`
premise is required.

Retrieval/status: compiled small-loss route, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`, Auer EXP3, inspiration-only
tail/potential weapons; `leanCompiled`, root imported, focused/root built, and
externally canaried.

Failure policy: this discharges the abstract `L1` input only under universal
pathwise support sparsity. It remains armwise aggregate rather than best-arm
first order; eta is selected by the tuning theorem below, gamma remains
caller-selected, and Markov retains `1/delta`. Probabilistic sparsity,
best-arm conversion, exponential/self-normalized overflow, anytime control,
general Freedman, and ideal EXP3.P remain open.

## Compiled theorem: eta-tuned sparse-loss predictable-variance EXP3 regret

Lean statements: `sparseLossPredictableVarianceBudget` names
`v=((1/(gamma/K))*s*T)/(delta/5)`; the scale definition adds `s*T` to the
predictable-variance radius at `(v,delta/5)`; the learning-rate definition sets
`eta=sqrt(log K/scale)`; positivity and square-balance lemmas establish the
regularity needed by the sparse theorem; the Hedge lemma bounds entropy plus
stability by `3*sqrt(log K*scale)`; the threshold and budget-comparison theorem
retain the remaining confidence terms; and
`sampledPredictable_tunedSparseLossPredictableVarianceRealizedMarkovRegret_tail`
proves the final generated tail.

Local APIs/imports: compiled sparse-loss budget and total-delta theorem,
predictable-variance radius, real log/sqrt positivity and square identities,
finite-cardinality casts, field/ring normalization, nonlinear/linear
arithmetic, and event monotonicity.

Proof route: prove positivity of `v`, the radius components, complete scale,
and eta; prove `eta^2*scale=log K`; rewrite entropy as `eta*scale`; use
`gamma<=1/2` to control the stability factor; identify entropy with the
balanced square root; unfold and compare complete budgets; tighten the final
bad event and consume the sparse total-delta theorem.

Regularity contracts: probability prior; Standard Borel nonempty Env/Action;
measurable singletons; decidable arms with `K>=2`; `0<gamma<=1/2`;
predictable `[0,1]` losses; supported comparator; positive horizon, natural
sparsity, and delta; universal pathwise support cap. Eta is internal. No eta
premise, `s<=K`, `delta<=1`, independence, stationarity, countability,
separate integrability, new law transport, supplied `L1`/`L2`/lintegral, or
deterministic `K*T`.

Retrieval/status: sparse-loss total-delta route, exponential/Bernstein square
tuning templates, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
`MLIB-FINSET-SUMS`, `SCN-ADVERSARIAL-FINITE`, Auer EXP3, inspiration-only
tail/potential weapons; `leanCompiled`, root imported, focused/root built, and
externally canaried.

Failure policy: exact-scale eta tuning is closed and consumed by the explicit
gamma theorem below. Support sparsity remains universal pathwise, the loss
notion remains armwise aggregate, and Markov retains `1/delta`.
Probabilistic sparsity, best-arm conversion, exponential/self-normalized
overflow, anytime control, general Freedman, and ideal EXP3.P remain open.

## Compiled theorem: explicit sparse-loss predictable-variance EXP3 tuning

Lean statements: exact `log(1/(delta/5))` and Markov-budget normalizations;
log-weighted radius and balanced-root bounds; the `14*gamma*T` characterized
threshold/tail; four explicit exploration components and their clipped
maximum; reusable fifth-root upper-bound and dominance lemmas; clipping
inactivity/contracts; and
`sampledPredictable_explicitSparseLossPredictableVarianceRealizedMarkovRegret_tail`.

Local APIs/imports: eta-tuned sparse route, explicit exponential/Bernstein
tuning templates, `Real.rpow_inv_natCast_pow`, square-root and power-order
APIs, max/min lemmas, generic Bernstein and realized-radius dominance,
finite casts, field/ring normalization, arithmetic tactics, and event
monotonicity.

Proof route: write `B=log(5/delta)` and
`v=5*K*s*T/(gamma*delta)`; square the mixed Markov radius and use the
fifth-power contract; use the cubic confidence contract and sparse base
contract for the linear term; derive the `14` threshold; define gamma as the
clipped maximum of square/fifth/cube/square roots; prove the four components
are at most one half under constants `4,32,8,8`; recover all dominance
contracts and invoke the characterized tail.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; predictable `[0,1]` losses;
supported comparator; positive horizon and sparsity; `0<delta<=1`; four
large-horizon inequalities; universal pathwise support cap. Eta and gamma are
internal; no `s<=K`, independence, stationarity, countability, supplied
integrability, law transport, `L1`/`L2`/lintegral, or `K*T` premise.

Retrieval/status: sparse eta-tuned route, exponential and Bernstein explicit
templates, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
`MLIB-FINSET-SUMS`, finite adversarial scenario, Auer EXP3, inspiration-only
tail/potential weapons; `leanCompiled`, root imported, focused/root built, and
external final theorem canary.

Failure policy: explicit large-horizon eta/gamma tuning is closed and consumed
by the all-horizon theorem below. Markov leaves a fifth-root polynomial
`1/delta` term, while the result remains armwise aggregate with universal
pathwise sparsity. Best-arm conversion, probabilistic sparsity, stronger
overflow, general Freedman, anytime control, sharper constants, and ideal
EXP3.P remain open.

## Compiled theorem: all-horizon sparse-loss predictable-variance EXP3

Lean statements:
`sparseLossPredictableVarianceLargeHorizonCondition`,
`sparseLossPredictableVarianceAllHorizonRegretThreshold`, and
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail`.

Local APIs/imports: explicit sparse-loss tuning, generic Bernstein
all-horizon fallback, explicit and trivial tail theorems, generated
realized-regret pathwise bound, classical branching, clipped-rate
positivity/stability, finite sums, order, and measure-zero APIs.

Proof route: package the four large-horizon inequalities; branch the threshold
between the explicit `14*gamma*T` expression and `(T:Real)+1`; invoke the
explicit theorem in the positive branch; instantiate the strict
zero-probability fallback with the same eta and gamma in the negative branch.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; predictable `[0,1]` losses;
supported comparator; positive horizon/sparsity; `0<delta<=1`; universal
pathwise support cap. Eta/gamma are internal, and no large-horizon proof,
`s<=K`, independence, stationarity, countability, supplied integrability,
law transport, or `L1`/`L2`/lintegral premise is required.

Retrieval/status: explicit sparse route, generic Bernstein and exponential
all-horizon templates, measure/integral, finite-sum, and order cards,
adversarial finite scenario, Auer EXP3, inspiration-only weapons;
`leanCompiled`, root imported, focused/root built, external final theorem
canary.

Failure policy: all positive horizons are covered, but the negative branch is
the coarse `T+1` fallback. The refined branch retains polynomial `1/delta`,
universal pathwise sparsity, armwise aggregate loss, constant `14`, and
bounded realized deviation. Sharp active clipping, best-arm conversion,
probabilistic sparsity, stronger overflow, general Freedman, anytime control,
and ideal EXP3.P remain open.

## Compiled theorem: all-horizon a.e.-sparse predictable-variance EXP3

Lean statement:
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_ae_sparsity`.

Local APIs/imports: the pathwise sparse all-horizon module; generalized a.e.
loss-mass lintegral and observed-square consumers; the sample-local
`L1<=S*T` support lemma; the raw a.e.-sparse total-delta theorem; clipped-rate
contracts; raw-to-tuned and tuned-to-explicit comparisons; strict `T+1`
fallback; `filter_upwards`, `lintegral_mono_ae`, `measure_mono`, finite sums,
and order APIs.

Proof route: require one common a.e. support-cap event under the exact
internally tuned generated measure; transport it to an a.e. loss-mass budget;
use that budget in both the observed-square bridge and Markov variance
lintegral; in the four-contract branch contain the explicit threshold event in
the raw-budget event; otherwise use the zero-probability fallback. No new
failure event is unioned.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; predictable `[0,1]` losses;
supported comparator; positive horizon/sparsity; `0<delta<=1`; and a.e.
support sparsity under the exact generated measure. There is no universal
pathwise cap, extra sparsity failure allocation, caller regime proof,
eta/gamma, `S<=K`, independence, stationarity, countability, or supplied
integrability.

Retrieval/status: pathwise all-horizon, sparse base, and small-loss rows;
measure/integral, finite-sum, and order cards; adversarial finite scenario;
Auer EXP3; inspiration-only weapons; `leanCompiled`, root imported,
focused-built, external theorem canary.

Failure policy: null exceptional paths are closed without spending delta.
Positive-probability sparsity violations, best-arm conversion, stronger
overflow, general Freedman, anytime control, sharp active clipping, and ideal
EXP3.P remain open; the current refined branch still has Markov polynomial
`1/delta` and armwise aggregate loss.

## Compiled theorem: positive-probability sparse predictable-variance EXP3

Lean statements: `sampledPredictableSparsityFailure` records trajectories with
some support cardinality above `S`;
`sampledPredictableLossMassSum_le_or_mem_sparsityFailure` gives
`L1<=S*T` or event membership;
`sampledPredictableMixedSquaredVarianceLIntegral_le_globalLossMass` derives the
unconditional variance mean `(1/(gamma/K))*(K*T)`; the residual theorem proves
failure `ofReal(delta)+mu(sparsityFailure)`; and
`sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail_of_sparsityFailure_le`
exposes the practical `ofReal(delta)+ofReal(epsilon)` endpoint.

Local APIs/imports: sparse-base support lemmas; explicit-bad-set observed-
square, predictable-joint, and realized-joint small-loss consumers;
`Filter.Eventually.of_forall`; filter/cardinality APIs; variance lintegral;
Markov overflow; measure unions; ENNReal division/addition; finite sums and
order algebra.

Proof route: split each generated sample into `L1<=S*T` or the exact failure
event; preserve `S*T` in the observed-square/Hedge route; use the global
`support.card<=K` bound to close the unconditional variance lintegral; union
Markov overflow as the fifth ordinary event; normalize five `delta/5` terms;
then add the sparsity-failure measure and consume its epsilon bound.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`;
predictable `[0,1]` losses; supported comparator; positive horizon and delta;
natural sparsity; and the exact generated-measure failure bound for the
epsilon consumer. No universal/a.e. support cap, `S>0`, `S<=K`,
`epsilon>=0`, `delta<=1`, independence, stationarity, countability, supplied
integrability, or event measurability premise.

Retrieval/status: a.e.-sparse, sparse-base, and small-loss rows; Mathlib
measure/integral, finite-sum, and order cards; adversarial finite scenario;
Auer EXP3; inspiration-only tail/potential weapons; `leanCompiled`, root
imported, focused/root built, and externally canaried.

Failure policy: positive-probability sparsity is closed only at the caller
eta/gamma threshold with the global `K*T` Markov envelope. Do not transport
the old tuned `14*gamma*T` claim to this theorem. Polynomial `1/delta`,
armwise aggregate loss, best-arm conversion, stronger overflow, general
Freedman, anytime control, and ideal EXP3.P remain open.

## Compiled theorem: pathwise sparse variance with positive-probability failure

Lean statements:
`sampledPredictableSparsePathwiseVarianceBudget` names
`(1/(gamma/K))*(S*T)`;
`sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure`
gives the pointwise variance-or-bad split; the three small-loss
`_tail_*_off_bad_of_lossMassSum_le_or_mem` declarations remove the bad set
from observed, predictable, and realized joint source events; and the final
residual/epsilon theorems expose generated regret failure
`delta+mu(sparsityFailure)` and `delta+epsilon`.

Local APIs/imports: probabilistic-sparsity definitions; small-loss pointwise
variance and off-bad tails; finite sums/casts; `Set.diff`/intersection/union;
eventually-of-forall; measure monotonicity and union; ENNReal addition.

Proof route: derive `sum V<=(K/gamma)*S*T` whenever the loss-mass side of the
sparse-or-bad split holds; apply four confidence events at `delta/4` to the
regret-and-variance-good event outside `bad`; contain every regret-bad sample
in that event or `bad`; charge the failure event once.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`;
predictable `[0,1]` losses; supported comparator; positive horizon, sparsity,
and delta; exact generated-measure failure bound for epsilon. No
event-measurability, restricted-measure, Markov, universal/a.e. sparsity,
`S<=K`, epsilon positivity, or `delta<=1` premise.

Retrieval/status: probabilistic Markov, small-loss, and sparse-base rows;
measure/integral, finite-sum, order, adversarial finite, and Auer EXP3 cards;
inspiration-only tail/potential weapons; `leanCompiled`, root imported,
focused/root built, external `delta+epsilon` canary.

Failure policy: caller eta/gamma now avoid global `K*T`, `K^2`, and Markov
`1/delta`. Eta tuning and the large-horizon explicit-gamma consumer are
migrated below; the all-horizon consumer still uses the old five-event budget
and must be migrated next.
Best-arm conversion, armwise-to-first-order conversion, general Freedman,
anytime control, and ideal EXP3.P remain open.

## Compiled theorem: eta-tuned pathwise variance with probabilistic sparsity

Lean statements:
`pathwiseVarianceProbabilisticSparseLossHighProbabilityScale` is
`S*T+predictableVarianceRadius((1/(gamma/K))*S*T,delta/4)`; the learning-rate
definition sets `eta=sqrt(log K/scale)`; positivity, square-balance, and
three-copy Hedge lemmas close the tuning algebra; the budget-comparison theorem
contains the tuned bad event in the raw event; and the final residual/epsilon
theorems expose the generated tail under the exact internal eta.

Local APIs/imports: pathwise-variance probabilistic-sparsity raw theorem;
sparse variance budget and predictable-variance radius; real log/sqrt;
finite casts; field/ring/nonlinear arithmetic; measure monotonicity; ENNReal
addition.

Proof route: prove the four-event scale positive; establish
`eta^2*scale=log K`; control stability using `gamma<=1/2`; unfold matching
`delta/4` raw and tuned budgets; use event monotonicity under the same
generated measure; consume the exact failure-event bound.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; `0<gamma<=1/2`;
predictable `[0,1]` losses; supported comparator; positive horizon, sparsity,
and delta; exact internally eta-tuned failure bound. No caller eta, global
`K*T`, Markov, event measurability, restricted measure, universal/a.e. cap,
`S<=K`, epsilon positivity, or `delta<=1`.

Retrieval/status: pathwise-variance base and prior tuning-template rows;
real-log/sqrt, measure/integral, finite-sum, order, adversarial finite, Auer
EXP3 cards; inspiration-only weapons; `leanCompiled`, root imported,
focused/root built, external eta-tuned practical canary.

Failure policy: eta no longer carries the old K-squared Markov scale. The
explicit schedule below now consumes this theorem; all-horizon migration
remains next. Armwise aggregate loss, bounded realized deviation, best-arm
conversion, Freedman, anytime control, and ideal EXP3.P remain open.

## Compiled theorem: explicit gamma for probabilistic sparse pathwise variance

Lean statements:
`sampledPredictableSparsePathwiseVarianceBudget_eq` rewrites the good-path
budget as `K*S*T/gamma`; the log-radius and balanced-root lemmas close the
characterized `14*gamma*T` threshold; the clipped-rate definitions and
contract theorem select gamma; and the final explicit residual/epsilon
theorems expose generated regret failure `delta+mu(bad)` and
`delta+epsilon`.

Local APIs/imports: pathwise eta tuning and sparse variance; predictable
variance radius; fourth-budget log identity; Bernstein/realized radius
dominance; sparse arm, random-square confidence, and realized scales; reusable
fifth/cube/square root algebra; real log/sqrt/rpow; finite casts; field/ring
and nonlinear arithmetic; measure monotonicity; ENNReal addition.

Proof route: use the mixed numerator
`K*S*(log K)^2*log(4/delta)` rather than the Markov
`K^2*log(K)^2*log(5/delta)/delta`; derive the radius and balanced-root bounds;
compare to `14*gamma*T`; prove a four-component clipped maximum is positive,
at most one half, and dominant under four horizon contracts; instantiate the
eta-tuned theorem under one internal measure.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; predictable `[0,1]`
losses; supported comparator; positive horizon/sparsity; `0<delta<=1`; four
large-horizon inequalities for arm, mixed fifth-root, Bernstein cube-root,
and realized square-root scales; exact internally eta/gamma-tuned failure
bound for epsilon. Eta/gamma are internal. No Markov, global `K*T`, `K^2`
mixed numerator, polynomial `1/delta`, event measurability, restricted
measure, universal/a.e. cap, `S<=K`, or epsilon positivity.

Retrieval/status: pathwise eta-tuning and old reusable explicit-algebra rows;
real-log/sqrt/rpow, measure/integral, finite-sum, order, adversarial finite,
and Auer EXP3 cards; inspiration-only weapons; `leanCompiled`, root imported,
focused/root and `Tests.Basic` built, external explicit practical canary,
consumed by the all-horizon route.

Failure policy: the large-horizon explicit branch is closed without the old
Markov scale and strict `T+1` now handles the complementary regime
downstream. Armwise aggregate loss, bounded realized deviation, best-arm
conversion, Freedman, anytime control, sharp clipping, and ideal EXP3.P
remain open.

## Compiled theorem: all-horizon probabilistic sparse pathwise variance

Lean statements:
`pathwiseVarianceProbabilisticSparseLossLargeHorizonCondition` packages the
four explicit schedule contracts;
`pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold` selects the
refined threshold or strict `T+1`; the generated off-bad theorem gives
`delta`; the residual theorem gives `delta+mu(bad)`; and the practical theorem
gives `delta+epsilon` for every positive horizon.

Local APIs/imports: raw through explicit off-bad pathwise chain; generic
Bernstein all-horizon fallback; clipped exploration positivity and stability;
`sampledPredictable_trivialRealizedRegret_tail`; classical `if`/`by_cases`;
set-difference monotonicity; ENNReal addition; generated regret and
sparsity-failure events.

Proof route: branch on the exact four-contract condition; invoke the explicit
pathwise off-bad theorem in the refined branch; rewrite to `T+1` and contain
the off-bad event in the strict event under the identical
eta/gamma/generated measure in the complementary branch; add bad once for the
residual and consume epsilon.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable `K>=2` arms; predictable `[0,1]` losses;
supported comparator; positive horizon/sparsity; `0<delta<=1`; exact
internally tuned bad-event bound. Eta, gamma, and regime selection are
internal. No caller horizon inequalities, global `K*T`, Markov, `K^2` mixed
numerator, polynomial `1/delta`, event measurability, restricted measure,
universal/a.e. cap, `S<=K`, epsilon positivity, independence, stationarity,
countability, supplied integrability, or law transport.

Retrieval/status: pathwise explicit-gamma and generic all-horizon rows;
measure/integral, finite-sum, order, adversarial finite, and Auer EXP3 cards;
inspiration-only weapons; `leanCompiled`, root imported, focused/root and
`Tests.Basic` built, external practical all-horizon canary; consumed by the
finite best-arm single-charge theorem below.

Failure policy: every positive horizon is covered without the old Markov
scale, but the fallback threshold remains coarse `T+1`. Armwise aggregate
loss, bounded realized deviation, sharp clipping, Freedman, anytime control,
and ideal EXP3.P remain open.

## Compiled theorem: finite best-arm all-horizon probabilistic sparse pathwise variance

Lean statements: `sampledPredictableBestArmCumulativeLoss` is the
`Finset.inf'` of cumulative predictable loss over the nonempty supported-arm
set; the event-equivalence theorem identifies regret against this value with
the existential finite union of fixed-comparator events. At confidence share
`delta/K`, the best-arm off-bad theorem gives `ofReal(delta)` after removing
the common `sampledPredictableSparsityFailure`; the strengthened residual
gives `ofReal(delta)+mu(sampledPredictableSparsityFailure)`; and the practical
single-charge theorem gives `ofReal(delta)+ofReal(epsilon)` under the exact
same-measure bound
`mu(sampledPredictableSparsityFailure)<=ofReal(epsilon)`. Older K-charge
wrappers remain available for compatibility.

Local APIs/imports: raw, eta-tuned, gamma-characterized, explicit, and
all-horizon fixed-comparator off-bad theorems; `Finset.inf'_le_iff` and
`Finset.inf'_le`; `Set.diff`; finite iUnions; `measure_biUnion_finset_le`,
`measure_mono`, and `measure_union_le`; finite sum comparison; ENNReal
`ofReal` division and multiplication cancellation; finite casts; order
algebra.

Proof route: rewrite the best-loss threshold event to a supported comparator
witness; establish `0<delta/K<=1`; instantiate the same internally selected
eta/gamma and generated measure for every comparator; distribute removal of
the common bad set through the finite comparator union; apply the finite-union
measure inequality only to off-bad events; normalize
`K*ofReal(delta/K)=ofReal(delta)`; then cover the full event by its off-bad
part union the common bad set and charge that set once.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; predictable measurable
`[0,1]` losses; positive horizon and sparsity; `0<delta<=1`; calibrated exact
same-measure failure bound. Eta, gamma, best-arm infimum, and regime selection
are internal. No caller comparator, caller horizon contracts, epsilon/K
calibration, global `K*T`, Markov, `K^2`, polynomial `1/delta`, event
measurability, restricted measure, universal/a.e. cap, `S<=K`, epsilon
positivity, independence, stationarity, countability, supplied integrability,
or law transport.

Retrieval/status: fixed-comparator off-bad pathwise all-horizon chain;
`MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
adversarial finite/Auer EXP3, and inspiration-only tail/potential weapons;
`leanCompiled`, root imported, focused/root and `Tests.Basic` built, external
single-charge practical best-arm canary.

Failure policy: this closes the finite hindsight best-supported-arm gap, not a
stochastic-mean or first-order best-arm theorem. Single charging of the common
bad event is closed; delta/K retains the expected logarithmic arm-count cost,
and the fallback remains coarse `T+1`. Sharp active clipping, general
Freedman, anytime control, and ideal EXP3.P remain open.

## Compiled theorem: eta-tuned positive-probability sparse EXP3

Lean statements:
`probabilisticSparseLossPredictableVarianceBudget` names
`v=((1/(gamma/K))*(K*T))/(delta/5)`;
`probabilisticSparseLossPredictableVarianceHighProbabilityScale` adds `S*T`
to the predictable-variance radius at `(v,delta/5)`; the learning-rate
definition sets `eta=sqrt(log K/scale)`; positivity and square-balance lemmas
establish the exact regularity; the Hedge lemma bounds entropy plus stability
by `3*sqrt(log K*scale)`; the budget-comparison theorem contains the raw event
in the tuned event; and the final residual/epsilon theorems expose the
generated regret tail.

Local APIs/imports: probabilistic-sparsity residual module; global variance
mean and radius; raw generated tail; real log/sqrt identities; finite casts;
field/ring normalization; nonlinear/linear arithmetic; measure monotonicity;
ENNReal addition.

Proof route: prove the global Markov threshold and complete scale are positive;
prove `eta^2*scale=log K`; rewrite entropy as `eta*scale`; use
`gamma<=1/2` to bound stability; compare the complete raw and tuned budgets;
tighten the bad-regret event under the same internally eta-tuned generated
measure; consume the exact sparsity-failure epsilon bound.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable arms with `K>=2`; `0<gamma<=1/2`;
predictable `[0,1]` losses; supported comparator; positive horizon, sparsity,
and delta; exact internally tuned generated-measure failure bound for the
epsilon consumer. Eta is internal. No caller eta, universal/a.e. support cap,
`S<=K`, epsilon positivity, `delta<=1`, independence, stationarity,
countability, integrability, event measurability, or new law transport.

Retrieval/status: probabilistic-sparsity residual and pathwise eta-tuning rows;
real-log/sqrt, measure/integral, finite-sum and order cards; adversarial finite
scenario; Auer EXP3; inspiration-only weapons; `leanCompiled`, root imported,
focused/root built, and externally canaried.

Failure policy: eta is closed against the honest global `K*T` Markov scale
and is consumed by the explicit-gamma theorem below. Polynomial `1/delta`,
all-horizon fallback, sharper overflow, best-arm conversion, Freedman, anytime
control, and ideal EXP3.P remain open.

## Compiled theorem: explicit positive-probability sparse EXP3 tuning

Lean statements: `probabilisticSparseLossPredictableVarianceBudget_eq`
identifies the global Markov threshold with
`5*K^2*T/(gamma*delta)`; the log-radius and balanced-square-root lemmas reduce
the eta-tuned threshold to `14*gamma*T`; the new Markov exploration component
is `(5*K^2*log(K)^2*log(5/delta)/(delta*T^3))^(1/5)`; raw/clipped schedule
lemmas recover all four dominance contracts; and the final residual/practical
theorems expose `delta+mu(bad)` and `delta+epsilon` under the fully internal
eta/gamma schedule.

Local APIs/imports: probabilistic eta-tuning; pathwise explicit-tuning
root/power helpers; global variance budget and mixed-square radius; Bernstein
and realized radius bounds; real log/sqrt/rpow; finite casts; field/ring and
nonlinear arithmetic; measure monotonicity; ENNReal addition.

Proof route: compute the global `K^2` budget; use fifth-power and confidence
contracts to control the mixed-square radius; balance the sparse base and
radius; compare the tuned threshold to `14*gamma*T`; define gamma as a clipped
four-way maximum; prove clipping inactive from four horizon inequalities;
extract the characterized contracts; preserve the exact generated measure
while consuming the sparsity-failure epsilon bound.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable `K>=2` arms; predictable `[0,1]` losses;
supported comparator; positive horizon/sparsity; `0<delta<=1`; four explicit
large-horizon inequalities; exact internally tuned generated-measure bad-event
bound for the epsilon endpoint. Eta/gamma internal. No universal/a.e. support
cap, `S<=K`, epsilon positivity, independence, stationarity, countability,
integrability, event measurability, or new law transport.

Retrieval/status: probabilistic eta-tuning and pathwise explicit-gamma rows;
real-log/sqrt, exp/log/rpow, measure/integral, finite-sum and order cards;
adversarial finite scenario; Auer EXP3; inspiration-only weapons;
`leanCompiled`, root imported, focused/root built, externally canaried.

Failure policy: explicit eta/gamma tuning is closed in the large-horizon
regime and is consumed by the all-horizon theorem below. The global envelope
retains `K^2`, polynomial `1/delta`, and armwise aggregate loss. Pathwise
sparse variance, stronger overflow, best-arm conversion, Freedman, anytime
control, and ideal EXP3.P remain open.

## Compiled theorem: all-horizon positive-probability sparse EXP3

Lean statements:
`probabilisticSparseLossPredictableVarianceLargeHorizonCondition` packages
the four explicit inequalities;
`probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold` selects
the explicit `14*gamma*T` threshold or strict `T+1`; the residual theorem
returns `delta+mu(bad)`; and the practical theorem returns `delta+epsilon`
under the exact same-measure bad-event premise.

Local APIs/imports: probabilistic explicit tuning; generic Bernstein
all-horizon fallback; clipped gamma positivity and upper bound; trivial
realized-regret tail; classical condition splitting; ENNReal addition order;
generated regret and support-failure events.

Proof route: split on the named four-contract regime; invoke the explicit
residual theorem in the true branch; rewrite the threshold to `T+1` and use
the strict zero-probability theorem in the false branch; weaken the latter to
`delta+mu(bad)`; consume epsilon without changing eta, gamma, or the measure.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable `K>=2` arms; predictable `[0,1]` losses;
supported comparator; positive horizon/sparsity; `0<delta<=1`; exact internal
generated-measure failure bound for epsilon. Eta/gamma/regime internal. No
universal/a.e. cap, caller horizon inequalities, `S<=K`, epsilon positivity,
independence, stationarity, countability, integrability, event measurability,
or law transport.

Retrieval/status: probabilistic explicit-gamma, pathwise sparse all-horizon,
and generic Bernstein all-horizon rows; measure/integral, finite-sum, order,
adversarial finite, and Auer EXP3 cards; inspiration-only weapons;
`leanCompiled`, root imported, focused/root built, externally canaried.

Failure policy: all positive horizons are covered, but the fallback is coarse
`T+1`. The refined branch retains `K^2`, polynomial `1/delta`, armwise
aggregate loss, and bounded realized deviation. Sharp clipping, pathwise
sparse variance, stronger overflow, best-arm conversion, Freedman, anytime
control, and ideal EXP3.P remain open.

## Compiled theorem: finite best-arm Bernstein-square all horizon

Lean statements: `sampledPredictableBestArmCumulativeLoss` and its event
equivalence now live in shared `Exp3BestArm`;
`bernsteinSquareBestArmAllHorizonRegretThreshold` calibrates the fixed
schedule at `delta/K`; and
`sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail`
bounds the resulting generated best-arm event by `ENNReal.ofReal delta`.

Local APIs/imports: shared finite best-arm transport; fixed-comparator
Bernstein-square all-horizon tail; finite unions and sums;
`measure_biUnion_finset_le`; ENNReal `ofReal` division and cancellation;
finite casts; omega and order algebra.

Proof route: show `0<delta/K<=1`; instantiate the comparator tail under one
common eta/gamma/generated measure; rewrite the `Finset.inf'` best-arm event
as the finite comparator union; union-bound; normalize
`K*ofReal(delta/K)=ofReal(delta)`.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable singletons; decidable `K>=2` arms; predictable `[0,1]` losses;
positive horizon; `0<delta<=1`. Comparator, eta, gamma, best-arm infimum, and
regime branch are internal. No sparsity, caller horizon inequalities,
independence, stationarity, countability, integrability, event measurability,
or new law transport.

Retrieval/status: fixed-comparator Bernstein all-horizon row; prior sparse
pathwise best-arm union; Mathlib finite-sum, measure, and order cards;
adversarial finite scenario; Auer EXP3; inspiration-only tail/potential
weapons; `leanCompiled`, root imported, focused/root and `Tests.Basic` built,
externally canaried.

Failure policy: finite hindsight best-arm conversion is closed for this route.
The `delta/K` schedule retains the expected log-K cost and the fallback remains
coarse `T+1`. Bounded realized deviation, deterministic fixed-tilt variance,
sharp clipping, random quadratic variation, general Freedman, anytime,
stochastic-mean/first-order regret, and ideal EXP3.P remain open.

## Compiled theorem: sparse EXP3 with double pathwise variance

Lean statements: `selectedLossCenteredSecondMoment` and its compensated
finite-action/conditional MGF route;
`sampledPredictableRealizedDeviation_sum_tail_predictableVariance_delta`;
`sampledPredictable_doublePredictableVarianceRealizedHighProbabilityRegret_tail_joint`;
the small-loss double-variance off-bad joint assembler; the sparse
realized-variance budget-or-failure theorem; and off-bad, residual,
eta-tuned, and `delta+epsilon` sparse regret endpoints.

Local APIs/imports: generated conditional action laws; `condDistrib`;
`condExpKernel`; finite-action measure maps; measurable history freezing;
deterministic-feedback AE transport; predictable and strongly adapted
processes; fixed-MGF finite-sum tail assembly; the small-loss predictable
regret joint tail; the existing pathwise sparse learning-rate scale and
square-root optimizer; support-sparsity loss-mass alternatives; finite sums,
set difference/intersection/union, measure monotonicity/union, and ENNReal
quarter normalization. The explicit consumer additionally reuses the sparse
arm square-root, pathwise mixed fifth-root, and Bernstein confidence
cube-root scales; min/max order; real rpow; square/fifth/cube dominance
helpers; and the exact selected-loss predictable-variance radius.

Proof route: center a bounded selected loss under the finite action law;
prove and compensate its exact second-moment MGF; transport through the
conditional law; iterate across the generated filtration; optimize the tilt;
decompose realized regret; require mixed variance at most
`(1/(gamma/K))*S*T` and realized variance at most `S*T`; prove each budget or
the same sparsity-failure event; restrict the predictable three-event branch
and the outer joint regret event by the bad-set complement while keeping the
realized-deviation tail global; then add the common bad set back once. The
corrected raw assembler uses loss-mass budget `S*T` instead of `K*T`. Eta is
then chosen as `sqrt(log K/scale)`, where `scale=S*T+mixedRadius`, and the
exact realized radius is retained additively. Explicit gamma tuning augments
the previous sparse pathwise raw schedule by
`sqrt(S*log(4/delta)/T)`, clips at `1/2`, and proves the tuned threshold is at
most `16*gamma*T`. The all-horizon wrapper packages the same four contracts,
uses that exact explicit threshold when they hold, and uses the generic strict
`T+1` zero-probability tail otherwise. Both branches keep the identical
internal eta, gamma, and generated measure. Its off-bad theorem removes the
common sparsity-failure set, the residual adds it once, and the practical
endpoint consumes the same-measure epsilon bound.

Regularity contracts: probability prior; Standard Borel nonempty spaces;
measurable action singletons; decidable `K>=2` arms for the tuned theorem;
`0<gamma<=1/2`; positive horizon, sparsity, and delta; predictable jointly
measurable pointwise `[0,1]` losses; supported comparator; exact same-measure
bad-event bound only for the epsilon endpoint. Eta is internal in the tuned
theorem. The generic conditional wrapper states
joint loss measurability and global `[0,1]` explicitly. No event
measurability, universal/a.e. sparsity, `S<=K`, epsilon positivity,
`delta<=1`, independence, stationarity, countability, supplied integrability,
restricted measure, Markov step, or extra reward law.

The explicit schedule assumes `0<delta<=1` and four large-horizon contracts:
`4*S*log K<=T`,
`32*K*S*log(K)^2*log(4/delta)<=T^3`,
`8*K*log(4/delta)<=T`, and
`4*S*log(4/delta)<=T`. Eta and gamma are internal there. No `S<=K`,
epsilon positivity, event measurability, Markov step, fixed Hoeffding proxy,
or new law transport is added.

Retrieval/status: compiled sparse pathwise row and predictable-variance tail;
Mathlib probability-kernel, measure/integral, finite-sum, and order cards;
adversarial finite scenario; Auer EXP3; inspiration-only tail/potential
weapons; `leanCompiled`, root imported, focused/root built, externally
canaried at tuned and explicit off-bad, residual, and practical theorem
surfaces. The all-horizon off-bad, residual, and practical surfaces are also
root imported, focused/`Tests.Basic` built, and externally canaried. The exact
best-arm module applies those off-bad tails at `delta/K`, rewrites the
`Finset.inf'` best-arm event as a finite comparator union, normalizes total
confidence to `delta`, and adds the common sparsity-failure event once. Its
off-bad and unscaled-epsilon practical endpoints are externally canaried.

Failure policy and next leaf: eta tuning and explicit large-horizon gamma
tuning for the fixed-comparator exact double-variance threshold are closed,
and the all-horizon wrapper covers every positive horizon without a caller
regime proof. Finite hindsight best-supported-arm transport and single
common-bad charging are also closed. The `delta/K` schedule retains log-K cost
and the fallback remains deliberately coarse strict `T+1`. Do not label this
as general Freedman, anytime, first-order, stochastic-mean, sharp clipping,
or ideal EXP3.P.

## Compiled leaf: predictable-compensator fixed-tilt tail

Lean statement:
`Concentration.measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`
proves
`mu{threshold <= sum Y and sum V <= varianceBudget} <=
ofReal(exp(-tilt*threshold + varianceCoeff*varianceBudget))` when the
compensated process `tilt*Y_i - varianceCoeff*V_i` is strongly adapted and
has a unit-tilt zero-budget initial MGF witness plus successor conditional MGF
witnesses. The existing EXP3 realized predictable-variance fixed-tilt theorem
now consumes it with `varianceCoeff=tilt^2`.

Local APIs/imports and route: `ConcentrationFixedMGF`,
`HasMGFUpperBoundAt`, `HasCondMGFUpperBoundAt`, `StronglyAdapted`,
`measure_sum_ge_le_of_hasCondMGFUpperBoundAt`, `Measure.real`, ENNReal
conversion, finite range sums, and `measure_mono`. Apply the fixed-tilt sum
theorem to the compensated increments, convert its real measure bound to
ENNReal, and include the joint deviation/variance event by nonnegative scalar
multiplication.

Regularity contracts: Standard Borel ambient space, finite zero-or-probability
measure, strong adaptedness, all-multiple exponential integrability carried by
the source MGF records, the displayed initial/successor MGF witnesses, and
nonnegative tilt and variance coefficient. No independence, deterministic
variance envelope, bounded increments, stationarity, or separate event
measurability is assumed.

Retrieval/status: the compiled fixed-tilt conditional-MGF sum leaf, Mathlib
MGF/conditional-kernel/martingale cards, and the existing EXP3 consumer;
repository Mathlib search found no ready Freedman/Bernstein declaration.
`leanCompiled` with focused builds and an external `Tests.Basic` canary.

Failure policy: this closes fixed-horizon fixed-tilt retention of a random
compensator. It does not optimize the tilt, derive one-step MGF witnesses,
prove maximal/anytime or self-normalized control, or establish a general
Freedman theorem.

## Compiled route: quadratic fixed-MGF delta tail

Lean statement:
`Concentration.measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`
uses a common joint event and fixed-tail bounds for every admissible tilt to
prove the delta tail at
`quadraticFixedMGFRadius c V cap delta`.

Local APIs/imports and route: `ConcentrationQuadraticFixedMGF`, the migrated
`exists_tilt_quadratic_fixedMGF_exponent_le_neg`, real log/sqrt/exp, max,
ENNReal monotonicity, and ordered-field algebra. Choose the exact
interior-or-cap optimizer, compare its exponent to `-log_+(1/delta)`, and
calibrate the latter to delta. Both realized selected-loss and mixed-square
predictable-variance EXP3 delta theorems now consume this route.

Regularity contracts: measurable ambient space; positive variance scale,
variance budget, tilt cap, and delta; and the displayed fixed-tail family.
Probability, filtration, conditional MGF, boundedness, and law transport stay
with each fixed-tail producer.

Retrieval/status: the fixed-tilt predictable-compensator leaf, Mathlib
log/sqrt/exp and order cards, and two local EXP3 consumers; `leanCompiled`,
root imported, focused/`Tests.Basic` built, externally canaried, consumed.

Failure policy: quadratic fixed-horizon optimization is closed. One-step MGF
production, maximal/anytime mixtures, optional stopping, self-normalization,
and general Freedman remain open.

## Compiled route: finite-prefix quadratic maximal tail

Lean statements:
`Concentration.measure_biUnion_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`
proves a nonempty finite-index union bound at equal-share confidence, and
`Exp3.sampledPredictableRealizedDeviation_prefix_max_tail_predictableVariance_delta`
instantiates it over every generated realized-loss prefix of length `t+1` for
`t<horizon`.

Local APIs/imports and proof route: `ConcentrationQuadraticMaximal`, the
quadratic fixed-MGF delta theorem, Mathlib-backed finite outer-measure union,
Finset card/range/sums, ENNReal `ofReal` division and cardinality
cancellation, and the realized predictable-variance fixed-tilt producer. Set
`deltaShare=delta/card`, optimize every indexed event, union, and normalize.

Regularity contracts: generic measurable ambient space; decidable nonempty
finite index set; positive scale, variance budget, cap, and delta; indexed
fixed-tail families. The EXP3 endpoint adds its probability prior, Standard
Borel spaces, nonempty finite support, legal positive gamma, predictable
measurable `[0,1]` losses, and positive horizon. No event measurability,
independence, stationarity, or `delta<=1` premise.

Retrieval/status: prior quadratic delta route, finite-union/measure and
finite-sum cards, realized fixed-tilt EXP3 route; `leanCompiled`, root
imported, focused/root and `Tests.Basic` built, externally canaried at both
generic and model endpoints.

Failure policy: finite prefix-union control with equal-share log-cardinality
cost is closed. Ville/Doob maximal inequalities, horizon-free anytime or
mixture boundaries, optional stopping, self-normalization, general Freedman,
and new one-step MGF producers remain open.

## COND-EXPECT-REWARD practical selected-policy centered-sum tail

Status: `leanCompiled`. The declaration
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_tail_ennreal_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
closes the fixed-horizon analytic route from all-time selected reward-coordinate
conditional laws and practical raw/mean/history-variance contracts to an
ENNReal Azuma-Hoeffding tail for successor centered rewards `1..n-1`.

Proof route: generated-action history filtration and StronglyAdapted process;
existing practical selected-policy one-step `HasCondSubgaussianMGF` with
`varianceCeiling i`; zero initial MGF; Mathlib-backed conditional sub-Gaussian
finite sum. Retrieval evidence is registered under
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-CENTERED-SUM-TAIL`.

Open/failure policy: concrete adaptive models must still construct the
trim-a.e. selected reward map law and prove selected-history variance
domination. If either fails, retain it as the named blocker; do not substitute
independence or an abstract conditional-MGF premise. Arm/sample-count
confidence, anytime concentration, and regret assembly remain open.

## COND-EXPECT-REWARD selected-policy two-sided delta confidence

Status: `leanCompiled`. The generic route now compiles a factor-two absolute
finite-sum tail from Mathlib's conditional-sum MGF theorem and calibrates
`sqrt(2 V log(2/delta))`. The practical theorem
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
uses the selected reward-coordinate law and history-variance source to bound
the centered successor-reward sum `1..n-1` by `ENNReal.ofReal delta`.

Retrieval evidence:
`LOCAL-LEAF-CONCENTRATION-CONDITIONAL-SUBGAUSSIAN-ABS-DELTA`,
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-CENTERED-SUM-TAIL`,
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-CENTERED-SUM-ABS-DELTA`,
Mathlib `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, negation,
outer-measure union, and real log/sqrt algebra.

Failure policy: positive total variance is required by the non-strict bad
event. For zero variance, prove the degenerate equality or switch to a strict
event. Concrete arm-wise/random-count confidence still needs a process adapter;
if selected-law or variance transport is absent, isolate it rather than assume
independence or a global MGF. Anytime, self-normalized, Freedman, and regret
routes remain open.

## Fixed-sample selected-policy centered average leaf

Status: `leanCompiled`. Generic declarations
`Concentration.subGaussianAverageConfidenceRadius`,
`Concentration.measure_average_abs_tail_le_of_measure_sum_abs_tail`, and
`Concentration.condSubGaussian_average_abs_tail_ennreal_delta_of_stronglyAdapted`
close deterministic sum-to-average transport and its strongly-adapted
conditional sub-Gaussian specialization. The practical declaration
`ConditionalExpectationReward.centeredRewardSuccProcess_average_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
reuses the selected-policy sum-delta theorem without adding law or MGF
assumptions.

Lean-facing route: use `range (m+1)`, with zero at slot zero and rewards
`1..m`, then divide the aggregate and `sqrt(2*V*log(2/delta))` radius by the
positive count `m`. Local imports/APIs are `ConcentrationSubGaussian`,
`ConditionalRewardLawSource`, outer-measure monotonicity, `abs_div`, and the
existing practical sum-confidence producer. Retrieval cards are
`LOCAL-LEAF-CONCENTRATION-CONDITIONAL-SUBGAUSSIAN-AVERAGE-ABS-DELTA` and
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-CENTERED-AVERAGE-ABS-DELTA`;
generic and practical `Tests.Basic` canaries compile.

Regularity/failure policy: require `m>0`, positive total proxy variance,
`0<delta<=1`, plus the prior selected reward law, measurability, raw/mean
range, centered kernel, and selected-history variance contracts. Do not erase
`m>0` or claim a zero-sample average; handle zero variance by a strict event
or degenerate equality. Arm-wise empirical means, random pull counts,
anytime/self-normalized/Freedman concentration, and regret remain open.

## UCB product arm-stream fixed-prefix average theorem

Status: `leanCompiled`. The generic independent route now exposes
`Concentration.subGaussian_sum_abs_tail_ennreal_of_iIndepFun`, its exact
delta calibration, and
`Concentration.subGaussian_average_abs_tail_ennreal_delta_of_iIndepFun` over
exactly `Finset.range k`. The theorem target
`UCB.measure_armPrefixAverageConfidenceRadius_le_abs_empiricalMean_sub`
instantiates them for one arm under `UCB.armStreamMeasure`.

Lean-facing proof route and imports: Mathlib
`HasSubgaussianMGF.sum_of_iIndepFun`, negation and finite outer-measure union;
the shared `sqrt(2*V*log(2/delta))` algebra; positive deterministic division;
`UCBArmStreamProcess`, double-`infinitePi` coordinate independence, coordinate
map-law MGF transport, constant `Finset.range k` proxy sums, and the exact
centered-prefix-to-empirical-mean identity. Retrieval cards are
`LOCAL-LEAF-CONCENTRATION-INDEPENDENT-SUBGAUSSIAN-AVERAGE-ABS-DELTA` and
`LOCAL-LEAF-UCB-ARM-STREAM-FIXED-PREFIX-AVERAGE-DELTA`; generic and concrete
external canaries compile. The theorem-card/LML/weapon material remains
retrieval evidence, not a substitute for these local proofs.

Regularity/failure policy: require a Markov arm kernel, centered
one-coordinate `HasSubgaussianMGF`, `k>0`, `sigma2!=0`, and `0<delta<=1`.
Aggregate variance positivity is internal. `k=0` and zero proxy require a
separate degenerate theorem. Existing fixed-count peeling handles canonical
adaptive pull counts; non-product selected-law transport, anytime/
self-normalized/Freedman concentration, and new regret endpoints remain open.

## Selected-policy fixed-arm masked centered-sum theorem

Status: `leanCompiled`. The generic declaration
`ProbabilityTheory.HasCondSubgaussianMGF.indicator` closes conditional
sub-Gaussian witnesses under conditioning-measurable masks using
`condExp_indicator` and conditional-kernel support. The practical route proves
the successor generated action is `F_i`-measurable, builds the fixed-arm masked
StronglyAdapted centered process, and exposes
`ConditionalExpectationReward.armMaskedCenteredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

Retrieval cards are
`LOCAL-LEAF-CONCENTRATION-CONDITIONAL-SUBGAUSSIAN-INDICATOR` and
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-ARM-MASKED-CENTERED-SUM-ABS-DELTA`.
The exact regularity surface remains the practical selected-policy law plus
measurable context/state/mean/reward, raw and mean ranges, centered kernel law,
selected-history variance ceilings, positive total proxy, fixed arm/horizon,
and `0<delta<=1`. The deterministic proxy is not masked. Failure policy: stop
at missing predictability or selected-law transport; do not assume independence.
The separate predictable-variance route below provides the masked proxy without
changing this theorem's statement.

## Conditional sub-Gaussian masked predictable-variance theorem

Status: `leanCompiled`. The card
`LOCAL-LEAF-CONCENTRATION-CONDITIONAL-SUBGAUSSIAN-PREDICTABLE-VARIANCE`
records the fixed-tilt compensated indicator MGF, the fixed-horizon joint tail,
the quadratic radius, and the two-sided delta theorem. The proof subtracts the
quadratic proxy only on the conditioning-measurable mask, iterates the
zero-budget conditional MGF witnesses, and optimizes upper and lower tails.

Regularity/failure policy: require a probability/Standard Borel space,
filtration, predictable masks, StronglyAdapted masked increments and proxies,
the successor conditional sub-Gaussian witnesses, fixed horizon, positive
deterministic proxy budget, and positive delta. The event retains the random
proxy sum and requires it to lie below the supplied budget. Budget/count
specialization compiles downstream; arbitrary variance-budget peeling,
maximal/anytime, self-normalized, general Freedman, and regret claims remain
open.

## Selected-policy successor-arm empirical-mean theorem

Status: `leanCompiled`. The generic declaration
`Concentration.measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail`
transports any sum-confidence event through an arbitrary positive realized Nat
denominator, with no count-measurability premise. The practical declarations
`successorArmPullCount`, `successorArmRewardSum`, and
`successorArmEmpiricalMean` cover coordinates `1..n-1`, while
`armMaskedCenteredRewardSuccProcess_sum_eq_successorArmRewardSum_sub_pullCount_mul`
identifies the masked centered sum under a stationary fixed-arm mean. The final
endpoint is
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

Local APIs/imports and proof route: `MathlibWrappers` supplies generalized
`sumRewards_eq_finset_filter_sum` plus `pullCount_eq_finset_filter_card`;
the compiled arm-masked selected-policy sum theorem supplies the tail;
outer-measure monotonicity divides by the positive realized count; finite-sum
algebra rewrites the result as empirical mean minus `armMean`. Retrieval cards
are `LOCAL-LEAF-CONCENTRATION-RANDOM-COUNT-AVERAGE-TRANSPORT` and
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-SUCCESSOR-ARM-EMPIRICAL-MEAN-ABS-DELTA`;
generic and practical external canaries compile.

Regularity/failure policy for this older endpoint: retain every practical
selected law, measurability, raw/mean range, centered-kernel, selected-history
variance, positive total proxy, and `0<delta<=1` contract; add
`[DecidableEq Action]` and stationarity of the fixed-arm mean. Its radius uses
full horizon variance divided by realized count.

The sharper exact-count endpoint now also has status `leanCompiled` under card
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-SUCCESSOR-ARM-EMPIRICAL-MEAN-EXACT-COUNT-ABS-DELTA`.
`armMaskedVarianceSuccProcess_sum_eq_mul_successorArmPullCount` identifies a
uniform selected-history ceiling's masked proxy with `sigma2*pullCount`, and
`successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
charges exactly `k*sigma2` on `pullCount=k`, for `k>0`, coerced `sigma2>0`, and
`delta>0`. It retains the practical selected-law/range/kernel contracts and
stationary fixed-arm mean, but needs neither positive full-horizon variance nor
`delta<=1`.

The random-count endpoint now also has status `leanCompiled` under cards
`LOCAL-LEAF-CONCENTRATION-POSITIVE-RANDOM-COUNT-EXACT-FIBER-PEELING` and
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-SUCCESSOR-ARM-EMPIRICAL-MEAN-RANDOM-COUNT-ABS-DELTA`.
The generic assembler covers `{0<count and bad(count)}` by exact fibers up to a
deterministic ceiling and normalizes equal `delta/maxCount` shares. The practical
consumer uses `successorArmPullCount_le_horizon`, `maxCount=n`, and
`successorArmEmpiricalMeanPeelingRadius sigma2 count n delta`; its single
positive random-count bad event has mass at most `ENNReal.ofReal delta`.

Regularity for the one-arm/one-horizon theorem: add `n>0`; retain the practical
selected law, uniform selected-history `sigma2` ceiling, stationary arm mean,
coerced `sigma2>0`, and `delta>0`. Count/event measurability, positive
full-horizon variance, and `delta<=1` are not required.

The simultaneous endpoint now has status `leanCompiled` under card
`LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-SUCCESSOR-ARM-EMPIRICAL-MEAN-FINITE-ARM-TIME-ABS-DELTA`.
It defines the family `arms.product (Finset.range T)`, assigns every member
`delta/family.card`, invokes the random-count endpoint at horizon `i+1`, and
uses `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform` to give the
whole union mass at most `ENNReal.ofReal delta`. It requires nonempty explicit
arms, `T>0`, and stationary means for every candidate arm, while retaining the
same practical selected-law and uniform-variance contracts.

The random-width UCB consumer now has status `leanCompiled` under card
`LOCAL-LEAF-UCB-SELECTED-POLICY-SUCCESSOR-RANDOM-WIDTH-LARGE-GAP-DELTA`.
`SelectedPolicySuccessorInitializedScoreMaxSource` isolates the genuine missing
algorithm contracts: an explicit charged time set below `T`, candidate-arm
membership, positive realized counts for best and chosen arms, and pointwise
maximality of the realized-count index. Outside the simultaneous event, the
compiled UCB algebra gives `gap <= 2*chosenRadius`; therefore the existential
large-gap selected-time event has mass at most `ENNReal.ofReal delta`.

Do not force this route through `UCB.finiteHorizonConfidenceBadEvent`: its radius
is sample-independent and cannot represent this realized-count index. The
current adapter also records `Action : Type`, inherited from the existing UCB
score algebra. The concrete source, initialization, and expected pull-count
transport now compile in the leaf below. Explicit threshold selection,
gap-weighted summation, maximal/anytime, self-normalized/general Freedman, and
UCB/ETC regret remain open; do not reopen finite arm/time union algebra or
concentration production.

The concrete generated-policy leaf now has status `leanCompiled` under
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-RANDOM-WIDTH-PULLCOUNT`.
`UCBConditionalRewardLawPolicy` reconstructs the finite pair history from the
reward prefix, initializes successor actions `1..K`, proves exact agreement
with the generated trace, and constructs the previously abstract initialized
score-max source. A final count above `B` forces a charged selection with prior
count at least `B`.

The random-width inversion is closed under two explicit deterministic
contracts at the full log budget `L_T`:
`32*sigma2*L_T < gap^2*B` and `4*L_T < gap*B`. They feed the prior practical
large-gap bound into a high-probability pull-count theorem and an ENNReal
expected-count theorem with right side `B + T*ofReal(delta)`. The source,
count, and expectation declarations are root imported and externally canaried.

The explicit integer-threshold leaf now has status `leanCompiled` under
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-EXPECTED-PULLCOUNT`.
It defines the real threshold as the maximum of
`32*sigma2*L_T/gap^2` and `4*L_T/gap`, then takes `Nat.ceil + 1`.
The ceiling margin proves both strict inequalities and closes the explicit
radius, tail, and expected-count consumers.

The final endpoint directly consumes the complete practical selected reward
law and positive chosen gap, internally produces the concrete large-gap event,
and yields `lintegral N_chosen(T+1) <= threshold + T*ofReal(delta)`. It has no
external threshold, radius, large-gap, or numeric obligations. The finite-arm
gap-weighted pseudo-regret bridge now compiles in the leaf below.

The practical pseudo-regret leaf now has status `leanCompiled` under
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`.
It shifts generated successor actions `1..T` to regret coordinates `0..T-1`,
identifies the resulting counts with successor counts at `T+1`, and aligns the
Real UCB mean gap with `FiniteBanditModel.gap`.

The generic consumer expands ENNReal scalar pseudo-regret as a finite
gap-weighted count sum, exchanges the finite sum and `lintegral`, invokes count
bounds only on positive-gap arms, and removes zero-gap terms using model gap
nonnegativity. The complete practical selected-law endpoint applies the prior
explicit threshold armwise and returns the `Finset.univ` sum of gap times
threshold plus gap times `T*ofReal(delta)`.

The module is root imported, focused-built, and externally canaried. Local
compiled declarations and Mathlib Finset/measure/lower-integral APIs are the
retrieval evidence; theorem-card and weapon-only routes are not proofs. The
textbook sum simplification now compiles below.

The textbook positive-gap leaf now has status `leanCompiled` under
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET`.
For a positive gap `g` and full log budget `L_T`, it proves
`g*threshold <= 32*sigma2*L_T/g + 4*L_T + 2*g`. The route is
`Nat.ceil_lt_add_one`, nonnegative `max <= quadratic+linear`, positive-gap
field normalization, and ENNReal `ofReal` transport.

The finite-arm theorem filters to `g>0`, removes zero gaps from model gap
nonnegativity, and preserves `ofReal(g)*(T*ofReal(delta))`. Its final public
consumer directly combines this textbook sum with the complete practical
selected reward-law pseudo-regret theorem. The module is root imported,
focused-built, and externally canaried; compiled local/Mathlib APIs are the
retrieval evidence, not theorem cards or weapon-only text.

That exact law leaf now compiles as
`LOCAL-LEAF-UCB-SELECTED-POLICY-CANONICAL-REWARD-TRAJMEASURE-TEXTBOOK-PSEUDOREGRET`.
It defines the generated-UCB reward-history step-kernel family and canonical
`Kernel.trajMeasure`, installs the Markov/probability instances, specializes
`historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace_trim`,
and transports the comap-trim law through
`generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy`.
The exported law has the exact trim-a.e. `historyFiltrationSucc`
`condExpKernel.map` surface. The canonical textbook pseudo-regret theorem then
uses that law internally, so callers no longer provide
`h_reward_map_eq_policy`.

Its contracts remain explicit: probability initial law, measurable
context/state/mean, Markov reward kernel, centered kernel law, stationary model
means, positive selected-history variance, `K,T>0`, `delta>0`, mean range, and
pointwise raw range. The module is root imported, focused-built, and externally
canaried. Compiled local declarations and Mathlib kernel/trajectory APIs are
the retrieval evidence; theorem-card and weapon-only text is not proof.

That apparent range blocker is now closed by
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-TEXTBOOK-PSEUDOREGRET`.
The audit found that `CenteredRewardKernelLaw` already packages centered
integrability, zero integral, and `HasSubgaussianMGF`; the practical range
source was redundant for this route. The new one-step theorem transfers that
MGF directly through the selected reward `condExpKernel.map` law.

The route then compiles the predictable arm mask, exact positive-count tail,
finite count peeling, finite arms-times union, generated-UCB large-gap event,
explicit expected count, finite-arm pseudo-regret, and textbook positive-gap
sum. The final canonical `trajMeasure` theorem supplies its selected law
internally and requires no raw range, mean range, or support-restricted sample
space. Its remaining contracts are probability initial law, measurable
context/mean, `CenteredRewardKernelLaw`, stationary model means, positive
selected-history variance, `K,T>0`, and `delta>0`.

The module is root imported, focused-built, and externally canaried. Compiled
local declarations and Mathlib conditional-MGF/predictable-variance/finite-
union/integration APIs are the evidence; theorem cards and weapon-only routes
are not proofs. The canonical ENNReal textbook UCB pseudo-regret theorem route
is closed. Its optional Real/Bochner presentation is now closed by
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-REAL-TEXTBOOK-PSEUDOREGRET`.
The new generic finite-measure leaf derives Real pull-count integrability from
timewise measurability and `pullCount_le_time`; the UCB wrapper assembles Real
pseudo-regret integrability; and the final theorem converts the compiled
lintegral bound into an explicit Bochner expectation bound with RHS
`sum_{gap>0} (textbookGapBudget + gap*(T*delta))`.

This conversion uses `ofReal_integral_eq_lintegral_ofReal`, finite RHS evidence,
`ENNReal.ofReal_le_iff_le_toReal`, and `ENNReal.toReal_sum/add/mul/ofReal`.
It introduces no caller integrability, range, support, or selected-law premise.
The module is root imported, focused-built, and externally canaried; compiled
declarations and `MLIB-MEASURE-INTEGRAL`/`MLIB-FINSET-SUMS` are the evidence.
The Real expectation presentation is therefore closed. Concrete centered-
kernel construction for context-independent direct-subGaussian and common-
bounded finite-arm laws is now closed by
`LOCAL-LEAF-UCB-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`.

The generic module constructs `CenteredRewardKernelLaw` directly from per-arm
MGF witnesses and exact means, or derives it from a common a.s. interval using
the Mathlib-backed bounded MGF wrapper. The nondegenerate interval lemma proves
the common proxy is positive. The UCB consumer chooses `Unit` context,
`armLaw defaultAction` as the initial law, and the context-independent arm-law
kernel for successors, then invokes the canonical Real theorem.

The resulting public theorem needs only per-arm probability laws, common
`lo < hi`, a.e. measurability, common a.s. support, exact model means, a default
arm, positive horizon, and positive delta. It has no abstract centered-law,
selected-law, trajectory-law, variance, or integrability premise. Focused/root/
test builds and retrieval canaries compile. The unequal-range stationary finite-
arm case is now closed by
`LOCAL-LEAF-UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`.

That route keeps `lo arm` and `hi arm` separate, derives one bounded centered
MGF witness per arm, and defines the UCB proxy as the `Finset.univ.sup` of all
armwise interval proxies. `Finset.le_sup` supplies every selected-arm ceiling;
`model.hK` and pointwise nondegenerate intervals supply strict positivity. The
final canonical Real theorem therefore needs no common range and no caller
variance ceiling, while retaining only per-arm probability, measurability,
support, exact-mean, positive-horizon, and positive-delta contracts.

Focused and external canary builds pass. The exact local declarations,
`MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-SUBGAUSSIAN`, the bounded centered MGF
wrapper, and the prior canonical Real card are retrieval evidence. Do not claim
context-dependent/nonstationary reward closure, anytime/self-normalized/general
Freedman control, cross-toolchain LML import, or completion of other bandit/RL
algorithms.

The bounded-support assumption is now removed for stationary finite-arm UCB by
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`.
Callers provide exact means and direct centered `HasSubgaussianMGF` witnesses.
The theorem computes the finite maximum of their armwise proxies, proves every
selected proxy is dominated by it, and needs only one positive member to close
the canonical UCB strict-positivity contract. Other arms may have zero proxy.

The resulting Real expected pseudo-regret bound has no bounded range, common
interval, caller variance ceiling, selected-law, trajectory-law, or
integrability premise. Focused/root/test builds and exact declaration retrieval
pass. `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-FINSET-SUMS`, `Finset.sup`,
`Finset.le_sup`, the direct centered-law constructor, and the canonical Real
endpoint are proof evidence. All-zero-proxy/noiseless models remain a precise
degenerate route; context-dependent/nonstationary, anytime/Freedman,
cross-toolchain, and other algorithms remain open.

## Context-dependent bounded reward-kernel canonical Real UCB

`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-BOUNDED-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is compiled locally. `RewardKernel.centeredRewardKernelLaw_of_hasSubgaussianMGF`
packages arbitrary context/action selected laws from exact pointwise means and
centered MGF witnesses; `RewardKernel.boundedCenteredRewardKernelLaw` derives
those witnesses from common a.s. bounded support. Both constructors install
the selected probability instances and derive integrability and centering.

The final theorem consumes an arbitrary `MarkovRewardKernel`, measurable
history-dependent context extraction, stationary means `model.mean arm`, and a
common `lo < hi` interval. Reward distributions may otherwise vary with context
and action. The canonical generated trajectory, selected-law transport,
positive interval proxy, variance ceiling, and integrability are internal, and
the conclusion is the explicit Real textbook positive-gap sum.

Exact declarations and `MLIB-PROBABILITY-SUBGAUSSIAN`,
`MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and the
canonical Real UCB card are retrieval evidence. Paper and weapon cards only
place or inspire the route. Do not claim context-dependent means, unequal
context/action ranges, direct sub-Gaussian automatic ceilings, nonstationary
regret, anytime/Freedman control, literal LML import, or other algorithms.

## Context-dependent direct sub-Gaussian canonical Real UCB

`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is compiled locally. Its public theorem consumes arbitrary context/action
selected laws with exact stationary arm means and direct centered
`HasSubgaussianMGF` witnesses. A positive global `sigma2` and pointwise proxy
domination are explicit because the context space is arbitrary and need not
have a computable finite maximum.

`RewardKernel.centeredRewardKernelLaw_of_hasSubgaussianMGF` constructs the
centered kernel law, integrability, and zero-centered-mean evidence. The
canonical reward trajectory theorem then derives selected-law transport and
the generated trajectory internally and proves the explicit positive-gap Real
textbook sum. No bounded support, range measurability beyond the MGF contract,
abstract centered law, trajectory law, or caller integrability remains.

Exact declarations, `MLIB-PROBABILITY-SUBGAUSSIAN`,
`MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and the
canonical Real UCB card are proof evidence. Paper/weapon cards only place or
inspire the route. Automatic finite/compact context ceilings, all-zero proxy
models, context-dependent means/nonstationary regret, anytime/Freedman, literal
LML import, and other algorithms remain separate.
