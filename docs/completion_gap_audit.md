# Completion Gap Audit

## Closed Gap: Generated EXP3 Realized-Regret Geometric All-Time Tail

- Lean statement: on one fixed generated EXP3 process and against one fixed
  supported comparator, the union over all positive prefixes where realized
  selected-loss regret crosses the sum of the two scheduled parent budgets has
  outer measure at most `ENNReal.ofReal delta`.
- Local APIs/imports: accepted predictable-regret and pure realized-deviation
  all-time modules; exact finite-prefix deviation decomposition; parent
  membership theorems; `measure_mono`, `measure_union_le`,
  `ENNReal.ofReal_add`, finite sums, ring, and linear arithmetic.
- Proof route: assign `delta/2` to each parent family; prove exact realized =
  predictable + deviation decomposition; show a combined weak crossing forces
  one component weak crossing; apply both parent tails and normalize halves.
- Regularity: probability prior; Standard Borel nonempty Env/Action;
  measurable action singletons; decidable nonempty arms; fixed `eta>0` and
  `0<gamma<1`; one predictable unit-loss process; one supported comparator;
  positive delta. No event measurability, `delta<=1`, independence,
  stationarity, countable Action, supplied integrability, or law transport.
- Retrieval/status: both accepted local all-time parent cards, fixed-horizon
  realized-regret precedent, Mathlib measure/finite-sum/order cards, source
  cards placement only, and weapons inspiration only. Six declarations,
  focused/root/Tests, five canaries, SafeVerify `34d6b6dd...5702`, and baseline
  axiom audit pass. Independent review found no P0/P1/P2/P3; lifecycle records
  are accepted; verified memory is `mem-2a0ffec376992850`; frontier shadow has
  zero mismatches; and the full harness passes.
- Failure policy: fixed-parameter realized regret against one comparator only.
  Next add a finite supported-comparator union and best-arm surface. No tuned
  sublinear all-time rate, horizon retuning, Ville/Doob, mixture, optional
  stopping, self-normalization, general Freedman, horizon-free tuned EXP3, or
  ideal EXP3.P is claimed.

## Closed Gap: Generated EXP3 Predictable-Regret Geometric All-Time Tail

- Lean statement: on one fixed generated EXP3 process and against one fixed
  supported comparator, the union over all positive prefixes where predictable
  regret crosses the scheduled parent budget has outer measure at most
  `ENNReal.ofReal delta`.
- Local APIs/imports: fixed-horizon predictable high-probability regret,
  `ConcentrationConfidenceSchedule`, `MeasureTheory.measure_iUnion_le`,
  `ENNReal.tsum_le_tsum`, and exact geometric share positivity/tsum.
- Proof route: evaluate the parent budget at horizon `n+1` and confidence
  `geometricConfidenceShare delta n / 2`; specialize the parent total tail at
  outer share `geometricConfidenceShare delta n`; compare measure tsums; close
  with the exact outer budget.
- Regularity: probability prior; Standard Borel nonempty Env/Action;
  measurable action singletons; decidable nonempty arms; fixed `eta>0` and
  `0<gamma<1`; one predictable unit-loss process; one supported comparator;
  positive delta. No event measurability, `delta<=1`, independence,
  stationarity, countable Action, supplied integrability, or new law transport.
- Retrieval/status: local predictable-Hedge/exploration/pure-cross/comparator
  assembly and geometric-schedule cards; Mathlib measure/finite-sum/order
  cards; source cards placement only; potential/tail weapons inspiration only.
  Four declarations, root/focused/Tests, three canaries, SafeVerify
  `dc280a8f...b13a5`, and baseline axiom audit pass. Independent review found
  no P0/P1/P2 and its retrieval-timing P3 is closed. Lifecycle records are
  accepted, verified memory is `mem-b8cfa9865d91f12a`, frontier shadow has
  zero mismatches, and the full harness passes.
- Failure policy: fixed-parameter predictable pseudo-regret only. The compiled
  realized-regret all-time route now consumes this event on the same process.
  No tuned sublinear all-time rate within this parent, realized-regret claim,
  horizon retuning, Ville/Doob, mixture, optional stopping, self-normalization,
  general Freedman, horizon-free tuned EXP3, or ideal EXP3.P is claimed.

## Closed Gap: Pure Generated EXP3 Geometric All-Time Deviation

- Lean statement: every exact generated selected-loss predictable variance is
  at most one, its first `horizon` values sum to at most `horizon`, and the
  union over positive prefixes `n+1` where pure realized deviation crosses the
  corresponding deterministic-budget geometric radius has outer measure at
  most `ENNReal.ofReal delta`.
- Local APIs/imports: `FiniteActionDistribution.nonneg/sum_eq_one`, exact
  selected-loss centered variance, generated probability sources,
  `PredictableLossVector` unit-interval bounds, finite sums, the accepted
  geometric joint-event API, and named-event membership theorems.
- Proof route: put the finite-law mean in `[0,1]`; bound every centered square
  by one; weight and sum; instantiate and accumulate the generated variance;
  choose budget `n+1`; remove the universally true variance conjunct by set
  extensionality; rewrite the accepted all-time measure bound.
- Regularity: finite action law and `[0,1]` losses for the support theorem;
  measurable Env, measurable-singleton Action, decidable nonempty arms,
  `0<=gamma<=1`, and one predictable loss process for generated support;
  additionally a probability prior, Standard Borel nonempty Env/Action,
  arbitrary fixed eta, `0<gamma`, and positive delta for the terminal. No event
  measurability, independence, stationarity, `delta<=1`, supplied budget, or
  variance-good premise is required.
- Retrieval/status: local selected-variance/geometric/countable parents;
  `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-VARIANCE`, and
  `MLIB-PROBABILITY-MGF`; source cards are placement only and the tail weapon
  is inspiration only. Focused/root/Tests and six semantic canaries compile;
  SafeVerify fixes `5479f334...870`, and all ten Lean declarations have only
  baseline axioms. Independent review found no P0/P1; its canary and contract
  findings are closed. Lifecycle/frontier and the full harness pass; verified
  memory is `mem-7ceab55257453017` and frontier shadow has zero mismatches.
- Failure policy: the universal `n+1` radius is not a small-loss or self-
  normalized improvement. The same-process predictable-regret assembly now
  compiles above; next combine the two events. No full regret, horizon retuning,
  Ville/Doob, mixture, optional stopping, general Freedman, horizon-free tuned
  EXP3, or ideal EXP3.P is claimed.

## Closed Gap: Generated EXP3 Geometric All-Time Predictable-Variance Tail

- Lean statement: `geometricConfidenceShare` allocates `delta/2/2^n`;
  `tsum_ofReal_geometricConfidenceShare` proves exact ENNReal total
  `ofReal delta`; the EXP3 radius and named countable failure set expose the
  exact `n+1` semantics; the terminal bounds that set by `ofReal delta` on one
  fixed generated process.
- Local APIs/imports: `ConcentrationConfidenceSchedule`,
  `ConcentrationQuadraticScheduled`,
  `Exp3RealizedPredictableVarianceTail`, `hasSum_geometric_two'`,
  `HasSum.toNNReal`, `ENNReal.hasSum_coe`, the generic countable scheduled
  quadratic theorem, and the generated fixed-tilt tail.
- Proof route: transport the real geometric sum through NNReal/ENNReal;
  instantiate constant variance scale and tilt cap one; specialize each
  pointwise theorem at prefix `n+1`; apply the countable parent and rewrite the
  exact total budget.
- Regularity: probability prior; Standard Borel nonempty Env/Action;
  measurable action singletons; decidable Action; nonempty arms; fixed
  `eta`, `0<gamma<=1`, and predictable unit-loss process; positive
  variance-budget schedule and delta. No event measurability, independence,
  stationarity, `delta<=1`, or deterministic variance envelope is required.
- Retrieval/status: the geometric schedule has independent ownership in
  `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`; the consumer uses
  local countable/quadratic/fixed-tilt parents, Mathlib measure/MGF/log/order
  cards, and the OFUL all-time scalar ridge leaf as exact-budget precedent.
  Focused/root/Tests builds, three semantic canaries, SafeVerify
  `be643bca...73b2`, baseline axiom audit, and independent review pass. Status
  is `accepted`; verified memory is `mem-1d262929553ef1ca` and frontier shadow
  reports zero mismatches.
- Failure policy: the theorem does not establish `W_n <= V_n` by itself; the
  unit-budget producer and pure-event consumer above now discharge that gap.
  The next leaf must connect the pure event to same-process pathwise potential,
  exploration, and comparator regret. No full EXP3 regret,
  horizon-dependent retuning, Ville/Doob, mixture, optional stopping,
  self-normalization, general Freedman, or ideal EXP3.P is claimed.

## Closed Gap: Countable Scheduled Quadratic Fixed-MGF Tail

- Lean statement: `quadraticFixedMGFScheduledRadius` evaluates the compiled
  optimized radius on four `Nat -> Real` schedules. The first theorem bounds
  the countable union of scheduled joint deviation/variance events by
  `sum' n, ENNReal.ofReal (deltaAt n)`; the second consumes a caller-supplied
  ENNReal total budget.
- Local APIs/imports: `ConcentrationQuadraticFixedMGF`, its one-event quadratic
  delta theorem, `MeasureTheory.measure_iUnion_le`, and
  `ENNReal.tsum_le_tsum`; the new module is root-imported and externally
  canaried through the full outer-budget statement.
- Proof route: specialize the parent at each index, use countable outer-measure
  subadditivity, compare every tsum term, then apply order transitivity.
- Regularity: measurable ambient space; pointwise-positive variance scale,
  variance budget, tilt cap, and confidence share; per-index fixed-tilt tail
  families. There is no event measurability, finite/probability measure,
  independence, filtration, boundedness, stationarity, or share-upper-bound
  premise.
- Retrieval/status: local quadratic-delta and finite-maximal leaves plus
  `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-MGF`,
  `MLIB-REAL-LOG-SQRT`, and `MLIB-EXP-LOG-INEQUALITIES`; textbook and EXP3
  cards provide placement only. Focused, root, `Tests.Basic`, statement,
  baseline-axiom, index, lifecycle, and full harness gates pass. Status is
  `accepted`.
- Failure policy: no confidence schedule is selected here. Do not infer a
  Ville/Doob or mixture boundary, horizon-free fixed-policy result, optional
  stopping, self-normalization, general Freedman, or ideal EXP3.P theorem.

## Closed Gap: Scalar Joint-Error Deterministic-Tail Confidence

- Lean statement: the left-associated maximum of the six literal
  capped/uncapped sampled-return, actual-successor-policy-return, and
  same-prefix-gap distances is measurable. For every positive real
  `epsilon, delta`, one natural `tailStart` controls every later index: its
  weak superlevel event has `ENNReal` mass `< ENNReal.ofReal delta`, its
  strict sublevel event has real mass `> 1-delta`, and the scalar strict bound
  is equivalent to the same six literal strict bounds.
- Local APIs/imports: the accepted deterministic-tail parent; six coordinate
  measurability lemmas; `Measurable.dist`, `Measurable.max`, `max_lt_iff`,
  `le_max_iff`, `measurableSet_lt`, and exact named good/bad event semantics.
- Proof route: define one six-way maximum, compose measurability, normalize
  strict and weak max predicates, prove named/scalar event equalities, then
  rewrite the parent's mass fields and retain its one all-later cutoff.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, literal actual-policy law, distinct capped `hittingBtwn` and
  uncapped `hittingAfter`, `4 < horizon`, and positive tolerances only.
- Retrieval/status: local-first `mem-cd67b8453f91af1b`; source cards are
  placement only. Seven declarations, root, and typed five-field canary
  compile. SafeVerify fixes `f4fc8680...355a`; placeholders are empty and all
  seven axiom reports are baseline-only. Review's P2/P3 ledger findings are
  closed; lifecycle/frontier/full harness gates pass. Status is `accepted`;
  verified memory is `mem-6f587b6fba5f9bfd`.
- Failure policy: the cutoff is existential/noncomputable. No rate,
  `delta <= 1`, independence, optional stopping, expectation/random-index
  interchange, model uniformity, raw episodes, recommended-policy
  substitution, minimax/reachability, or complete UCB-VI is claimed.

## Closed Gap: Stopped Return Deterministic-Tail High-Probability Optimality

- Lean statement: for every positive real `epsilon, delta`, one existential
  natural `tailStart` works at every later schedule index. The accepted
  six-error bad event is measurable and has `ENNReal` mass below
  `ENNReal.ofReal delta`; its named complement has real probability greater
  than `1 - delta`, exactly when all six literal errors are `< epsilon`.
- Local APIs/imports: the accepted simultaneous-confidence parent and its bad
  event, measurability, complement, and eventual-mass APIs; Mathlib
  `eventually_atTop`, `MeasureTheory.probReal_compl_eq_one_sub`,
  `ENNReal.toReal_lt_toReal`, and `ENNReal.toReal_ofReal`.
- Proof route: convert strict bad `ENNReal` mass to strict real mass, rewrite
  complement probability, define and normalize the named good event, extract
  one `Nat` cutoff with `eventually_atTop.1`, and package all four fields at
  each later index.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward uniform
  sub-Gaussianity, support/floor, literal actual-policy trajectory law,
  distinct capped `hittingBtwn` and uncapped `hittingAfter` prefixes, and
  `4 < horizon`; only `0 < delta`, not `delta <= 1`.
- Retrieval/status: local-first `mem-89d817ed84c75c44`; source cards are
  placement only and no theorem card or weapon is consumed. Seven
  declarations, root import, and typed external canary compile. SafeVerify
  fixes `09d8972f...a28f`; placeholders are empty and all seven axiom reports
  are baseline-only. Independent review's P2/P3 ledger findings are closed;
  lifecycle and full harness gates pass, so the leaf is `accepted`. Verified
  memory is `mem-5265bad6103b31c3`.
- Failure policy: the cutoff is existential and noncomputable. No quantitative
  rate, independence, optional stopping, expectation/random-index
  interchange, model uniformity, raw episodes, recommended-policy
  substitution, minimax/reachability, or complete UCB-VI is claimed.

## Closed Gap: Stopped Return Simultaneous High-Probability Optimality

- Lean statement: at one common schedule index and on the exact generated
  trajectory law, one measurable event is the union of the six capped/uncapped
  sampled-return, actual-successor-policy-return, and same-prefix-gap distance
  violations. Outside it all six distances are `< epsilon`; its probability
  tends to zero and is eventually `< ENNReal.ofReal delta` for positive
  `epsilon, delta`.
- Local APIs/imports: four local stopped-coordinate measurability wrappers,
  two inherited policy-return measurability lemmas, the accepted six
  `TendstoInMeasure` endpoints, and Mathlib `tendstoInMeasure_iff_dist`,
  `measure_union_le`, `tendsto_order`, and `ENNReal.ofReal_pos`.
- Proof route: build the explicit left-associated six-event union, prove its
  complement by `simp`, convert the six in-measure parents to distance-event
  mass limits, dominate the union by their six-term sum, squeeze to zero, and
  specialize the zero neighborhood at a positive confidence tolerance.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded reward means,
  selected-reward sub-Gaussianity, support/floor, literal actual-policy law,
  distinct exact capped and genuine uncapped prefixes, and `4 < horizon`.
- Retrieval/status: local-first `mem-8642ef20df67310d`; source cards are
  placement only and no theorem card or weapon is consumed. Eleven
  declarations, root import, and typed external canary compile. SafeVerify
  fixes `abeed7f0...2c443`; placeholders are empty and seven representative
  axiom reports are baseline-only. Independent review's P2/P3 ledger findings
  are closed with no open P0-P3; lifecycle and full harness gates pass, so the
  leaf is `accepted`.
- Failure policy: finite subadditivity, not independence, proves the joint
  bound. This is qualitative and fixed-model: no finite-index rate/cutoff,
  optional stopping, expectation/random-index interchange, model uniformity,
  raw episodes, recommended-policy substitution, minimax/reachability, or
  complete UCB-VI is claimed.

## Closed Gap: Stopped Sampled/Policy Return In-Measure And A.E. Optimality

- Lean statement: at both the exact capped inverse-square-root first-passage
  prefix and genuine uncapped `hittingAfter`, literal stopped sampled return
  and the trajectory-law expected return of the actual `successorPolicyAt`
  policies converge in measure and almost everywhere to
  `optimalInitialExpectedReturn`; their same-prefix gap converges to zero in
  both modes. The terminal exposes six `TendstoInMeasure` plus six a.e.
  `Tendsto` contracts.
- Local APIs/imports: the accepted stopped-return `L1` terminal and its six
  `eLpNorm 1` limits; capped/uncapped realized and behavior a.e. limits; exact
  sampled/realized, policy/behavior, and deviation identities; Mathlib
  `tendstoInMeasure_of_tendsto_eLpNorm`, `Tendsto.const_sub`, and `Tendsto.sub`.
- Proof route: transport capped realized a.e. convergence through a.s.
  eventual capped/uncapped equality; rearrange return deviation exactly;
  derive six in-measure endpoints from exponent-one norm limits; derive the
  six a.e. endpoints independently from a.e. parents and exact algebra; package
  the literal capped/uncapped surfaces.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded reward means,
  selected-reward uniform sub-Gaussianity, exploratory support/floor, literal
  actual-policy trajectory-law semantics, exact prefixes, and
  `4 < mdp.horizon`.
- Retrieval/status: local-first `mem-1ae15dfd64b32dc6`; Mathlib
  `ConvergenceInMeasure` supplies the general conversion API; `SCN-RL-MDP`
  and the UCB-VI paper card are placement only, with no theorem card or weapon
  consumed. Fifteen declarations, root import, and external declaration/
  generic-terminal/typed-twelve-contract canaries compile. SafeVerify fixes
  `22635f14...ad041`; placeholders are empty and seven representative axiom
  reports are baseline-only. Independent review's sole P3 stale-ledger
  finding is closed with no open P0-P3; lifecycle and full harness gates pass,
  so the leaf is `accepted`.
- Failure policy: a.e. convergence is not inferred from convergence in
  measure. This fixed-model qualitative result does not prove
  expectation/random-index interchange, optional stopping, rates, model
  uniformity, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI.

## Closed Gap: Stopped Sampled/Successor-Policy Return L1 Optimality

- Lean statement: at both the exact capped inverse-square-root first-passage
  prefix and genuine uncapped `hittingAfter`, the sampled-return optimality
  error, literal actual-successor-policy return optimality error, and their
  same-prefix gap are coordinatewise `MemLp 1`; all six exponent-one
  `eLpNorm` sequences tend to zero.
- Local APIs/imports: the accepted sampled/realized, policy/behavior, and
  sampled-policy/return-deviation pointwise identities; capped and uncapped
  realized-regret, behavior-regret, and return-deviation `MemLp 1` and
  `eLpNorm` limits; Mathlib `MemLp.neg` and `eLpNorm_neg`.
- Proof route: define three stable centered/gap processes -> rewrite them
  exactly to negative realized regret, negative behavior expected regret, and
  return deviation -> transport six coordinatewise `MemLp` contracts and six
  norm limits -> package the two stopping routes in one terminal theorem.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded reward means,
  selected-reward uniform sub-Gaussianity, exploratory support/floor, literal
  `successorPolicyAt` trajectory-law semantics, exact same-prefix processes,
  both exact stops, and `4 < mdp.horizon`.
- Retrieval/status: local-first record `mem-de0a77c377532117`; scenario
  `SCN-RL-MDP` and paper card `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` are placement
  only; no proof weapon is consumed. Twenty declarations, the project root,
  and external declaration/generic-terminal/typed-twelve-contract canaries
  compile. SafeVerify fixes hash `604b612b...a9562a`; the placeholder scan is
  empty and ten representative axiom reports are baseline-only. Independent
  review's sole P2 canary finding is closed with no open P0-P3; lifecycle and
  the full harness gate pass, so the leaf is `accepted`.
- Failure policy: this proves true fixed-model `L1` convergence, not merely a
  difference of expectations. It does not prove expectation/random-index
  interchange, optional stopping, a pathwise or quantitative rate,
  model-uniform control, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI.

## Closed Gap: Stopped Sampled/Successor-Policy Expected-Return Consistency

- Lean statement: the actual `successorPolicyAt trajectory t` expected return
  is the literal integral of cumulative reward under that policy's trajectory
  law. Its equal-round natural-prefix average, with optimal return at prefix
  zero, equals optimal return minus average behavior expected regret. At both
  exact stopping prefixes, sampled return minus this policy return equals
  return deviation pathwise and in expectation; both signed and absolute
  expected gaps vanish and both expected policy returns converge to optimal.
- Local APIs/imports: `MarkovPolicy.expectedRegret`; policy trajectory measure
  and `cumulativeReward`; existing sampled-return complement; stopped
  realized/behavior/return-deviation decomposition; stopped behavior
  `MemLp 1`; capped/uncapped behavior and return-deviation integral limits;
  finite sums, `integral_sub`, and continuous subtraction.
- Proof route: literal policy integral -> unfold expected regret -> zero/nonzero
  finite-prefix complement -> stopped measurability and integrability ->
  eliminate realized and behavior regret at one random prefix -> exact
  sampled-policy-deviation integral identity -> signed/absolute gap and
  policy-return limits ->
  terminal package.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means, selected-reward
  sub-Gaussianity, exploratory support/floor, exact dependent source and
  `successorPolicyAt` indexing, equal-round normalization, zero-prefix
  convention, both exact stops, and `4 < mdp.horizon`.
- Retrieval/status: exact no-hit; local-first record `mem-06aaf9949ace539d`;
  29 declarations plus root and external literal/zero-prefix/positive-prefix/
  `untopA`/stopped/typed-terminal-projection canaries compile. SafeVerify
  passes at `e35de2a4...7353`; placeholders are empty and ten representative
  axiom reports are baseline-only. Independent review's P2/P3 findings are
  closed by the typed contract canaries, absolute-gap wrappers, and expanded
  terminal bundle; no P0-P3 remains.
- Failure policy: no expectation/random-index interchange, optional stopping,
  pathwise sampled-return convergence, rate, raw episodes, recommended-policy
  substitution, minimax/reachability, or complete UCB-VI follows.

## Closed Gap: Stopped Average Sampled-Return Expected Optimality

- Lean statement: define the observed successor-batch sample mean and its
  natural-prefix average, using the optimal initial expected return at prefix
  zero. Prove the total identity `sampled return = optimal - realized regret`.
  At both exact capped and genuine uncapped prefixes, sampled return is
  integrable, its expectation is exactly optimal minus expected realized
  regret, and its expectation tends to the optimal initial value.
- Local APIs/imports: `sampledCumulativeRewardSum`; natural average realized
  regret and its natural-filtration adaptation; `stoppedValue` and
  `measurable_stoppedValue`; capped/uncapped stopped `MemLp 1`; both realized
  integral limits; `Finset.sum_sub_distrib`; `integral_sub`;
  `Tendsto.const_sub`.
- Proof route: explicit batch/prefix finite sums -> split zero/nonzero prefix
  -> exact complement algebra -> filtration adaptation -> stopped pointwise
  identity -> integrability by constant subtraction -> exact Bochner
  expectation identity -> map both realized-regret expectation limits through
  constant subtraction -> terminal package.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, exploratory support/floor, exact source,
  scheduled batch normalization, natural filtration, zero-prefix convention,
  generic zero-size batch totalization to zero, positive scheduled batch sizes,
  both exact stops, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; local-first record
  `mem-31b7a2396410fc17`. Twenty-two declarations, root import, and external
  semantic/regularity/integrability/expectation/limit/terminal canaries
  compile. SafeVerify passes at `cf81f234...e5f5`; placeholders are empty and
  representative axioms are baseline-only. Independent review's two P3
  hardening findings are closed by the totalization documentation and direct
  zero-prefix plus capped/uncapped measurability canaries; no P0-P3 remains,
  lifecycle shadow and the full gate pass.
- Failure policy: no expectation/random-index interchange, optional stopping,
  sample-path return convergence, quantitative rate, model uniformity, raw
  episodes, behavior=recommended equality, minimax/reachability, or complete
  UCB-VI follows.

## Closed Gap: Stopped Realized/Policy-Value Expected Consistency

- Lean statement: for both the exact capped first-passage and genuine
  uncapped `hittingAfter` prefixes, expected realized regret minus the
  successor-policy value-gap expectation equals the negative return-deviation
  expectation at every schedule index. Both signed and absolute vertical
  gaps tend to zero. Together with the accepted behavior and realized
  uncapped-minus-capped gaps, an exact per-index path identity gives a full
  expectation-consistency square.
- Local APIs/imports: accepted capped/uncapped expected decompositions;
  capped/uncapped return-deviation integral limits; accepted horizontal
  behavior/realized expected gaps; `Tendsto.neg`; `continuous_abs`; `ring`.
- Proof route: normalize each expected decomposition into the vertical
  identity -> rewrite each vertical sequence to negative expected return
  deviation -> apply return convergence and negation -> map through absolute
  value -> prove the two square paths equal by ring arithmetic -> package all
  exact identities and eight edge limits.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, exploratory support/floor, exact source,
  indexing, centering, normalization, behavior-policy semantics, both exact
  stops, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; local-first record
  `mem-4fafd4fc9904f47d`. Seven declarations, root import, and external
  declaration/terminal canaries compile. SafeVerify passes at
  `d07f9ed4...c7b9`; placeholders are empty, axioms are baseline-only, and
  independent local review found no open P0-P3. The full gate passes.
- Failure policy: no expectation/random-index interchange, optional stopping,
  finite-index equality, quantitative rate, model uniformity, raw episodes,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI
  follows.

## Closed Gap: Componentwise Capped/Uncapped Expected Truncation

- Lean statement: on the exact generated trajectory law, the signed and
  absolute differences between uncapped and capped behavior-expected-regret
  expectations tend to zero, and the analogous two return-deviation limits
  hold. Capped and uncapped expected realized regret each equal expected
  behavior regret minus expected return deviation. All six coordinates are
  integrable, and all four capped/uncapped component expectations tend to
  zero.
- Local APIs/imports: accepted componentwise behavior/return `MemLp 1` and
  difference-integral limits; accepted realized expectation replacement;
  exact stopped decomposition; `MemLp.integrable`; `integral_sub`;
  `continuous_abs`.
- Proof route: derive coordinate integrability -> rewrite each integral of a
  difference as a difference of integrals -> apply continuous absolute value
  -> preserve the pointwise realized/behavior/return identity -> integrate
  the same representatives -> package the four coordinate limits.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, exploratory support/floor, exact source,
  indexing, centering, normalization, behavior-policy semantics, both exact
  stops, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; local-first record
  `mem-bf148b8e7faff0cd`. Seven declarations, root import, and external
  expected-gap/decomposition/terminal canaries compile. SafeVerify passes at
  `d46e2fb3...e0e53`; placeholders are empty, axioms are baseline-only, and
  independent local review found no P0-P3. The full gate passes.
- Failure policy: no expectation/random-index interchange, optional stopping,
  finite-index equality, quantitative truncation rate, model uniformity, raw
  episodes, behavior=recommended equality, minimax/reachability, or complete
  UCB-VI follows.

## Closed Gap: Componentwise Capped/Uncapped Policy-Value L1 Truncation

- Lean statement: on the exact generated trajectory law, capped and uncapped
  stopped behavior-expected-regret and return-deviation coordinates are
  a.e.-eventually equal. Capped behavior and return are `MemLp 1` with
  vanishing exponent-one norm and signed integral. Both uncapped-minus-capped
  component differences are `MemLp 1` and their norms/integrals tend to zero.
  Both stopped realized/behavior/return decompositions and the exact identity
  `Delta return = Delta behavior - Delta realized` are retained.
- Local APIs/imports: capped/uncapped eventual-base prefix theorems; capped
  stopping-time theorem; all-prefix behavior a.e. limit; generic `2H` bound;
  accepted capped/uncapped realized L1 terminal; accepted uncapped
  behavior/return terminal; `MemLp.sub`; `memLp_congr_ae`;
  `eLpNorm_congr_ae`; `eLpNorm_sub_le`; dominated and Bochner integral
  continuity.
- Proof route: capped eventual-base equality -> `untopA` divergence ->
  random-prefix behavior composition -> bounded/dominated capped behavior L1
  -> exact capped decomposition -> capped return L1 -> behavior-difference
  triangle -> exact component-difference algebra plus accepted realized
  truncation -> return-difference L1 -> signed-integral continuity.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, exploratory support/floor, exact source,
  indexing, centering, normalization, behavior-policy semantics, both exact
  stops, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; local-first record
  `mem-1011ebc0a0909b71`. Eighteen declarations, root import, and external
  canaries compile. SafeVerify passes at `20132e52...62acb`; placeholders are
  empty and the public axiom set matches both accepted parents. Independent
  local review and the full gate pass.
- Failure policy: no expectation/random-index interchange, optional stopping,
  finite-index equality, quantitative truncation rate, model uniformity, raw
  episodes, behavior=recommended equality, minimax/reachability, or complete
  UCB-VI follows.

## Closed Gap: Uncapped Policy-Value And Return-Deviation L1

- Lean statement: at the exact genuine uncapped `hittingAfter` prefix, the
  successor-policy value-gap average is measurable, pointwise in `[0,2H]`,
  `MemLp 1`, and tends to zero a.e., in expected absolute value,
  `eLpNorm 1`, and signed integral. The exact stopped realized/behavior/return
  decomposition holds, and return deviation is `MemLp 1` with vanishing
  exponent-one norm and signed integral.
- Local APIs/imports: cumulative behavior measurability/nonnegativity/`2H`;
  `measurable_apply_randomNat`; `ae_tendsto_apply_randomPrefix`; uncapped
  prefix divergence; `Integrable.of_bound`;
  `tendsto_integral_filter_of_norm_le_const`;
  `MemLp.eLpNorm_eq_integral_rpow_norm`; accepted realized L1;
  `memLp_congr_ae`; `MemLp.sub`; `eLpNorm_congr_ae`; `eLpNorm_sub_le`.
- Proof route: deterministic average envelope -> measurable random-prefix
  evaluation -> a.e. composition -> dominated L1 behavior limits -> exact
  same-prefix decomposition -> L1 triangle for return deviation -> Bochner
  integral continuity and integral decomposition.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive proxy/floor, bounded means, selected-reward
  sub-Gaussianity, support/floor, exact source/indexing/centering/per-batch
  normalization/behavior semantics, genuine uncapped stop, and
  `4 < horizon`.
- Retrieval/status: no duplicate; exact local and Mathlib APIs are recorded
  under `mem-cd29ac6abaf4cb55`. Twenty-three declarations, root import, and
  external canaries compile. SafeVerify passes at `0af3bbb9...79da77`, the
  public axiom audit is baseline-only, independent review found no P0-P3,
  and the full gate passes with 36 CLI tests and one expected skip.
- Failure policy: do not substitute a deterministic integrated average,
  commute expectation with the random index, or infer optional stopping,
  finite-index equality, rates, model uniformity, raw episodes,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI.

## Closed Gap: Expected-Regret Truncation Replacement

- Lean statement: on the exact same generated trajectory law, capped and
  uncapped stopped-process coordinates are integrable, the integral of their
  pointwise uncapped-minus-capped difference is exactly the difference of
  their integrals, both forms and the absolute expected gap tend to zero, and
  both signed expectations tend to zero.
- Local APIs/imports: accepted capped/uncapped L1 comparison; accepted
  uncapped signed-expectation terminal; `memLp_one_iff_integrable`;
  `integrable_zero`; `eLpNorm_congr_ae`; `tendsto_integral_of_L1'`;
  `integral_sub`; and `continuous_abs`.
- Proof route: generic arbitrary-measure L1 integral continuity -> exact
  truncation-error integral limit -> coordinate integrability and
  `integral_sub` -> signed expected gap -> continuity of absolute value ->
  direct capped expectation limit plus accepted uncapped expectation limit.
- Regularity: unchanged finite nonempty Standard Borel spaces, initial and
  generated probability laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, support/floor, exact source/indexing/
  centering/normalization/behavior, both exact stop definitions, and
  `4 < horizon`. The generic wrapper has no finite-measure assumption.
- Retrieval/status: no duplicate; exact accepted local parents and Mathlib
  Bochner/topology APIs, recorded as `mem-0c4479e50a03a4ce`. Six
  declarations, root import, and external canaries compile. SafeVerify passes
  at `ef44a0df...b9741`; the declaration audit uses only baseline axioms.
  Independent review found no P0-P2; both P3 metadata findings are closed.
  Lifecycle shadow and the full gate pass, including 36 CLI tests with one
  expected skip.
- Failure policy: do not infer finite-index equality, equality on or between
  delayed events, a quantitative rate, optional stopping, policy-value
  identity, model uniformity, raw episodes, behavior=recommended equality,
  minimax/reachability, or complete UCB-VI.

## Closed Gap: Capped/Uncapped HittingAfter L1 Truncation Equivalence

- Lean statement: outside the existing capped inverse-square-root delayed set,
  both the capped first-passage stop and exact uncapped `hittingAfter` stop
  equal the common deterministic base and their stopped processes agree;
  almost every trajectory eventually has exact equality. Their difference is
  coordinatewise `MemLp 1` and tends to zero in `eLpNorm 1`, named
  `Lp Real 1`, and measure.
- Local APIs/imports: delayed-set equality; capped stopping-prefix lower bound;
  uncapped `eq_base_of_process_le`; compiled capped L1 and uncapped Lp
  terminals; `MemLp.sub`; `eLpNorm_sub_le`;
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; and
  `tendstoInMeasure_of_tendsto_eLpNorm`.
- Proof route: delayed-set nonmembership -> capped upper bound and threshold
  nonviolation -> both stops equal base -> pointwise stopped-process equality;
  Borel-Cantelli parent -> a.e. eventual equality; parent L1 norms plus the
  triangle inequality -> difference norm convergence -> Lp and in-measure
  packaging.
- Regularity: unchanged finite nonempty Standard Borel spaces, initial and
  generated probability laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, support/floor, exact source/indexing/
  centering/normalization/behavior, exact capped and uncapped stops, exact
  capped delayed set, and `4 < horizon`.
- Retrieval/status: no duplicate local comparison theorem; exact compiled
  parents and Mathlib Lp APIs. Ten declarations, root import, and external
  terminal/#check canaries compile. SafeVerify passes at `b68c4bc4...76a80`;
  placeholders and baseline axioms are clean. Independent review found no
  P0-P2, and its two P3 metadata findings were closed; lifecycle shadow and
  the full repository gate pass.
- Failure policy: equality is only outside the capped delayed set. Do not
  identify capped and uncapped delayed events or infer an explicit truncation
  rate, optional stopping, model uniformity, raw episodes,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI.

## Closed Gap: Delayed-Event Expected Contribution At Exact HittingAfter

- Lean statement: the existing capped inverse-square-root first-passage
  delayed event is measurable and has probability tending to zero; for the
  genuine uncapped stopped process, both its restricted expected absolute
  contribution and the absolute signed restricted expectation on that event
  tend to zero.
- Local APIs/imports: accepted uniform absolute continuity;
  `Filter.Tendsto.eventually`; `Iio_mem_nhds`; `eventually_atTop`;
  `integral_nonneg`; `abs_integral_le_integral_abs`; compiled delayed-set
  measurability and `delayedProbability_tendsto_zero`.
- Proof route: event mass convergence enters the UI delta eventually -> apply
  the uniform restricted absolute-integral bound at half epsilon -> metric
  convergence of restricted L1 mass -> squeeze the absolute signed integral.
- Regularity: unchanged finite nonempty Standard Borel spaces, initial and
  generated probability laws, positive proxy/floor, bounded means,
  selected-reward sub-Gaussianity, support/floor, exact source/indexing/
  centering/normalization/behavior, genuine uncapped stop, exact capped
  delayed-set definition, and `4 < horizon`. The generic bridge needs no
  finite-measure or probability assumption.
- Retrieval/status: no memory/local/Mathlib duplicate; exact accepted parent,
  compiled delayed-event producer, and Mathlib order/integral APIs. Three
  declarations, root import, and external generic/exact canaries compile;
  SafeVerify `304b5afc...499c0`, placeholder scan, and baseline-axiom audit
  pass. Independent review found no P0-P3 and the requested signed generic
  application canary now compiles. Lifecycle shadow and the full repository
  gate pass.
- Failure policy: qualitative fixed-model convergence only; no explicit rate,
  optional stopping, model uniformity, raw episodes, behavior=recommended
  equality, minimax/reachability, or complete UCB-VI.

## Closed Gap: Exact Uncapped HittingAfter Uniform Absolute Continuity

- Lean statement: for every positive epsilon, one positive delta controls the
  exact stopped-regret restricted integral uniformly over every schedule index
  and measurable event of probability at most `ENNReal.ofReal delta`; both
  the integral of absolute regret and the absolute signed integral are at
  most epsilon.
- Local APIs/imports: accepted exact stopped-process `UniformIntegrable`;
  `UniformIntegrable.unifIntegrable`; `UniformIntegrable.memLp`;
  `MemLp.indicator`; `MemLp.eLpNorm_eq_integral_rpow_norm`;
  `integral_indicator`; `ENNReal.ofReal_le_ofReal_iff`; and
  `abs_integral_le_integral_abs`.
- Proof route: take Mathlib's UI delta; rewrite the exponent-one indicator
  norm as `ofReal` of the restricted absolute integral; reflect the ENNReal
  bound into `Real`; then dominate the absolute signed integral.
- Regularity: unchanged finite nonempty Standard Borel spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, exact source/stop/indexing/centering/normalization/behavior,
  `4 < horizon`, and per-event measurability.
- Retrieval/status: no memory or local duplicate; exact Mathlib source and
  accepted UI parent; two declarations, root import, external generic and
  terminal canaries, SafeVerify `db0cd463...71c67`, empty placeholder scan,
  and baseline-only axioms compile. Independent review's one P3 fence-guard
  finding was repaired, leaving no P0-P3; lifecycle shadow and the full
  repository gate pass.
- Failure policy: qualitative fixed-model epsilon-delta only; no computable
  delta, tail/moment rate, optional stopping, model-uniform control, raw
  episodes, behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Exact Uncapped HittingAfter Uniform Integrability And Signed Expectation

- Lean statement: the exact genuine uncapped stopped-regret sequence is
  Mathlib probability-theory `UniformIntegrable` at exponent one, and its
  signed Bochner integrals tend to zero.
- Route: the accepted L1/eLpNorm limit gives `UnifIntegrable`; the convergent
  named `Lp Real 1` range is bounded, and `Lp.enorm_toLp` turns this into the
  uniform norm field required by `UniformIntegrable`. Independently,
  `tendsto_integral_of_L1'` gives the signed expectation limit.
- Evidence: four declarations, root import, external generic and terminal
  canaries, SafeVerify `2c010bef...fcd24`, empty placeholder scan, baseline
  axioms, and independent review with no P0-P3.
- Scope boundary: fixed-model sequence UI and signed expectation consistency,
  not optional stopping, a stopping-time moment/rate theorem, model/index
  uniformity, raw episodes, behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Exact Uncapped HittingAfter Lp

- Lean statement: the accepted expected-absolute exact uncapped stopped-regret
  limit now has coordinate `MemLp 1`, exact exponent-one `eLpNorm`, named
  `Lp Real 1`, in-measure, and a.e. surfaces in one terminal theorem.
- Route: fixed-index integrability gives `MemLp 1`; Mathlib identifies
  `eLpNorm 1` with the lifted absolute integral; continuous `ENNReal.ofReal`
  and `Lp.tendsto_Lp_iff_tendsto_eLpNorm''` provide the two norm limits.
- Evidence: the eight-declaration module, root import, and seven external
  canaries compile; SafeVerify hash is `30ec3b42...aaca8a8`; five audited
  theorem layers use only the baseline axioms. Independent review found no
  P0-P3 and its terminal-consumer canary request is closed.
- Acceptance: retrieval/index/lifecycle records are synchronized, frontier
  shadow has no mismatches, and full `python3 tools/bandit.py check` passes.
- Scope boundary: this parent is fixed-model exact-source L1/Lp. The accepted
  child above now proves sequence UI and signed expectation convergence, but
  still no optional stopping, stopping-time rate, model-uniform control, raw
  episodes, or complete UCB-VI.

## Closed Gap: Exact Uncapped HittingAfter L1 Consistency

- Lean statement: the canonical expected absolute exact natural-causal average
  realized behavior regret at the genuine uncapped inverse-square-root
  `hittingAfter` tends to zero.
- New foundations: measurable dynamic coordinate evaluation; square-summable
  weighted stopping-fiber Holder; global successor-coordinate MGF and uniform
  L2 envelope; exact first-hit negative-overshoot inequality.
- Route: the accepted positive-part limit handles excess above zero. For the
  negative part, immediate hits are bounded by the summable explicit-prefix L1
  term, while delayed hits are bounded by `|X_(hit-1)| / hit`; the reciprocal
  square tail makes the latter expectation vanish.
- Closed gap: the previous exact uncapped route was only one-sided. It now has
  an accepted fixed-model L1 endpoint after SafeVerify, independent review,
  lifecycle shadow, and the full repository gate.
- Still open: optional stopping, a uniform-integrability theorem, stopping-time
  moment/rate bounds, model-uniform rates, raw-episode regret,
  behavior=recommended equality, minimax/reachability, and complete UCB-VI.

## Closed Gap: Expected Positive-Part Consistency At Exact HittingAfter

- Lean statement: for the exact uncapped inverse-square-root `hittingAfter`
  stopped average realized behavior regret, the expected positive part tends
  to zero as the schedule index tends to infinity.
- Local APIs/imports: the accepted fixed-index stopped-process integrability
  parent, exact finite-hit pointwise threshold theorem, `Integrable.abs.mono'`,
  `Measurable.max`, `integral_mono_ae`, threshold positivity/convergence, and
  `squeeze_zero`.
- Proof route: dominate `max stoppedProcess 0` by `abs stoppedProcess`; use
  a.e. finiteness of the genuine hit to bound the maximum by the positive
  threshold; integrate; then sandwich the nonnegative expected positive part
  between zero and the inverse-square-root threshold.
- Regularity contracts: exact finite nonempty Standard Borel spaces,
  generated probability law, selected-reward uniform sub-Gaussianity,
  support/floor and bounded-mean conditions, positive proxy/floor,
  source/filtration/indexing/centering/normalization/behavior semantics, and
  `4 < horizon` are preserved from the parent route.
- Retrieval/status: no matching local theorem or typed memory result; exact
  local/Mathlib route compiled in scratch as `mem-f0db6d1dd3a432a9`;
  `leanCompiled` with four declarations, three external canaries, SafeVerify
  hash `151c8c10...e9815`, clean placeholders, baseline-only axioms, and
  independent local review with no P0-P3.
- Failure policy: this is one-sided excess consistency. It does not prove
  signed expectation convergence, expected-absolute/L1 convergence, uniform
  integrability, optional stopping, uniform-in-model/index control, raw
  episodes, behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Cauchy-Schwarz Degree-Four Expected-Absolute Asymptotics

- Lean statement: with finite-MDP/generated-source parameters fixed, the
  actual expected absolute stopped average realized behavior regret is
  `O((scheduleIndex+1)^4)`.
- Local APIs/imports: the accepted degree-eight moment parent,
  `Real.sum_mul_le_sqrt_mul_sqrt`, `Summable.sum_le_tsum`,
  `Summable.tsum_le_of_sum_le`, the exact stopping-fiber weighted-moment
  identity, the uniform coordinate-L2 stopped-value bound,
  `Asymptotics.IsBigO.sqrt`, and
  `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.
- Proof route: apply finite-sum Cauchy--Schwarz to
  `sqrt p_n=((n+1)*sqrt p_n)*(1/(n+1))`; pass both square sums to `tsum`;
  rewrite the weighted mass as the actual rounds second moment; substitute
  its polynomial budget; then use `sqrt(s^8)=s^4` and `IsBigO.sqrt`.
- Regularity contracts: the generic theorem needs a finite measure,
  measurable/a.e.-finite fixed stopping time, rounds `MemLp 2`, coordinate
  `MemLp 2`, and a uniform coordinate second moment. The terminal retains all
  exact probability/Standard-Borel/MGF/support/indexing/centering/
  normalization/behavior contracts, positive proxy/floor, bounded means, and
  `4 < horizon`; only the schedule index varies.
- Retrieval/status: no direct memory hit; exact local and Mathlib APIs compiled
  in scratch as `mem-e0a6fb8355363a3e`; `leanCompiled` with two generic and
  ten RL declarations, five external canaries, SafeVerify hash
  `11fca241...145b4`, clean placeholders, baseline-only axioms, and
  independent review with no P0-P3.
- Failure policy: degree four is an improved fixed-model growth envelope
  relative to the available degree-eight second moment, not a sharp or
  decreasing regret rate. It does not prove uniform-in-model/index control,
  UI/L1 convergence, optional stopping, raw episodes, behavior=recommended,
  or complete UCB-VI.

## Closed Gap: Degree-Eight Stopping-Round Moment Asymptotics

- Lean statement: with the finite MDP, generated source, reward law, policy,
  support, variance proxy, and visit floor fixed, both the actual successor
  stopping-round second moment and expected absolute stopped average realized
  behavior regret are `O((scheduleIndex+1)^8)`.
- Local APIs/imports: the accepted polynomial pointwise parent,
  `Mathlib.Analysis.Asymptotics.Lemmas`, `Asymptotics.isBigO_iff`,
  `Nat.one_le_pow`, `Nat.pow_le_pow_left`, `one_le_pow₀`,
  `integral_nonneg`, `tsum_nonneg`, and `Real.norm_eq_abs`.
- Proof route: normalize `((c*s)^4+1)^2` to a fixed coefficient times
  `s^8`; absorb the nonnegative weighted MDP and shifted inverse-square
  constants using `1 <= s^8`; export scalar budget `IsBigO`; then transport
  the accepted exact integral bounds through norm nonnegativity.
- Regularity contracts: all model/source parameters are fixed while only the
  natural schedule index varies. The terminal retains the exact probability,
  Standard-Borel, MGF, support, indexing, centering, normalization, behavior,
  positive proxy/floor, bounded-mean, and `4 < horizon` contracts.
- Retrieval/status: no prior matching card; local parent and OFUL/UCB
  `isBigO_iff` patterns plus exact Mathlib APIs retrieved as
  `mem-208816c27b4594b9`; `leanCompiled` with twenty-five declarations, five
  external canaries, SafeVerify hash `ee350657...66dc1c`, clean placeholders,
  baseline-only axioms, and independent review with no P0-P3.
- Failure policy: exponent eight remains the stopping-round second-moment
  envelope; its expected-absolute exponent is sharpened by the Cauchy--Schwarz
  child above. It does not evaluate the weighted constant or prove convergence, uniform
  moments, UI/L1 control, optional stopping, sharpness, raw episodes,
  behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Polynomial Stopping-Round Second-Moment Bound

- Lean statement: for each fixed index, the explicit ceiling start plus one is
  at most `(Nat.ceil rateCoefficient + 2) * (scheduleIndex + 1)`. Therefore
  the exact checkpoint square is bounded by
  `(((Nat.ceil rateCoefficient + 2) * (scheduleIndex + 1))^4 + 1)^2`, and the
  actual stopping-round second moment and stopped-regret absolute integral use
  this degree-eight term plus one named MDP-only weighted failure constant.
- Local APIs/imports: the accepted explicit-tail-start module,
  `Real.sqrt_le_iff`, `Nat.le_ceil`, `Nat.ceil_le`, max/multiplication order,
  `Nat.pow_le_pow_left`, weighted-series `ne_top`, `ENNReal.toReal_add`, and
  `ENNReal.toReal_mono`.
- Proof route: bound sqrt by the positive natural scale, transport the rate
  coefficient through its ceiling, handle both maximum branches and the final
  successor, raise monotonically through fourth power and square, isolate the
  unchanged weighted `tsum`, then compose the accepted actual-moment and
  stopped-value endpoints.
- Regularity contracts: the scalar inequalities use finite MDP parameters and
  one fixed index. Real conversion keeps `4 < horizon`; the terminal preserves
  the exact generated probability/Standard-Borel/MGF/support/indexing/
  centering/normalization/behavior contracts, positive proxy/floor, and
  bounded means. No independence or optional-stopping premise is added.
- Retrieval/status: no prior polynomial-start memory hit; exact local parent
  declarations and Mathlib order/sqrt/integral APIs retrieved;
  `leanCompiled` with sixteen declarations, five external canaries, SafeVerify
  hash `ef4b1038...0aba9`, empty placeholder scan, and baseline-only axioms.
- Failure policy: the MDP-only failure constant is a proved-finite `tsum`, not
  a numerical closed form. This is pointwise in `scheduleIndex`, not uniform
  integrability, L1 convergence, optional stopping, raw episodes,
  behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Explicit Tail-Start Deterministic Second-Moment Bound

- Lean statement: the exact scheduled realized-regret rate is bounded by one
  explicit coefficient divided by `n+1`; therefore
  `max scheduleIndex (Nat.ceil (coefficient * sqrt (scheduleIndex+1)))`
  satisfies the all-later inverse-sqrt threshold comparison. The canonical
  `Nat.find` start is no larger, so the actual stopping-round second moment
  and stopped-regret absolute first moment inherit an explicit deterministic
  budget with no canonical witness, visit-floor parameter, fibers, or random
  integral on its right side.
- Local APIs/imports: compiled component rate envelopes, `Nat.le_ceil`,
  positive scale/square-root/division order, `Nat.find_min'`, checkpoint
  monotonicity, ENNReal finiteness, and `ENNReal.toReal_mono`.
- Proof route: combine the burn-in, logarithmic, and return-radius terms into
  a reciprocal-linear envelope; invert it at the fixed threshold; compare the
  least witness; enlarge only the initial checkpoint square in the accepted
  finite weighted budget; substitute the resulting real bound into the
  compiled stopped-value theorem.
- Regularity contracts: the scalar route uses only finite MDP parameters and
  one fixed index. The terminal preserves the exact generated probability/
  Standard-Borel/MGF/support/indexing/centering/normalization/behavior
  contracts, positive proxy/floor, bounded means, and `4 < horizon`.
- Retrieval/status: no prior explicit-ceiling card; exact local rate and
  canonical-start APIs plus Mathlib order/sqrt/integral APIs retrieved;
  `leanCompiled` with fifteen declarations and four external canaries.
- Failure policy: the remaining deterministic weighted failure `tsum` is
  finite but not numerically evaluated. Do not infer a uniform-in-index
  moment, UI/L1 convergence, optional stopping, raw episodes,
  behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Deterministic Stopping-Round Second-Moment Bound

- Lean statement: a canonical checkpoint start is chosen after the scheduled
  regret envelope is permanently below the fixed inverse-sqrt threshold; the
  actual squared successor stopping round is bounded by the squared start
  checkpoint plus the seventh-degree weighted exact model/return budget. The
  stopped regret therefore has a deterministic absolute first-moment bound
  containing neither stopping fibers nor an unevaluated random integral.
- Local APIs/imports: deterministic rate `Tendsto`, positive threshold,
  `Nat.find`, compiled delayed-event inclusion and violation budget,
  checkpoint telescope, `lintegral_tsum`, `lintegral_indicator_const`,
  weighted-budget summability, `integral_eq_lintegral_of_nonneg_ae`, and
  `ENNReal.toReal_mono`.
- Proof route: select and specify the canonical tail start, transport every
  later delayed event to its failure budget, integrate the squared-checkpoint
  layer cake, prove the ENNReal budget finite under `4 < horizon`, convert to
  the Bochner second moment, and substitute it into the prior stopped-value
  theorem.
- Regularity contracts: probability measure and measurable stopping value for
  the generic bridge; inherited exact RL probability/Standard-Borel/MGF/
  support/indexing/centering/normalization/behavior contracts, positive
  proxy/floor, bounded means, `4 < horizon`, and fixed `scheduleIndex`.
- Retrieval/status: no pre-existing memory card; exact local and Mathlib APIs
  found; generic/source/endpoint declarations and external canary compile.
- Failure policy: the explicit child above bounds the canonical `Nat.find`
  start. Preserve this parent interface and do not infer a uniform moment,
  UI/L1 convergence, optional stopping, raw episodes, behavior=recommended
  equality, or complete UCB-VI.

## Closed Gap: Stopping-Round Second-Moment Absolute First-Moment Bound

- Lean statement: the squared-successor-index real fiber sum equals the
  actual stopping-round second moment; hence the square-root fiber-mass sum is
  at most one half of that moment plus the universal shifted inverse-square
  series. The exact fixed-index inverse-sqrt RL consumer retains integrability
  and names the resulting absolute first-moment budget.
- Local APIs/imports: `UnboundedStoppingTimeL2CoordinateIntegrability`,
  `ENNReal.tsum_toReal_eq`, `integral_eq_lintegral_of_nonneg_ae`, shifted
  `Real.summable_one_div_nat_pow`, `Summable.tsum_add`, `tsum_mul_left`, the
  compiled fiber/Holder bridge, uniform RL moments, and L2 hit parent.
- Proof route: decompose squared rounds in ENNReal, take `toReal` under
  finite second moment, identify the Bochner integral, sum Young's pointwise
  inequality, compose with the existing absolute stopped-value theorem, and
  instantiate the exact source.
- Regularity contracts: finite measure; measurable/a.e.-finite tau; `MemLp 2`
  rounds and coordinates; uniform coordinate second moment; inherited exact
  RL contracts and `4 < horizon`; fixed `scheduleIndex`; no independence or
  optional stopping.
- Retrieval/status: exact local and Mathlib APIs found; weighted identities,
  generic quantitative bridge, named budget, RL terminal, and external canary
  compile.
- Failure policy: the actual stopping-round second moment remains fixed-index
  and unevaluated. It is not a schedule-index rate, uniform moment estimate,
  uniform integrability, L1 convergence, raw-episode theorem,
  behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Stopping-Fiber Absolute First-Moment Bound

- Lean statement: a measurable a.e.-finite stop with L2 successor rounds and
  uniformly L2 coordinates satisfies
  `integral |stoppedValue| <= sqrt(envelope) * tsum sqrt(real fiber mass)`;
  the exact fixed-index inverse-sqrt RL consumer retains integrability and
  names this RHS.
- Local APIs/imports: `UnboundedStoppingTimeL2CoordinateIntegrability`, local
  indicator Holder, compiled fiber square-root summability,
  `integral_tsum_of_summable_integral_norm`, `Summable.tsum_le_tsum`, uniform
  RL coordinate moments, and the square-integrable hit/expected-bound parents.
- Proof route: restrict absolute coordinates to equality fibers, apply
  Holder, sum the fiber costs, identify the a.e. stopped-value series, and
  instantiate the exact generated source.
- Regularity contracts: finite measure; measurable/a.e.-finite tau; `MemLp 2`
  rounds and coordinates; uniform second moment; inherited exact RL contracts
  and `4 < horizon`; no independence or optional stopping.
- Retrieval/status: no prior `integral_abs_stoppedValue` declaration; exact
  local/Mathlib APIs found; generic/RL modules and external canary compile.
- Failure policy: the RHS is fixed-index and explicit. It is not a
  schedule-index absolute-moment rate, uniform integrability, L1 convergence,
  raw-episode theorem, behavior=recommended equality, or complete UCB-VI.

## Closed Gap: Unbounded HittingAfter Integrable Expected Upper Bound

- Lean statement: for every fixed inverse-sqrt threshold index under
  `4 < mdp.horizon`, the exact stopped natural-causal average realized
  behavior regret is `Integrable`, and its integral is at most the threshold.
- Local APIs/imports: measurable equality fibers, `lintegral_tsum`,
  `ENNReal.summable_toReal`, shifted inverse-square p-series, Young's
  inequality, the local L2 indicator Holder bound, compiled coordinate
  moments, stopped-value measurability, and the square-integrable hit parent.
- Proof route: L2 rounds give finite squared-index-weighted fiber mass; Young
  gives summable square-root fiber masses; Holder sums uniformly L2
  deterministic coordinates into an integrable unbounded `stoppedValue`;
  finite-hit `Set.Iic` membership then integrates to the threshold bound.
- Regularity contracts: exact dependent causal source; finite nonempty
  Standard Borel spaces; probability law; positive proxy/floor; bounded
  means; selected-reward sub-Gaussianity; support; exact indexing, centering,
  normalization, and behavior semantics; explicit `4 < horizon`.
- Retrieval/status: exact local/Mathlib retrieval; `leanCompiled` with seven
  declarations, root import, external generic-MDP canary, clean placeholders,
  and baseline-only axiom reports.
- Failure policy: fixed index only; no expected nonnegativity, absolute-moment
  rate, uniform integrability/L1 convergence, optional stopping, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Unbounded HittingAfter Fixed-Index Second Moment

- Lean statement: for every fixed inverse-sqrt threshold index and
  `4 < mdp.horizon`, the genuine uncapped Mathlib `hittingAfter` satisfies
  `OFUL.SquareIntegrableFiniteStoppingTime source.trajectoryMeasure tau`.
- Local APIs/imports: the compiled first-moment/delayed-checkpoint route;
  `OFUL.SquareIntegrableFiniteStoppingTime`; `memLp_two_iff_integrable_sq`;
  `Finset.notMemRangeEquiv`, ENNReal product `tsum`, antidiagonal p-series,
  polynomial-exponential summability, indicators, and `lintegral_tsum`.
- Proof route: square fourth-power checkpoint values and bound consecutive
  gaps by `16*(n+2)^7`; use horizon at least five for inverse-tenth local
  shares; reduce the seventh-weighted shifted model tails to an inverse-cube
  pair envelope; add the exponential return share; integrate the squared
  delayed-indicator domination; package `MemLp 2` with prior a.e. finiteness.
- Regularity contracts: exact dependent causal source; finite nonempty
  Standard Borel spaces; probability initial law; positive proxy and visit
  floor; bounded means; selected-reward uniform sub-Gaussian law; exploratory
  support/floor; exact indexing, centering, normalization, and behavior
  semantics; explicit `4 < mdp.horizon`. No event independence or optional
  stopping is added.
- Retrieval/status: exact local/Mathlib retrieval; `leanCompiled` with 17
  declarations, root import, generic external final-contract canary, clean
  placeholders, and three baseline-only critical axiom reports. Independent
  local checks confirmed the event direction and horizon boundary.
- Failure policy: for horizon at most four, retain the compiled first-moment
  theorem; inverse-sixth local shares do not justify the seventh-weighted
  model sum. The result is fixed-index L2 regularity, not a uniform moment
  rate, stopped-process L1 theorem, exponential tail, optional-stopping
  identity, raw-episode result, behavior=recommended equality,
  minimax/reachability, or complete UCB-VI.

## Closed Gap: Unbounded HittingAfter Fixed-Index First Moment

- Lean statement: for every fixed inverse-sqrt threshold index, the genuine
  uncapped Mathlib `hittingAfter` satisfies
  `OFUL.IntegrableFiniteStoppingTime source.trajectoryMeasure tau`.
- Local APIs/imports: fourth-power checkpoints and explicit burn-in-tail/
  return budgets; `Finset.notMemRangeEquiv`, `ENNReal.tsum_sigma`, Nat
  antidiagonals, p-series and polynomial-exponential summability;
  `hittingAfter_le_of_mem`, `lintegral_tsum`, indicator integration, measurable
  `WithTop.untopA`, and the compiled fixed-index a.e.-finiteness parent.
- Proof route: bound each checkpoint gap by `4*(n+2)^3`; reindex shifted model
  tails and use positive horizon for an inverse-sixth-power charge; combine
  the resulting p-series with the exponential return share; eventually embed
  delayed checkpoints in the compiled regret violation; integrate the
  weighted delayed indicators and package the first moment with a.e.
  finiteness.
- Regularity contracts: exact dependent causal source; finite nonempty
  Standard Borel spaces; probability initial law; positive horizon, proxy,
  and visit floor; bounded means; selected-reward uniform sub-Gaussian law;
  exploratory support/floor; exact indexing, centering, normalization, and
  behavior semantics. No independence or optional stopping is added.
- Retrieval/status: exact local and Mathlib declaration retrieval;
  `leanCompiled` with 21 declarations, root import, concrete final-contract
  canary, clean placeholders, and four baseline-only axiom reports.
  Independent local checks found no P0-P3 issue.
- Failure policy: fixed-index first-moment regularity is not a uniform moment
  rate, second moment, exponential crossing tail, L1/UI stopped-process
  theorem, optional-stopping identity, raw-episode result,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI.

## Closed Gap: Unbounded HittingAfter A.E. Finiteness And In-Measure Consistency

- Lean statement: Mathlib `hittingAfter` searches the exact natural average
  realized behavior-regret process below `1/sqrt(n+1)` from `(n+1)^4` with
  no finite cap. Each fixed hit is finite a.e.; all schedule indices are
  finite on one a.e. set; a.e. the hits eventually equal their bases; the
  stopped process converges a.e. and in measure.
- Local APIs/imports: `hittingAfter`, `le_hittingAfter`,
  `hittingAfter_le_of_mem`, `hittingAfter_mem_set_of_ne_top`,
  `hittingAfter_eq_top_iff`, `Adapted.isStoppingTime_hittingAfter`,
  `ae_all_iff`, `tendstoInMeasure_of_tendsto_ae`; compiled all-prefix,
  diverging-stopping-time, and inverse-sqrt summable-delay parents.
- Proof route: expose lower/base/hit/stopping semantics; use all-prefix a.e.
  convergence and threshold positivity for fixed-index finiteness; combine
  the countable family with `ae_all_iff`; use the summable-delay parent for
  eventual base equality; transfer base divergence through `untopA`; invoke
  the generic stopped a.e. theorem and then convergence in measure.
- Regularity contracts: exact dependent causal source, finite nonempty
  Standard Borel spaces, probability initial law, inherited MGF/support/
  bounded-mean/indexing/centering/normalization/behavior assumptions. No
  independence or optional-stopping premise is added.
- Retrieval/status: exact search returned no uncapped local hit; exact
  Mathlib hitting-time APIs and compiled local parents were retrieved.
  Status is `leanCompiled` with 12 declarations, root import, direct canaries,
  clean placeholders, and 11 baseline-only theorem axiom reports. Independent
  review's initial P3 semantic-canary gap was repaired and follow-up review
  confirmed no P0-P3.
- Failure policy: a.e. finiteness is not pointwise finiteness and does not
  imply expected delay, crossing tails or moments, L1/UI, optional stopping,
  raw episodes, behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Inverse-Sqrt First-Passage Summable Delay And Eventual Immediate Stopping

- Lean statement: use threshold `1/sqrt(n+1)` in the capped first-passage
  scan over `[(n+1)^4,(n+1)^4+(2*n+1)]`. The delay probabilities have
  finite total mass, so almost every generated trajectory eventually stops
  exactly at `(n+1)^4`; the stopped process retains `MemLp 1`,
  expected-absolute, `eLpNorm`, in-measure, and a.e. convergence.
- Local APIs/imports: compiled capped and reciprocal first-passage routes;
  explicit polynomial expected-absolute envelope and Markov distance tail;
  `Real.sqrt_eq_rpow`, `Real.rpow_sub`,
  `Real.summable_one_div_nat_add_rpow`, `ENNReal.tsum_le_tsum`,
  `Summable.tsum_ofReal_ne_top`, and `MeasureTheory.ae_eventually_notMem`.
- Proof route: characterize `base<tau` by the strict base violation; transport
  into the distance event; divide the inverse-cubic/inverse-square L1
  envelope by `1/sqrt(n+1)`; normalize to inverse-`5/2` and inverse-`3/2`
  shifted p-series; prove finite ENNReal delay mass; apply first
  Borel-Cantelli; combine eventual non-delay with `base<=tau`.
- Regularity contracts: preserve the exact dependent causal source and all
  inherited Standard Borel/probability/MGF/support/bounded-mean/indexing/
  centering/normalization/behavior contracts. First Borel-Cantelli adds no
  event independence or optional-stopping premise.
- Retrieval/status: exact calibration search returned no hit; exact local
  first-passage/L1/Markov/Borel-Cantelli precedents and Mathlib shifted
  p-series/rpow/ENNReal APIs were retrieved. Status is `leanCompiled` with
  twenty declarations, root import, and direct summability/finite-mass/
  eventual-base/root canaries. The placeholder scan is clean, all fifteen
  public theorem axiom reports are baseline-only, and independent review's
  initial P3 canary gap was closed; no P0-P3 findings remain.
- Failure policy: the almost-sure conclusion is along this scheduled family.
  It does not provide a deterministic eventual index, pointwise
  all-trajectory stopping, uncapped `hittingAfter`, expected delay,
  exponential crossing tails, optional stopping, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Reciprocal-Threshold First-Passage Vanishing Delay Probability And L1 Consistency

- Lean statement: use threshold `1/(n+1)` in the capped first-passage scan
  over `[(n+1)^4,(n+1)^4+(2*n+1)]`. The probability that the scan advances
  past its base tends to zero, while the stopped process retains `MemLp 1`,
  expected-absolute and `eLpNorm 1` convergence, in-measure convergence,
  and a.e. convergence.
- Local APIs/imports: compiled finite first-passage semantics and L1 terminal;
  explicit polynomial-prefix expected-absolute and summable L1 envelopes;
  scheduled Markov distance tail; scale atTop limits; `measure_mono`,
  `ENNReal.ofReal_le_ofReal`, and `ENNReal.tendsto_ofReal`.
- Proof route: prove `base<tau` iff the base process strictly exceeds
  `1/(n+1)`; embed this event in the absolute-distance violation; apply
  Markov; divide the exponent-three/exponent-two envelope by the reciprocal
  threshold to obtain inverse-square plus inverse-linear decay; squeeze the
  ENNReal probability; append the compiled stopped L1 parent.
- Regularity contracts: preserve the exact dependent causal source and all
  inherited Standard Borel/probability/MGF/support/bounded-mean/indexing/
  centering/normalization/behavior contracts. The concentration step is
  first-moment Markov and adds neither independence nor optional stopping.
- Retrieval/status: exact calibration search returned no hit; exact local
  first-passage, scheduled L1/Markov, and asymptotic declarations were
  retrieved. Status is `leanCompiled`: sixteen declarations, root import,
  and external threshold/delay/subset/rate/Markov/probability/root-`MemLp`
  canaries compile. All theorem axioms are baseline-only, and independent
  read-only review found no P0-P3 issue.
- Failure policy: vanishing delay probability does not imply finite-index
  immediate stopping, summable delay probabilities, eventual immediate
  stopping a.s., uncapped `hittingAfter`, crossing-time moments, exponential
  crossing tails, raw episodes, behavior=recommended, minimax/reachability,
  or complete UCB-VI.

## Closed Gap: Capped Double-Linear Raw-Window First-Passage Stopping-Time L1 Consistency

- Lean statement: at index `n`, Mathlib `hittingBtwn` scans the exact natural
  average realized behavior-regret process from `(n+1)^4` through
  `(n+1)^4+(2*n+1)`. It returns the first prefix at or below deterministic
  `threshold n`, or the right endpoint when no earlier prefix hits. The
  resulting stopped process converges in expected absolute value,
  `eLpNorm 1`, in measure, and almost everywhere.
- Local APIs/imports: the compiled strongly-adapted natural process;
  `MeasureTheory.hittingBtwn`; its first-hit, no-prior-hit, interval, and
  stopping-time lemmas; the local `BudgetStoppingTime` precedent; the
  double-linear candidate-rate theorem; and the generic rate-controlled
  raw-window L1 terminal.
- Proof route: construct the finite hitting time for `Set.Iic (threshold n)`;
  expose exact candidate/base/fallback and before/at-stop certificates; apply
  `Adapted.isStoppingTime_hittingBtwn`; transport the closed-window bounds to
  `WithTop Nat`; then specialize the generic L1 terminal.
- Regularity contracts: preserve the exact dependent source and inherited
  Standard Borel/probability/MGF/support/bounded-mean/indexing/centering/
  normalization/behavior contracts. The deterministic threshold has no sign,
  monotonicity, calibration, or limiting premise. No independence or optional
  stopping is added.
- Retrieval/status: the local search found only the previous two-endpoint
  non-first-passage card; Mathlib hitting-time source, local precedent, and
  exact parent declarations were then retrieved. Status is `leanCompiled`:
  eleven declarations, root import, and external semantic/stopping/`MemLp`/
  expected/`eLpNorm`/in-measure/a.e. canaries compile. Independent review
  found no P0-P3 findings, and representative axioms are baseline only.
- Failure policy: a strict pre-cap stop is a threshold hit, but a stop at the
  cap may be either a hit or the no-earlier-hit fallback. Do not infer a hit
  at the cap, crossing probability, an uncapped `hittingAfter` theorem,
  trajectory-dependent thresholds, optional stopping, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Threshold-Triggered Double-Linear Raw-Window Stopping-Time L1 Consistency

- Lean statement: at index `n`, compare the exact natural average realized
  behavior-regret process at `(n+1)^4` with a deterministic threshold. Stop
  there on `process<=threshold`; otherwise stop `2*n+1` raw prefixes later.
  This rule is an exact-natural-filtration stopping time and its full stopped
  process converges in expected absolute value, `eLpNorm 1`, in measure, and
  almost everywhere.
- Local APIs/imports: compiled strong adaptation of the natural process;
  `measurableSet_le`; Mathlib `isStoppingTime_piecewise_const`; the
  explicit double-linear candidate-rate theorem; and the generic
  rate-controlled raw-window L1 terminal.
- Proof route: make the base threshold event measurable, construct the
  two-constant piecewise stopping rule, prove both branches and pointwise
  window bounds, then specialize the generic parent with base `(n+1)^4`
  and width `2*n+1`.
- Regularity contracts: preserve the exact dependent source and inherited
  Standard Borel/probability/MGF/support/bounded-mean/indexing/centering/
  normalization/behavior contracts. The threshold is deterministic but needs
  no sign or limit. No independence or optional stopping is added.
- Retrieval/status: exact threshold-triggered memory no-hit; exact local
  declarations and Mathlib's piecewise-constant stopping constructor were
  retrieved. Status is `leanCompiled`: nine declarations, root import, and
  external branch/stopping/`MemLp`/expected/`eLpNorm`/in-measure/a.e.
  canaries compile. Independent review found no P0-P3 findings and confirmed
  baseline-only axioms.
- Failure policy: this is a one-shot choice between two endpoints after the
  base observation, not a first-passage threshold time. Do not infer
  trajectory-dependent thresholds, arbitrary widths/candidate sets, optional
  stopping, raw episodes, behavior=recommended, minimax/reachability, or
  complete UCB-VI; the conditional branch canaries do not prove positive
  probability for either branch.

## Closed Gap: Rate-Controlled Raw-Window Stopping-Time L1 Consistency

- Lean statement: for deterministic positive `baseRounds` and `windowWidth`,
  every exact-natural-filtration stopping prefix satisfying
  `baseRounds n <= tau_n <= baseRounds n+windowWidth n` has vanishing expected
  absolute natural average realized behavior regret when
  `((windowWidth n+1)/sqrt(baseRounds n))->0`. The terminal also returns
  stopped `MemLp 1`, explicit budget/rate bounds, `eLpNorm`, in-measure, and
  a.e. convergence.
- Local APIs/imports: the compiled `D/sqrt rounds` all-prefix majorant;
  `Real.sqrt_le_sqrt`; ordered division; `Finset.sum_const`; `Tendsto.mul`;
  the WithTop finite-window selector; stopped `MemLp`; finite-sum integration;
  exponent-one norm, in-measure, and stopped a.e. parents.
- Proof route: each of the `windowWidth n+1` raw candidates costs at most
  `D/sqrt(baseRounds n)`. Sum these costs, consume the explicit candidate
  ratio, select and integrate the stopped coordinate, and transport the
  expected-absolute limit to `eLpNorm 1` and in measure. The separate
  `n<=baseRounds n` contract supplies the a.e. lower envelope.
- Regularity contracts: preserve the exact dependent source and all inherited
  Standard Borel/probability/MGF/support/bounded-mean/indexing/centering/
  normalization/behavior contracts. Require positive bases, the candidate
  ratio limit, `n<=baseRounds n`, one exact stopping time per index, and both
  pointwise window bounds; no independence or optional stopping is added.
- Retrieval/status: the explicit raw-window parent and exact declarations were
  retrieved, together with recorded Mathlib/RL cards; weapon evidence remains
  inspiration only. Status is `leanCompiled`: nineteen declarations, root
  import, and an external trajectory-dependent width-`2n+1` endpoint canary directly pin
  `MemLp`, budget/rate, expected-absolute convergence, `eLpNorm`, in-measure,
  and a.e. outputs. Independent review found no P0/P1; all P2/P3 record and
  canary findings are closed.
- Failure policy: base divergence alone does not replace the candidate-ratio
  limit, and the a.e. conclusion still needs a diverging lower envelope. Do
  not infer optional stopping, arbitrary finite candidate sets, arbitrary
  diverging-stop L1, raw episodes, behavior=recommended, minimax/reachability,
  or complete UCB-VI.

## Closed Gap: Polynomial-Base Growing Raw-Window Stopping-Time L1 Consistency

- Lean statement: every exact-natural-filtration stopping prefix satisfying
  `explicitRounds n <= tau_n <= explicitRounds n+n`, where
  `explicitRounds n=(n+1)^4`, has expected absolute natural average realized
  behavior regret tending to zero. The terminal also returns stopped
  `MemLp 1`, the explicit budget and rate, `eLpNorm`, in-measure, and a.e.
  convergence.
- Local APIs/imports: `Real.log_le_sub_one_of_pos`, `Real.log_sqrt`,
  `Real.sq_sqrt`, `Real.sqrt_le_sqrt`, the compiled all-prefix L1 and
  fixed-window selector/MemLp parents, `Finset.sum_const`, both finite-sum
  integral wrappers, and the stopping a.e. parent.
- Proof route: majorize `C(1+log r)/r` and the return first moment by one
  `D/sqrt r`; every raw coordinate after `(n+1)^4` then costs at most
  `D/(n+1)^2`. Sum all `n+1` contiguous candidates to obtain
  `D/(n+1)->0`, select the stopped offset through WithTop bounds, and
  transport the resulting expected-absolute limit to L1 and in measure.
- Regularity contracts: preserve the exact dependent source, inherited
  Standard Borel/probability/MGF/support/bounded-mean contracts, indexing,
  centering, normalization, and behavior semantics. Require one exact
  stopping time and both pointwise raw-window bounds per index; no independence
  or optional stopping is added.
- Retrieval/status: exact no-hit, compiled local parents, recorded Mathlib and
  RL cards, and weapon inspiration only. Status is `leanCompiled`: twenty-two
  declarations, root import, and a trajectory-dependent canary that reaches
  both raw endpoints and directly pins `MemLp`, budget/rate, `eLpNorm`,
  in-measure, and a.e. terminals. Independent review found no P0-P2; its P3
  canary request is closed.
- Failure policy: this concrete route is now subsumed by the parameterized
  rate-controlled raw-window theorem. Do not infer candidate sets outside a
  contiguous interval, arbitrary diverging-stop L1, optional stopping,
  raw episodes, behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Growing-Window Grid Stopping-Time L1 Consistency

- Lean statement: if `windowAt n -> infinity` and every exact-natural-
  filtration stopping prefix is pointwise one of
  `explicitHighProbabilityRounds (n+offset)` for `offset <= windowAt n`, then
  expected absolute stopped natural average realized behavior regret tends to
  zero. The terminal also returns stopped `MemLp 1`, `eLpNorm` convergence,
  convergence in measure, and almost-everywhere convergence.
- Local APIs/imports: the compiled summable fourth-power-prefix L1 envelope;
  `summable_nat_add_iff`; `Summable.sum_le_tsum`; `tendsto_sum_nat_add`;
  `memLp_stoppedValue`; both project finite-sum integral wrappers; the
  exponent-one norm identity; in-measure transport; and the stopping a.e.
  parent.
- Proof route: extract the finite grid offset and its finite endpoint bound;
  dominate its absolute coordinate by the finite candidate sum; integrate and
  apply the explicit-grid envelope; dominate every such finite sum by the full
  shifted summable tail. Then identify `eLpNorm 1`; grid growth in the base
  index gives the a.e. stopping lower bound.
- Regularity contracts: preserve the exact finite Standard Borel dependent
  source, selected-reward sub-Gaussian law, bounded means, support/floor,
  indexing, centering, normalization, and behavior semantics. Require one
  exact stopping time per index, pointwise sparse-grid membership, and
  `windowAt -> infinity`; no independence is added.
- Retrieval/status: exact no-hit, compiled parent/Mathlib APIs, recorded cards,
  and weapon inspiration only. Status is `leanCompiled`: eighteen
  declarations, root import, and a trajectory-dependent width-`n` canary that
  selects both left and right grid endpoints.
- Failure policy: arbitrary candidate-count growth is proved only on the
  summable fourth-power grid. Do not infer an arbitrary raw-prefix growing
  interval, arbitrary diverging-stopping L1, optional stopping, a sharper
  rate, raw episodes, behavior=recommended, minimax/reachability, or complete
  UCB-VI.

## Closed Gap: Fixed-Window Stopping-Time L1 Consistency

- Lean statement: for exact-natural-filtration stopping times satisfying one
  pointwise fixed window `n+1 <= tau_n <= n+1+window`, expected absolute
  stopped natural average realized behavior regret tends to zero. The terminal
  also returns stopped `MemLp 1`, `eLpNorm` convergence, convergence in
  measure, and almost-everywhere convergence on the exact trajectory measure.
- Local APIs/imports: the all-prefix L1 envelope and its limit, the stopping
  a.e. parent, `memLp_stoppedValue`, `MemLp.eLpNorm_eq_integral_rpow_norm`,
  `tendsto_finset_sum`, `tendsto_add_atTop_nat`,
  `tendstoInMeasure_of_tendsto_eLpNorm`, and both project finite-sum integral
  wrappers.
- Proof route: eliminate `top` using the finite upper bound; write `untopA` as
  `n+1+offset` with `offset < window+1`; charge its absolute value to the finite
  coordinate sum; integrate, apply coordinate envelopes, and compose their
  limits with fixed shifts. Then identify `eLpNorm 1` and reuse the lower-bound
  stopping-time a.e. theorem.
- Regularity contracts: preserve the exact finite Standard Borel dependent
  causal source, selected-reward sub-Gaussian law, bounded means,
  support/floor, natural indexing, normalization, and behavior semantics.
  Every `tau_n` is an exact-natural-filtration stopping time and the same
  deterministic pointwise window bounds all `n`; no independence is added.
- Retrieval/status: exact no-hit, compiled parent/Mathlib APIs, recorded cards,
  and weapon inspiration only. Status is `leanCompiled`: twelve declarations,
  root import, and an external deterministic `tau_n=n+1` canary.
- Failure policy: no envelope monotonicity or optional-stopping identity is
  used. The downstream sparse-grid growing-window route is separate. Do not
  infer raw-prefix growing-window/arbitrary-stopping L1 convergence, a sharper
  rate than the explicit shifted finite sum, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Closed Gap: Deterministic-Moment Expected Bounded-Stopping Regret

- Lean statement: for one exact-natural-filtration stopping time with
  `1 <= tau <= T`, the exact stopped average realized behavior-regret second
  moment is at most a deterministic sum of positive-prefix envelopes. The
  fixed-quarter overflow is at most `(1/2) * sqrt(momentBudget)`, and expected
  stopped regret is at most the finite logarithmic-rate budget plus that term.
- Local APIs/imports: the new
  `Concentration.integral_sq_le_four_mul_proxy_mul_exp_half_of_hasSubgaussianMGF`,
  the cumulative behavior `rounds * (2*horizon)` bound, the exact process
  identity, `MemLp.integrable_sq`, `Finset.single_le_sum`,
  `IntegrabilitySums.integrable_finset_sum`,
  `ExpectationBochnerSums.integral_finset_sum`, and the exact-moment parent.
- Proof route: derive a conservative MGF second moment; bound every positive
  coordinate by behavior-square plus normalized deviation-square; select the
  stopped coordinate inside the finite `Icc 1 T` square sum; integrate and
  sum; apply `Real.sqrt_le_sqrt` to both parent bounds.
- Regularity contracts: retain the exact finite Standard Borel dependent
  causal source, bounded means, selected-reward sub-Gaussian law,
  support/floor, normalization, indexing, and centering. Coordinate bounds
  require positive rounds; stopping requires exact `IsStoppingTime` and
  pointwise `1 <= tau <= T`; no independence is added.
- Retrieval/status: exact no-hit; compiled local/Mathlib APIs and recorded
  cards, with OFUL/weapon evidence used only as route inspiration. Status is
  `leanCompiled`: nine declarations across `ConcentrationSubGaussian` and the
  root-imported RL module, plus external moment and expected-bound canaries.
- Failure policy: do not claim the sharper `E[X^2] <= c`, endpoint
  monotonicity, optional stopping, or nonnegative expected realized regret.
  The finite deterministic sum may grow with `T`; asymptotic expected rate,
  arbitrary confidence, unbounded stopping, raw episodes,
  behavior=recommended, minimax/reachability, and complete UCB-VI remain open.

## Closed Gap: Exact-Moment Expected Bounded-Stopping Regret

- Lean statement: for one exact-natural-filtration stopping time with
  `1 <= tau <= T`, the stopped average realized behavior regret is in `L2`.
  Its bad-event absolute integral is at most
  `(1/2) * sqrt(exact stopped second moment)`, and its expectation is at most
  the finite `Icc 1 T` logarithmic-rate sum plus that overflow. The same
  theorem retains the `1/4` bad tail, `3/4` good mass, and good-event pathwise
  stopped rate.
- Local APIs/imports: new namespace-neutral `MeasureL2Indicator` wrapper;
  `MemLp.of_bound`, cumulative return `HasSubgaussianMGF.memLp`, exact
  expected-minus-deviation identity, Mathlib `memLp_stoppedValue`,
  `Finset.single_le_sum`, `integral_mono`, and the compiled three-quarter
  parent.
- Proof route: prove deterministic behavior and return coordinates are `L2`;
  transport through bounded stopping; name the exact second moment; convert
  the quarter event tail into a half square-root mass; split paths between the
  bad-event absolute overflow and the good-event stopped rate; integrate.
- Regularity contracts: inherit the exact finite Standard Borel causal source,
  bounded means, selected-reward sub-Gaussian law, support/floor, indexing,
  normalization, and centering contracts; require `0 < horizon`, `0 < T`, and
  pointwise positive bounded exact-filtration `IsStoppingTime`; no independence.
- Retrieval/status: exact no-hit; compiled local parent/process/MGF APIs,
  Mathlib Holder/stopping/integral APIs, recorded cards, and OFUL/weapon
  inspiration only. Status is `leanCompiled`: eleven declarations across two
  root-imported modules, focused builds, and external stopped-`L2`, overflow,
  and expected-integral canaries.
- Failure policy: no optional stopping, no `L1 * probability` shortcut, no
  assumed nonnegative expected realized regret, and no unproved numerical
  second-moment bound. Therefore this is not yet an asymptotic expected rate,
  arbitrary confidence, unbounded stopping, raw episodes, behavior=recommended,
  minimax/reachability, optimal UCB-VI, or complete UCB-VI.

## Closed Gap: Explicit Three-Quarter Bounded-Stopping Good Event

- Lean statement: under the exact natural-causal source and one stopping time
  with `1 <= tau <= T`, the unchanged scheduled finite-prefix model-failure
  budget is at most `ENNReal.ofReal (1/8)`. With return budget `1/8`, the
  measurable joint and stopped bad events have mass at most `1/4`; the joint
  good event has real mass at least `3/4` and carries the stopped logarithmic
  pathwise average realized behavior-regret bound.
- Local APIs/imports: the compiled single-model-event parent;
  `sum_range_one_div_natCast_add_two_pow_le_one`, the scheduled local-delta and
  finite model-budget identities, `ENNReal.ofReal_sum_of_nonneg`,
  `ENNReal.ofReal_add`, and `MeasureTheory.probReal_compl_eq_one_sub`.
- Proof route: dominate exponent-at-least-six shifted powers by `1/16` of the
  inverse-square series; map the real finite sum through `ofReal`; charge the
  two exact model shares to `1/8`; add the return `1/8`; convert the quarter
  event tail into the three-quarter complement mass; reuse parent containment.
- Regularity contracts: all source/support/MGF/indexing/normalization contracts
  are inherited. The numerical bound explicitly needs `0 < mdp.horizon`; the
  terminal also needs `0 < T` and one pointwise positive bounded stopping time.
- Retrieval/status: exact search was a no-hit; evidence is the compiled parent,
  exact local/Mathlib finite-sum and probability-complement APIs, and recorded
  cards. Status is `leanCompiled`: five declarations, root import, focused and
  `Tests.Basic` builds, with the trajectory-dependent one-or-two stopping-time
  canary projecting `1/8`, `1/4`, and `3/4` certificates.
- Failure policy: preserve the exact schedule and fixed confidence split. This
  is not arbitrary caller confidence, optional stopping, stopped expectation,
  unbounded-anytime control, raw episodes, behavior=recommended,
  minimax/reachability, an optimal UCB-VI rate, or complete UCB-VI.

## Closed Gap: Bounded Stopping-Time Single-Model-Event Tail

- Lean statement: for one exact-natural-filtration stopping time with
  pointwise `1 <= tau <= T`, allocate one global return budget `delta` over
  `Finset.Icc 1 T`. The stopped average realized-regret violation is
  filtration-`T` measurable and contained in one horizon-`T` model event plus
  the finite return-only window. Both the joint and stopped event have mass at
  most `modelFailureBudget mdp T + ENNReal.ofReal delta`.
- Local APIs/imports: the compiled bounded-stopping and fixed-prefix parents;
  heterogeneous `finiteHorizonBadEvent`; `Set.mem_iUnion`; `Finset.Icc`,
  `card_pos`, and `measurableSet_biUnion`;
  `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`;
  `measure_union_le`; `measure_mono`.
- Proof route: embed every `Fin r` model-event witness into `Fin T`; use the
  exact unchanged coordinate-event family; divide the return budget by the
  positive-prefix index-card; split each prefix model/return event; transport
  its model branch into `M_T` and union-bound only return branches; compose the
  prior stopped-to-prefix containment.
- Regularity contracts: all finite/Standard-Borel/probability/support/MGF,
  source/indexing/normalization/centering assumptions are inherited. New
  contracts are `0 < T`, one positive bounded `IsStoppingTime`, and
  `0 < delta <= 1`. No independence is used.
- Retrieval/status: exact search was a no-hit; direct evidence is the compiled
  parents, exact local/Mathlib finite-union APIs, and recorded cards. Status is
  `leanCompiled`: thirteen declarations, root import, focused/Tests builds, a
  trajectory-dependent one-or-two-prefix canary, clean placeholders,
  baseline-only axioms, no P0-P3 in independent review, and the full
  `python3 tools/bandit.py check` gate.
- Failure policy: retain the horizon model-failure budget. This is not a
  total-`delta`, optional-stopping, stopped-expectation, unbounded-anytime,
  raw-episode, behavior=recommended, minimax/reachability, optimal-UCB-VI-rate,
  or complete-UCB-VI theorem.

## Closed Gap: Bounded Stopping-Time High-Probability Natural Realized Regret

- Lean statement: for one exact-natural-filtration stopping time satisfying
  pointwise `(1 : WithTop Nat) <= tau <= T`, the exact stopped average realized
  behavior regret and its scheduled logarithmic rate are defined; their
  violation is measurable at filtration level `T`, contained in the positive
  fixed-prefix window, and bounded by the exact sum over `Finset.Icc 1 T` of
  model and return budgets. Every window-good path obeys the stopped rate.
- Local APIs/imports: the compiled natural-filtration stopping parent and
  fixed-prefix high-probability realized parent; `stoppedValue`,
  `stronglyMeasurable_stoppedValue_of_le`, `WithTop.untopA_eq_untop`,
  `Finset.measurableSet_biUnion`, `measure_biUnion_finset_le`, and
  `Finset.sum_le_sum`.
- Proof route: the finite upper bound excludes `top`; both pointwise bounds
  put `tau.untopA` in `Icc 1 T`; progressive measurability gives filtered
  stopped-event measurability; the stopped path chooses its fixed-prefix
  witness; finite subadditivity and the compiled per-prefix event tails yield
  the exact finite sum.
- Regularity contracts: all finite/Standard-Borel/probability/support/MGF,
  source/indexing/normalization/centering assumptions are inherited. New
  contracts are one `IsStoppingTime`, pointwise positive finite bounds, and
  `0 < returnDeltaAt r <= 1` only inside the finite window.
- Retrieval/status: exact route search was a no-hit; evidence is the two
  compiled RL parents, local OFUL bounded-stopping pattern, exact Mathlib
  stopping/finite-union APIs, and the recorded cards. Status is
  `leanCompiled`: fourteen declarations, root import, focused/Tests builds,
  a trajectory-dependent one-or-two-prefix source canary, baseline-only
  representative axioms, and no P0-P3 in independent read-only review.
- Failure policy: preserve the exact finite sum. This is not optional
  stopping, a stopped expectation identity, an unbounded anytime theorem,
  raw episodes, behavior=recommended, minimax/reachability, an optimal UCB-VI
  rate, or complete UCB-VI.

## Closed Gap: Diverging Stopping-Time Almost-Sure Natural Realized Regret

- Lean statement: the exact dependent `Filtration.piLE` natural filtration is
  exposed; the per-batch-normalized, equal-round-weighted natural average
  realized behavior-regret process is `StronglyAdapted`; every Mathlib
  `stoppedValue` at a `WithTop Nat` stopping time is measurable; and any
  schedule whose `untopA` values diverge a.e. on the same causal measure tends
  to zero a.e. A pointwise `n <= tau_n.untopA` terminal is included.
- Local APIs/imports: the compiled diverging-random-prefix parent,
  `Filtration.piLE_eq_comap_frestrictLe`, `Preorder.frestrictLe`,
  `measurable_pi_apply`, `Filtration.mono`, `Finset.measurable_sum`,
  `StronglyAdapted.progMeasurable_of_discrete`, `measurable_stoppedValue`,
  `IsStoppingTime.measurable'`, and `IsStoppingTime.measurableSpace_le`.
- Proof route: prove dependent coordinate evaluation at every later
  filtration level; lift successor-batch reward sums into the finite prefix;
  sum and divide to obtain adaptedness; apply Mathlib stopped-value
  measurability; then transport the compiled all-prefix a.e. limit through the
  measurable Nat-valued `untopA` coordinates.
- Regularity contracts: all finite/Standard-Borel/probability/support/MGF,
  source, successor-indexing, normalization, and centering contracts are
  inherited. New contracts are `IsStoppingTime` at every schedule index and
  a.e. divergence of `tau_n.untopA`, or the stronger pointwise lower envelope.
- Retrieval/status: exact route searches were no-hits; direct evidence is the
  compiled random-prefix parent, Mathlib filtration/stopping source, and local
  OFUL stopping-time patterns. Status is `leanCompiled`: fourteen declarations,
  root import, focused and `Tests.Basic` builds, and an extensionally
  trajectory-dependent source canary whose explicit zero- and one-reward
  trajectories choose `n+1` and `n+2` from the time-zero sampled return.
- Failure policy: this is stopped-subsequence consistency and measurable
  stopped evaluation, not optional stopping, a stopped expectation identity,
  an anytime confidence/rate theorem, raw episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI. Mathlib assigns `top.untopA` an
  arbitrary fixed Nat default, so divergence implies eventual non-`top` but
  permits finitely many `top` values; it cannot be replaced by convergence to
  `top` in `WithTop Nat`.

## Closed Parent: Diverging Random-Prefix Almost-Sure Natural Realized Regret

- Lean statement: on the same heterogeneous causal trajectory measure, any
  coordinatewise measurable random-prefix schedule `tau_n` which tends to
  infinity almost everywhere preserves measurability and the a.e. zero limit
  of the exact per-batch-normalized, equal-round-weighted average realized
  behavior-regret process. A pointwise `n <= tau_n` terminal is included.
- Local APIs/imports: the compiled deterministic all-prefix terminal,
  `measurable_from_prod_countable_left`, `Measurable.prodMk`, `Tendsto.comp`,
  `filter_upwards`, `tendsto_atTop`, and `eventually_ge_atTop`; the local UCB
  arm-stream random-coordinate theorem is implementation-pattern evidence.
- Proof route: make `(trajectory,n) -> X_n trajectory` jointly measurable and
  compose with `trajectory -> (trajectory,tau_n trajectory)`; intersect the
  parent-limit and schedule-divergence full-measure sets and compose limits
  pathwise; derive divergence from `threshold <= n <= tau_n` when requested.
- Regularity contracts: all finite/Standard-Borel/probability/positive
  parameter, bounded-reward, selected-reward MGF, support/floor, filtration,
  source, indexing, normalization, and centering contracts are inherited.
  New contracts are measurable schedule coordinates and a.e. divergence on
  the exact same source measure.
- Retrieval/status: exact search was a no-hit; the compiled parent, local UCB
  pattern, and exact Mathlib countable-product/filter APIs are direct proof
  evidence. Status is `leanCompiled`: eight declarations, root import,
  generic random-Bool and trajectory-dependent Bool/Bool source canaries,
  focused and `Tests.Basic` builds, baseline-only axioms, no placeholders,
  and defect-free independent re-review.
- Failure policy: divergence is essential; bounded or recurrent schedules are
  not accepted. This is random-subsequence transport, not optional stopping,
  a stopping-time or anytime rate, raw online episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI.

## Closed Parent: All-Prefix Almost-Sure Equal-Round Natural Realized Regret

- Lean statement: on the one heterogeneous self-consistent causal trajectory
  measure, every coordinate of the exact per-batch-normalized,
  equal-round-weighted natural average realized behavior-regret process is
  measurable, and the process tends to zero almost everywhere over all
  deterministic natural prefixes.
- Local APIs/imports: the compiled successor-policy expected-regret a.e.
  theorem, `Filter.Tendsto.cesaro`, the fixed-prefix normalized-return tail,
  the linear cumulative proxy bound, `subGaussianSumConfidenceRadius_sq`,
  shifted real p-series, ENNReal tsum comparison, `ae_eventually_notMem`,
  `tendsto_add_atTop_iff_nat`, and the exact expected-minus-deviation identity.
- Proof route: use pathwise Cesaro for the behavior term; at rounds `n+1` use
  return share `1/(n+2)^2`; bound its divided radius by
  `sqrt(6*(C+1)*(1+log(n+2))/(n+1))`; sum event measures; apply first
  Borel-Cantelli without independence; remove the shift and subtract the two
  pathwise zero limits.
- Regularity contracts: finite nonempty Standard Borel State/Action with
  equality and measurable singletons, probability initial law, positive
  horizon/base floor/proxy, bounded rewards, uniform selected-reward
  sub-Gaussianity, exploratory support/floor, and inherited filtration/global
  return measurability. Prefixes are deterministic; there is no stopping-time
  or event-independence premise.
- Retrieval/status: exact search was a no-hit; compiled local parents and
  Mathlib probability/measure/asymptotic APIs are proof evidence. The textbook,
  UCB-VI paper, scenario, and tail weapon remain placement/inspiration only.
  Status is `leanCompiled`: 21 declarations, root import, Bool/Bool canaries,
  focused and `Tests.Basic` builds, baseline-only axioms, clean placeholders.
- Failure policy: preserve the one dependent source, `t -> t+1`, each batch's
  own positive-count normalization before equal round averaging, and global
  centering. This is all deterministic prefixes a.s., not an anytime
  confidence sequence, random stopping-time theorem, raw episode process,
  behavior/recommended-policy equality, minimax/reachability, or complete
  UCB-VI.

## Closed Gap: Explicit Polynomial-Prefix Almost-Sure Equal-Round Consistency

- Lean statement: on deterministic prefixes `(n + 1)^4`, the exact
  per-batch-normalized, equal-round-weighted average realized behavior-regret
  process is measurable and tends to zero almost everywhere under the one
  heterogeneous dependent causal trajectory measure.
- Local APIs/imports: the compiled all-prefix L1 expected-absolute bound, the
  explicit schedule/process/distance-event APIs, shifted p-series summability,
  Markov's inequality, integral/`lintegral` and Real/ENNReal bridges,
  `MeasureTheory.ae_eventually_not_mem`, and reciprocal-natural thresholds.
- Proof route: specialize the behavior term to `C3/(n+1)^3` and the normalized
  return first moment to `C2/(n+1)^2`; sum the deterministic L1 envelope and
  expected absolute process; apply Markov at every fixed positive threshold;
  invoke first Borel-Cantelli; intersect the reciprocal thresholds and use
  `exists_nat_one_div_lt` to obtain pathwise convergence.
- Regularity: inherited finite nonempty Standard Borel State/Action,
  probability, positive horizon/floor/proxy, bounded rewards, uniform
  selected-reward sub-Gaussianity, support/floor, filtration and global-return
  measurability. No independence or stopping-time premise is added.
- Retrieval/status: exact search was a no-hit; compiled local L1/schedule APIs
  and Mathlib summability/measure APIs are direct evidence. The 21-declaration
  module, root import, and Bool/Bool terminal canaries compile; independent
  review found no defect, representative axioms are baseline-only, and the
  placeholder scan and full `tools/bandit.py check` are clean.
- Failure policy: preserve `(n+1)^4`, one source, global centering, and each
  batch's own normalization before equal round weights. This is sparse-prefix
  a.e. convergence and is now consumed by the all-prefix route above; it is
  not anytime/stopping-time, raw-episode,
  minimax, reachability, behavior=recommended-policy, or complete UCB-VI.

## Closed Gap: All-Prefix L1 Equal-Round Natural Realized Regret

- Lean statement: on the one heterogeneous dependent causal trajectory
  measure, the exact natural average realized behavior-regret process which
  normalizes each successor batch by its own count and then weights rounds
  equally is integrable and `MemLp 1` for every deterministic prefix. Its
  expected absolute value, exponent-one `eLpNorm`, and named `Lp Real 1`
  value tend to zero; `TendstoInMeasure` follows.
- Local APIs/imports: natural successor-average return increments,
  `Filtration.piLE`, `StronglyAdapted`, conditional-MGF sum, the local MGF
  first-moment theorem, linear cumulative variance-proxy bound, `Real.sqrt`
  order/asymptotics, exact expected-minus-deviation identity, expected-process
  integrability/nonnegativity/integral and logarithmic rate, and Mathlib
  integral/`MemLp`/`eLpNorm`/`Lp`/in-measure APIs.
- Proof route: expose the global MGF already internal to the fixed-prefix tail;
  bound the divided return first moment by a constant over `sqrt rounds`;
  integrate `|(E-D)/rounds| <= E/rounds + |D|/rounds`; combine the compiled
  `log(rounds)/rounds` and inverse-square-root limits; package `L1`.
- Regularity: inherited finite nonempty Standard Borel State/Action,
  probability, positivity, bounded reward, selected-reward uniform
  sub-Gaussian, support/floor, filtration and global-return measurability
  contracts. No independence, summability, or stopping-time premise is added.
- Retrieval/status: exact search was a no-hit; compiled local and Mathlib
  measure/order/log-sqrt/asymptotic APIs are direct evidence. The 23-declaration
  module, root import, and Bool/Bool canaries compile; representative axioms
  are baseline-only and there are no placeholders.
- Failure policy: preserve `t -> t+1`, per-batch normalization followed by
  equal round weights, one source, and global initial-law centering. The old
  L1 process is total-episode-mass-weighted and is pattern evidence only. This
  is not almost-sure, anytime/stopping-time, raw-episode, minimax,
  reachability, behavior=recommendation, or complete UCB-VI.

## Closed Gap: Explicit Polynomial-Prefix Absolute In-Measure Consistency

- Lean statement: the equal-round-weighted natural average realized
  behavior-regret process at `rounds n = (n+1)^4` is measurable and tends to
  zero in Mathlib `TendstoInMeasure`. For every `epsilon > 0`, its measurable
  distance event `{epsilon <= dist (X_n trajectory) 0}` is eventually
  contained in the exact model-tail/return event, and its ENNReal probability
  tends to zero.
- Local APIs/imports: the compiled explicit-schedule high-probability parent,
  expected-cumulative-regret nonnegativity, the exact
  expected-minus-return-deviation identity, positive scheduled rounds,
  `measurableSet_le`, `Real.dist_eq`, `abs_lt`, `measure_mono`, ENNReal order
  squeeze, and `tendstoInMeasure_iff_dist`.
- Proof route: the parent supplies the upper envelope off its event. The
  return-event complement gives `|deviation| < radius`; expected-regret
  nonnegativity and positive division give the missing strict lower bound.
  Both deterministic sides tend to zero, so fixed distance violations are
  eventually event-contained; measure monotonicity and the vanishing exact
  budget yield the fixed-threshold probability limit and the Mathlib root.
- Regularity contracts: unchanged finite nonempty Standard Borel
  State/Action, probability initial law, positive horizon/base floor/variance
  proxy, bounded stored means, uniform selected-reward sub-Gaussian law,
  exploratory path support/visit floor, and inherited filtration/adaptation.
  No independence, summability, or stopping-time premise is added.
- Retrieval evidence/status: exact target retrieval was a no-hit. Compiled
  local declarations and Mathlib measure/order/asymptotic APIs are direct
  evidence; scenario/UCB-VI cards are placement only and proof weapons are
  inspiration only. Status is `leanCompiled`: 11 declarations, root import,
  focused and `Tests.Basic` builds, typed Bool/Bool canaries, clean
  placeholders, baseline-only axioms, and independent review integrated. The
  review's stale-blueprint observation was cleared by refresh, and direct
  lower-bound/event-measure canaries were added.
- Failure policy: this process normalizes each successor batch before giving
  rounds equal weight. The older compiled `realizedSuccessorAverageRegret`
  in-measure theorem weights by total episode mass and is contrast evidence,
  not a transport theorem. The result is fourth-power-subsequence convergence
  in measure, not all-prefix, anytime, almost-sure, L1, minimax, reachability,
  raw-episode, behavior/recommendation equality, or complete UCB-VI.
- Next boundary: an equal-round-weighted L1 or almost-sure strengthening needs
  separate integrability or summable-tail infrastructure and is not inferred
  from this route.

## Closed Gap: Explicit Polynomial-Prefix Upper-Tail Probability Consistency

- Lean statement: for every fixed `epsilon > 0`, the scheduled event
  `{trajectory | epsilon < average realized behavior regret}` is measurable;
  eventually it is contained in the compiled envelope-violation set, its
  trajectory probability is at most the exact model-tail/return failure
  budget, and that ENNReal probability tends to zero.
- Local APIs/imports: the compiled explicit fourth-power high-probability
  terminal and its process/rate/violation/budget surfaces; Mathlib
  `measurableSet_lt`, `measure_mono`, eventual filters, strict order
  transitivity, and the order squeeze theorem.
- Proof route: use the parent's rate limit to obtain eventually
  `rate n < epsilon`; compose with `epsilon < process n` for event inclusion;
  project the parent's exact violation-probability bound; transport it with
  measure monotonicity; squeeze the upper-tail probability between zero and
  the vanishing budget.
- Regularity contracts: exactly the parent finite nonempty Standard Borel
  State/Action, probability, positivity, bounded-mean, selected-reward
  sub-Gaussian, path-support/visit-floor, filtration, and StronglyAdapted
  contracts. No independence, summability, or stopping-time premise is added.
- Retrieval evidence/status: exact local search was a no-hit; all proof terms
  come from the compiled parent or Mathlib measure/order/asymptotic APIs.
  UCB-VI/scenario cards are placement only and weapons are inspiration only.
  Status is `leanCompiled`: 8 declarations, root import, focused and
  `Tests.Basic` builds, external measurability/inclusion/budget/limit canaries,
  no placeholders, baseline-only axioms, and independent review integrated.
- Failure policy: preserve the one dependent source, `t -> t+1`, per-batch
  normalization, global initial-law centering, fourth-power schedule, and
  exact budget. This is one-sided subsequence control, not absolute
  `TendstoInMeasure`, lower-tail, all-prefix, anytime, minimax, reachability,
  behavior/recommendation equality, or complete UCB-VI.
- Next route: a lower-tail certificate or an exact connection to an existing
  absolute in-measure process requires a separate proof; neither follows from
  this one-sided result.

## Closed Gap: Explicit Polynomial-Prefix High-Probability Average Realized Behavior-Regret Consistency

- Lean statement: with `scale n = n+1`, `burnin n = scale n`,
  `rounds n = scale n ^ 4`, and `returnDelta n = exp (-scale n)`, the exact
  model-tail/return failure budget and complete average realized behavior-
  regret envelope both tend to zero. At every scheduled prefix the terminal
  exposes measurable event and one-sided violation sets, their inclusion and
  exact probability bounds, eventual strict-subunit confidence, and the
  event-good pathwise average bound.
- Local APIs/imports: the burn-in/tail terminal; natural own-count-normalized
  return proxy; conditional sub-Gaussian radius-square identity; finite sums;
  Real exp/log/sqrt and order; ENNReal `ofReal`; filter arithmetic.
- Proof route: remove the dummy-zero term and bound each positive-count proxy
  by one per-episode proxy; sum exactly `rounds` terms; reduce the scheduled
  radius to `2*(C+1)/scale`; compose tail-model and exponential return-share
  limits; split the average rate into `2H/scale^3`, the logarithmic parent,
  and the return radius; instantiate the parent terminal for every `n`.
- Regularity contracts: finite nonempty Standard Borel State/Action,
  probability initial law, positive horizon/base floor/reward proxy and
  scheduled counts, bounded means, uniform selected-reward sub-Gaussianity,
  path support/visit floor, and inherited filtration/StronglyAdapted
  contracts. No model/return independence is assumed.
- Retrieval evidence/status: exact search was a no-hit; local compiled
  burn-in/tail, model-tail, return, logarithmic and finite-sum routes plus
  Mathlib measure/martingale/sub-Gaussian/order/log-sqrt-exp/asymptotic APIs
  are direct evidence. `SCN-RL-MDP` and UCB-VI are placement only; weapons
  are inspiration only. Status is `leanCompiled`: 25 declarations, root
  import, focused/root/`Tests.Basic` builds, Bool/Bool canaries, no
  placeholders, and standard axioms only.
- Failure policy: preserve the one dependent source, `t -> t+1` successor
  indexing, per-batch positive-count normalization, global initial-law
  centering, and exact union-bound shares. This is a deterministic cofinal
  fourth-power prefix subsequence with a one-sided upper envelope, not
  all-prefix, anytime, absolute `TendstoInMeasure`, minimax, reachability,
  behavior/recommendation equivalence, or complete UCB-VI.
- Downstream status: consumed by the compiled fixed-`epsilon` one-sided
  upper-tail probability route above.

## Closed Gap: Burn-In Tail High-Probability Logarithmic Realized Behavior Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-BURNIN-TAIL-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityBurninLogRate`.
For deterministic `burnin <= rounds`, it splits the natural finite sum at
`burnin`, charges exactly the early coordinates by the uniform `2 * horizon`
bound, and applies the actual one-coordinate model-good planning certificate
to the later coordinates outside the infinite model tail. The suffix is
dominated by the existing nonnegative full planning sum and its compiled
`C_mdp * (1 + log rounds)` envelope.

The terminal unions that infinite tail with the fixed-prefix normalized
successor-batch-average return event. It proves the joint event and both
one-sided cumulative/positive-round average violations measurable, contains
the violations in the joint event, and bounds all three probabilities by the
exact budget
`selfConsistentScheduledCausalTailModelFailureBudget mdp burnin +
ENNReal.ofReal returnDelta`. No model/return independence is assumed. Every
joint-event-good path has cumulative envelope
`2 * horizon * burnin + C_mdp * (1 + log rounds) + returnRadius`; the average
is this quantity divided by positive `rounds`.

Local proof evidence is the compiled fixed-prefix realized route, infinite
tail-model route, `Finset.sum_range_add_sum_Ico`, per-round `2H` and
model-good planning bounds, exact realized/expected/deviation identity,
normalized return tail, `measure_union_le`, and `measure_mono`. Regularity
retains finite nonempty Standard Borel State/Action, probability initial law,
positive horizon/rounds/base floor/reward proxy, bounded means, uniform
selected-reward sub-Gaussianity, exploratory path support/visit floor,
`burnin <= rounds`, and `0 < returnDelta <= 1`. Exact retrieval was a no-hit;
UCB-VI/scenario cards are placement only and weapons are inspiration-only.
Status is `leanCompiled`, root-imported, externally instantiated on Bool/Bool,
placeholder-free, and baseline-axiom audited.

Failure policy preserves the one dependent source, actual `t -> t+1`
successor batch, each batch's own positive-count normalization, global
initial-law centering, and the exact tail-model plus caller-return shares.
This remains a fixed-`burnin`, fixed-`rounds` batch-average theorem, not
anytime, minimax, reachability, one-raw-episode regret, behavior/recommended-
policy equivalence, or complete UCB-VI. The next route must choose a growing
sublinear burn-in and vanishing return share and prove both the average
envelope and total failure budget tend to zero.

## Closed Gap: Fixed-Prefix High-Probability Logarithmic Cumulative/Average Realized Behavior Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FIXED-PREFIX-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityLogRate`.
Its 41 declarations normalize each actual successor-batch return deviation by
that batch's positive scheduled episode count, square-scale the conditional
sub-Gaussian proxy with Mathlib `Kernel.HasSubgaussianMGF.const_mul`, preserve
the dummy-zero/`piLE` successor indexing, and prove a fixed-prefix two-sided
tail for their finite sum. The exact identity rewrites cumulative realized
behavior regret as the existing random cumulative behavior expected regret
minus this globally initial-law-centered normalized deviation.

The self-consistent terminal unions the actual model event with the normalized
return event. It exposes measurable cumulative and round-average realized
processes and violation sets, contains both violations in that union, and
bounds the union and both violations by
`selfConsistentScheduledCausalModelFailureBudget mdp rounds +
ENNReal.ofReal returnDelta`. Every union-good trajectory has cumulative regret
at most the compiled logarithmic expected-regret envelope plus the normalized
return radius, and average regret at most that quantity divided by positive
`rounds`. The proof uses `measure_union_le`; it assumes no independence between
model and return events. The terminal also explicitly proves that if the exact
total budget is less than one, then the joint event and both violations each
have probability strictly less than one.

Regularity retains finite nonempty Standard Borel State/Action, a probability
initial law, positive horizon/rounds/base floor/reward proxy and scheduled
batches, bounded means, uniform mean-compatible selected-reward
sub-Gaussianity, exploratory path support, and `0 < returnDelta <= 1`. Exact
retrieval was a no-hit; compiled local model/logarithmic and causal return-
concentration routes plus Mathlib finite-sum, conditional expectation,
martingale, sub-Gaussian, measure, order, and log/sqrt cards are evidence.
UCB-VI is placement only; weapon cards are inspiration-only. Status is
`leanCompiled`, root-imported, and externally instantiated on Bool/Bool.

Failure policy preserves the one dependent causal source, natural `t -> t+1`
selection, actual successor batches, per-batch rather than total-mass
normalization, global initial-law centering, positive fixed prefix, and the
exact model-plus-return shares. This is fixed-prefix batch-average realized
behavior regret, not one raw online episode per round, arbitrary-delta model
control, uniform-time/anytime control, minimax/optimal-rate regret,
reachability, or complete UCB-VI. Any all-prefix or asymptotic consumer must
separately schedule `returnDelta` and handle the accumulated model budget.

## Closed Gap: Fixed-Prefix High-Probability Logarithmic Cumulative Behavior Expected Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FIXED-PREFIX-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-BEHAVIOR-EXPECTED-REGRET`
now compiles in
`FiniteHorizonNaturalCausalBehaviorExpectedRegretHighProbabilityLogRate`.
Its thirteen declarations define the natural planning-rate prefix sum, expose
the exact finite ENNReal sum of both model-confidence shares, transport the
complement of the prefix model event to every included coordinate, prove the
random cumulative behavior expected-regret process measurable, and define its
one-sided logarithmic violation set. The terminal proves the model and
violation events measurable, the violation set contained in the model event,
both probability bounds controlled by the exact accumulated model budget, and
every model-good trajectory bounded first by the planning sum and then by the
compiled `C_mdp * (1 + log rounds)` envelope.

The proof uses the existing finite union of actual selected count-and-reward
model failures; it introduces no new independence or MGF claim. Its local APIs
are `selfConsistentScheduledCausalModelBadEvent`, the coordinate model event
and actual-behavior planning theorem, `Set.mem_iUnion_of_mem`,
`Finset.measurable_sum`, `Finset.sum_le_sum`, `measurableSet_lt`, and
`measure_mono`, plus the compiled logarithmic parent. Regularity retains finite
nonempty Standard Borel State/Action, probability initial law, positive
horizon/base floor/reward proxy, bounded means, uniform mean-compatible
selected-reward sub-Gaussianity, and path support. Exact retrieval was a
no-hit; compiled model-confidence/logarithmic routes and Mathlib finite-sum,
measure, kernel, and sub-Gaussian cards are evidence. RL/UCB-VI cards are
placement only and the optimism weapon remains inspiration-only. Status is
`leanCompiled`, root-imported, and externally instantiated on Bool/Bool.

Failure policy preserves actual exploratory behavior rather than the
recommendation, one dependent source and actual sampled batches, natural
`t -> t+1` selection, schedules, initial exclusion, and both confidence
shares. The budget is exact and is not replaced by an arbitrary delta or
claimed to vanish with the prefix. This is fixed-prefix probability over a
random behavior expected-regret process, not realized return, uniform-time or
anytime control, every-trajectory control, reachability, minimax/optimal-rate,
or complete UCB-VI. The realized fixed-prefix consumer above now supplies the
separately compiled normalized sampled-return process and combined event.

## Closed Gap: Natural Causal Explicit Logarithmic Cumulative/Average Behavior Rate

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-EXPLICIT-LOGARITHMIC-CUMULATIVE-AVERAGE-BEHAVIOR-EXPECTED-REGRET-RATE`
now compiles in `FiniteHorizonNaturalCausalBehaviorExpectedRegretLogRate`.
Its thirty declarations provide unconditional shifted inverse-square,
high-power, and harmonic finite-sum bounds; explicit nonnegative rate
coefficients; refined and logarithmic cumulative/average envelopes; actual
expected cumulative and average pointwise bounds; Big-O statements for the
envelope and both actual objectives; and the actual `log(n)/n` average limit.

The coordinate integrated rate is rewritten exactly as
`a/(t+2)^2 + b/(t+3) + c/(t+2)^(horizon+5)`. The inverse-square term is
compared to the telescoping difference
`1/(t+1) - 1/(t+2)` and summed with `Finset.sum_range_sub'`. Exponent
monotonicity reduces the high-power term to that bound. Mathlib
`harmonic_le_one_add_log` bounds the shifted exploration sum, and
`one_le_one_add_log_natCast` absorbs the two summable constants without losing
the zero-prefix case. `Real.isLittleO_log_id_atTop`,
`tendsto_const_div_atTop_nhds_zero_nat`, `Asymptotics.isBigO_refl`, and
`Asymptotics.isBigO_iff` provide the limit and actual asymptotic interfaces.

The scalar leaves have no probability contracts. The causal consumers retain
finite nonempty measurable State/Action with equality and measurable
singletons, Standard Borel State/Action, probability initial law, positive
horizon/base floor/reward proxy, bounded deterministic means, uniform
mean-compatible selected-reward sub-Gaussianity, and exploratory path support.
Exact retrieval was a no-hit; compiled finite-prefix and explicit integrated
parents plus Mathlib finite-sum/order/log/asymptotic cards are direct evidence.
The RL/UCB-VI paper card is placement only and the optimism weapon is
inspiration only. Status is `leanCompiled` with root import and Bool/Bool
pointwise, Big-O, zero-prefix, and limit canaries.

Failure policy preserves actual exploratory behavior rather than the
recommended policy, one dependent source and sampled batches, natural
`t -> t+1` successor selection, scheduled budgets, initial exclusion, and both
integrated confidence shares. The theorem is expectation over source
randomness, not realized return, every-trajectory, anytime/high-probability,
reachability, minimax/optimal-rate, or complete UCB-VI. The fixed-prefix
high-probability consumer now compiles above and keeps the accumulated
nonvanishing model-confidence budget explicit.

## Closed Gap: Natural Causal Finite-Prefix Cumulative And Average Behavior Rate

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FINITE-PREFIX-CUMULATIVE-AVERAGE-BEHAVIOR-EXPECTED-REGRET-RATE`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretFinitePrefixCumulativeAverageRate`.
Its seventeen declarations define the pathwise natural-prefix behavior-regret
sum, its expectation, cumulative and average deterministic rates, prove
nonnegativity/integrability, identify the cumulative expectation exactly with
the sum of coordinate expected absolute regrets, establish cumulative and
average inequalities, prove both average zero limits, and expose a route
terminal.

`IntegrabilitySums.integrable_finset_sum` closes prefix integrability and
`ExpectationBochnerSums.integral_finset_sum` moves the actual pathwise
`Finset.range` sum through the Bochner integral on the unchanged causal
measure. Coordinate nonnegativity removes the absolute values. The compiled
pointwise integrated bound is then summed by `Finset.sum_le_sum`; division by
the nonnegative real cast of `rounds` gives the average bound. The deterministic
average rate is exactly `natWeightedAverage (fun _ => 1)`, so the compiled
positive-weight zero-limit theorem gives Cesaro convergence and
`squeeze_zero'` transfers it to actual average behavior expected regret.

Beyond the module-wide finite measurable-space assumptions, the exact
finite-sum identity needs a probability initial law and bounded means for
coordinate integrability. The rate terminal retains finite nonempty
Standard Borel State/Action, positive horizon/base floor/reward proxy, uniform
mean-compatible selected-reward sub-Gaussianity, and path support. Exact route
retrieval was a no-hit; the compiled pointwise parent, finite-sum wrappers,
positive-weight-average Mathlib candidate, and Mathlib finite-sum/integral/
order/asymptotic cards are direct evidence. RL/UCB-VI cards are placement only
and the optimism weapon is inspiration only. Status is `leanCompiled` with
Bool/Bool exact-sum, cumulative-bound, zero-prefix, rate-limit, and
actual-average-limit canaries.

Failure policy preserves actual exploratory behavior rather than the
recommended policy, one dependent source, sampled batches, natural `t -> t+1`
successor selection, scheduled budgets, initial exclusion, and both already
integrated confidence shares. The explicit logarithmic consumer above now
closes the finite-sum constants and actual Big-O interfaces. This parent remains
the exact same-source finite-prefix assembly surface and supplies no
realized-return, every-trajectory/anytime, reachability, minimax/optimal-rate,
or complete UCB-VI result by itself.

## Closed Gap: Natural Causal Explicit Integrated Behavior Rate

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-EXPLICIT-INTEGRATED-BEHAVIOR-EXPECTED-REGRET-RATE`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretExplicitIntegratedRate`.
Its ten declarations provide a generic measurable bad-event integral split,
planning-rate nonnegativity, exact ENNReal-to-Real identification of the two
coordinate confidence shares, a named and fully expanded finite-coordinate
envelope, its nonnegativity and zero limit, the expected-absolute behavior
bound, a quantitative squeeze proof, and a route terminal.

The generic proof majorizes `f` by `rate + bad.indicator envelope` and uses
`integral_mono`, `Integrable.indicator`, `integral_add`,
`integral_indicator`, and `Measure.real_def`. The causal consumer applies the
compiled event-outside actual `successorPolicyAt` planning certificate and the
global `2 * horizon` bound. The model-round event is measurable and its mass
is bounded by the exact two-share coordinate budget;
`ENNReal.toReal_le_toReal` transports that bound and the budget simplifies to
`2 * delta_t`. Thus expected absolute behavior regret is at most planning
rate plus `4 * horizon * delta_t`. Planning convergence and summability of
`delta_t` make the envelope vanish.

The generic lemma requires a probability measure, measurable bad event,
integrability, nonnegative local rate, and pointwise local/global bounds. The
causal terminal retains finite nonempty Standard Borel State/Action,
probability initial law, positive horizon/base floor/reward proxy, bounded
means, selected-reward sub-Gaussianity, and path support. Exact combined-route
retrieval was a no-hit; compiled local event/pointwise/L1 parents and Mathlib
integral/order/asymptotic APIs are direct evidence. RL/UCB-VI cards are
placement only and the optimism weapon is inspiration only. Status is
`leanCompiled` with Bool/Bool bound, nonnegativity, envelope-limit, and
expectation-limit canaries.

Failure policy preserves the actual behavior policy, recommendation/behavior
distinction, one dependent source, samples, `n -> n+1`, scheduled budgets,
initial exclusion, and exact two confidence shares; no realized-return MGF is
used. The compiled finite-prefix consumer above now supplies the exact
same-source cumulative/average assembly and Cesaro limit. This parent remains
per-coordinate and is not a realized-return, every-trajectory, anytime,
reachability, minimax/optimal-rate, or complete UCB-VI result.

## Closed Gap: Natural Causal Behavior-Expected L1 Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-L1-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretL1Consistency`.
Its thirteen declarations provide the actual behavior expected-regret
process's global `2 * horizon` bound, coordinate integrability, named expected-
absolute objective and zero limit, `MemLp Real 1`, exact exponent-one
`eLpNorm`, named `Lp Real 1` convergence, and a same-source joint behavior/
realized L1 terminal.

The proof consumes the compiled coordinate measurability and a.e. behavior
limit. `Integrable.of_bound` handles each coordinate, while Mathlib
`tendsto_integral_filter_of_norm_le_const` applies dominated convergence under
the constant `2 * horizon` envelope. Nonnegativity converts the integral of
the absolute value to the process integral. `memLp_one_iff_integrable`,
`MemLp.eLpNorm_eq_integral_rpow_norm`, `ENNReal.continuous_ofReal`, and
`Lp.tendsto_Lp_iff_tendsto_eLpNorm''` package the result. The final terminal
reuses the compiled realized L1 theorem on the identical trajectory measure.

The pointwise bound/integrability need finite measurable nonempty State/Action,
equality/singletons, a probability initial law, and bounded deterministic
means; no Standard Borel law or selected-reward MGF enters that part. The
limits retain the a.e. parent's finite nonempty Standard Borel State/Action,
positive horizon/base floor/reward proxy, bounded means, uniform mean-
compatible selected-reward sub-Gaussianity, and path support. Exact combined-
route retrieval was a no-hit; compiled local a.e./measurability and realized-
L1 parents plus Mathlib integral/Lp/asymptotic APIs are direct evidence. RL/
UCB-VI cards are placement only and the optimism weapon is inspiration only.
Status is `leanCompiled` with Bool/Bool terminal and projection canaries.

Failure policy preserves the actual exploratory policy, recommendation/
behavior distinction, one dependent source, actual samples, `n -> n+1`,
scheduled budgets, initial exclusion, and realized-regret global centering.
The behavior proof does not borrow the realized-return MGF. The explicit-rate
consumer above now closes the one-model-event finite-coordinate integrated
bound. This parent still does not supply cumulative/average, every-trajectory,
anytime, reachability, minimax/optimal-rate, or complete-UCB-VI control.

## Closed Gap: Natural Causal Behavior-Expected In-Measure Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-IN-MEASURE-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretInMeasureConsistency`.
Its four declarations prove a generic finite policy-table selector
measurability theorem, every coordinate of the actual causal successor-policy
expected-regret process measurable, behavior expected regret tending to zero
in measure, and a same-source joint behavior/realized in-measure terminal.

The generic proof writes the selected policy statistic as a finite sum of
singleton indicators and uses `Finset.measurable_sum`, `Measurable.ite`, and
measurable singleton preimages. The concrete coordinate composes
`StochasticEpisodeBatch.measurable_sampledEmpiricalOptimisticPolicyTable`
with `measurable_pi_apply t`, then unfolds `heterogeneousSuccessorTable` and
`successorPolicyAt`. Mathlib `tendstoInMeasure_of_tendsto_ae` transports the
compiled a.e. behavior theorem after each coordinate is promoted to strongly
measurable. The joint theorem reuses the existing realized in-measure result
on the identical `source.trajectoryMeasure`.

The generic selector requires finite measurable State/Action, equality,
measurable singletons, a nonempty Action, and a probability initial law; it
does not require a nonempty State. The causal terminals
retain the parent finite nonempty Standard Borel State/Action, positive
horizon/base floor/reward proxy, bounded means, uniform mean-compatible
selected-reward sub-Gaussianity, and full-exploration path support. Exact
retrieval for successor-policy expected-regret measurability was a no-hit;
the local sampled-table measurability and compiled a.e./realized in-measure
parents plus Mathlib finite-sum and convergence-in-measure APIs are direct
evidence. RL/UCB-VI cards are placement only and the optimism weapon is
inspiration only. Status is `leanCompiled` with external Bool/Bool terminal
and projection canaries.

Failure policy preserves the actual exploratory policy, the recommendation/
behavior distinction, one dependent source, actual samples, `n -> n+1`,
scheduled budgets, initial exclusion, and realized-regret global centering.
The L1 consumer above now supplies `MemLp 1`, expected-absolute, exact
`eLpNorm`, and named `Lp` convergence. This parent itself still supplies no
explicit integrated finite-round rate, every-trajectory, anytime,
reachability, minimax, optimal-rate, or complete-UCB-VI result.

## Closed Gap: Natural Causal Behavior-Expected And Realized A.E. Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-ALMOST-SURE-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceAlmostSureBehaviorExpectedRegretConsistency`.
Its pointwise leaf proves that outside one model-round bad event, the actual
exploratory `source.successorPolicyAt trajectory t` has expected regret at
most `selfConsistentScheduledCausalPlanningRateAt mdp t`. The proof consumes
the recommended-policy occupancy certificate, applies the compiled
recommended-to-exploratory transport with its decaying-exploration charge,
evaluates the occupancy sum, and closes the local planning bound.

Only the model-event sequence is used for the new limit. Its finite measure
tsum and first Borel-Cantelli give eventual pointwise domination; actual
policy expected regret is nonnegative and the deterministic planning rate
tends to zero. The final theorem intersects this a.e. set with the compiled
realized-regret set. The same trajectories therefore have eventual all-state
optimism plus the recommended-policy certificate, actual behavior expected-
regret convergence, and realized-regret convergence.

Regularity is unchanged: finite nonempty Standard Borel State/Action,
probability initial law, positive horizon/base floor/reward proxy, bounded
stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
full-exploration path support. Exact retrieval was a no-hit; the compiled
coordinate-confidence, exploratory transport, occupancy identity, causal
rate, and Borel-Cantelli parents are the direct evidence. Status is
`leanCompiled` with five declarations and external Bool/Bool pointwise,
standalone-a.e., joint-terminal, behavior-limit, and realized-limit canaries.

This parent does not prove coordinate measurability internally. The finite-
selector consumer above now supplies that regularity and same-source
`TendstoInMeasure`. Preserve the actual/recommended policy distinction; the
remaining narrow boundary is behavior-process `MemLp 1`/`L1`, not every-
trajectory, anytime, reachability, minimax, optimal-rate, or complete-UCB-VI.

## Closed Gap: Heterogeneous Natural Causal Almost-Sure Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-ALMOST-SURE-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceAlmostSureConsistency`.
On the same genuine round-varying dependent trajectory measure as the natural
causal in-probability and L1 routes, every regret coordinate is measurable,
realized successor-average regret tends to zero almost everywhere, and one
strengthened terminal retains eventual all-state empirical-model optimism and
the recommended-policy occupancy-radius regret certificate on that same a.e.
full set.

The new analytic leaf proves `exp (-sqrt n)` summable using Mathlib
Schloemilch condensation along `(n+1)^2`. Positive scheduled episode batches
make actual successor mass at least the round index, so the mass-adapted return
share is summable. Existing p-series model-event bounds and the actual return
event bounds therefore have finite ENNReal measure tsums. First
Borel-Cantelli `ae_eventually_notMem` applies separately to both sequences on
the same dependent source and requires no independence. Almost every
trajectory receives one finite model-good burn-in and is eventually
return-good; the compiled fixed-burn-in absolute-regret envelope then tends to
zero. Applying the existing one-coordinate confidence theorem to the eventual
model-good filter gives both global optimism and the recommended-policy bound
without introducing another sample space or another null set.

Regularity is unchanged: finite nonempty Standard Borel State/Action,
probability initial law, positive horizon/base floor/reward proxy, bounded
stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
full-exploration path support. Exact local retrieval was a no-hit; the direct
Mathlib Borel-Cantelli/Schloemilch sources and compiled causal event/terminal/
coordinate-confidence parents are the evidence. Status is `leanCompiled` with
14 declarations and external Bool/Bool summability, eventual-good, final a.e.,
joint-terminal, and all-state-optimism canaries.

This parent remains a measure-a.e. realized-regret statement, not convergence
for every theoretical trajectory, an anytime finite-sample envelope, minimax
control, state reachability, or complete UCB-VI. The behavior-expected consumer
above now compiles the pointwise successor-policy rate and its a.e. limit on
this same source. Coordinate measurability of that behavior expected-regret
process is the next narrow boundary.

## Closed Gap: Heterogeneous Natural Causal L1 Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-L1-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceL1Consistency`.
On the same genuine round-varying dependent trajectory measure as the natural
causal in-probability route, expected absolute realized successor-average
regret tends to zero. Every coordinate is `Integrable` and `MemLp 1`, its
exponent-one `eLpNorm` is identified exactly, and the named `Lp Real 1`
process converges to zero.

No uniform-integrability axiom is added. Mean-policy regret is globally at
most `2 * horizon`; a fixed burn-in pays this bound only on the vanishing
model-tail event. The cumulative globally centered successor return deviation
has a direct sub-Gaussian MGF under the same causal measure, and the compiled
MGF-to-absolute-integral theorem bounds its first moment. Dividing by actual
successor mass gives a vanishing normalized return term. The two-parameter
proof first chooses burn-in for the p-series model tail and then rounds for
the planning and return-MGF terms.

Regularity is unchanged: finite nonempty Standard Borel State/Action,
probability initial law, positive horizon/base floor/reward proxy, bounded
stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
full-exploration path support. Exact retrieval was a no-hit; compiled causal
MGF, integral, asymptotic, `MemLp`, `eLpNorm`, and `Lp` APIs are the direct
evidence. Status is `leanCompiled` with 27 declarations and external Bool/Bool
expected-absolute, `MemLp`, named-`Lp`, and terminal canaries.

This L1 theorem alone is not an almost-sure argument. The distinct consumer
above now supplies summable full-sequence events and first Borel-Cantelli on
the same source. Neither theorem is an all-trajectory pathwise result, anytime
control, a minimax rate, state reachability, or complete UCB-VI.

## Closed Gap: Heterogeneous Natural Causal In-Probability Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-IN-PROBABILITY-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceConsistency`.
On the one genuine round-varying causal trajectory measure, its measurable
realized successor-average regret process tends to zero in Mathlib
`TendstoInMeasure`.

The proof rewrites the local model share as a summable p-series, bounds the
union of model failures after an explicit burn-in by the complementary
`ENNReal` tail sum, and lets that budget vanish. Early expected regret uses
the deterministic `2 * horizon` policy bound and is diluted by the diverging
successor episode mass; post-burn-in coordinates use the compiled causal
planning rate. The return share `exp (-sqrt successorMass)` and its normalized
sub-Gaussian radius both vanish. A finite terminal combines these terms into
one measurable bad event and an absolute realized-regret envelope.

Regularity remains finite nonempty Standard Borel State/Action, probability
initial law, positive horizon/base floor/reward proxy, bounded stored means,
uniform mean-compatible selected-reward sub-Gaussianity, and full-exploration
path support. Retrieval found no exact natural heterogeneous causal
convergence card; the compiled causal parents, Mathlib p-series/tail-sum,
finite-sum, kernel, integral, log/sqrt, sub-Gaussian, and asymptotic APIs are
the route evidence. Status is `leanCompiled` with 38 declarations and external
Bool/Bool finite-tail and convergence canaries.

This theorem itself is convergence in probability only. Its same-measure `L1`
consumer now compiles above by directly integrating the causal return MGF,
without importing the independent complete-window product argument. Neither
result is pathwise, almost-sure, anytime, minimax, state-reachability, or
complete-UCB-VI control.

## Closed Gap: Heterogeneous Causal Explicit Weighted Rate

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EXPLICIT-WEIGHTED-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalExplicitRate`.
The module proves a reusable positive-natural-weight average theorem from
Mathlib `Asymptotics.IsLittleO.sum_range`. It then bounds each causal planning
coordinate by its scale-squared reward/transition rate plus the actual
successor exploration charge, weights coordinate `t` by `episodes (t+1)`, and
normalizes by the exact successor mass. The heterogeneous global-return proxy
is identified as that mass times the one-episode proxy, so a fixed-half
normalized return radius also tends to zero.

The finite-prefix terminal retains the named causal model/return event, exact
failure budget, and every sampled-model optimism certificate, while replacing
the abstract realized-regret bound by the explicit weighted planning-plus-
return envelope. The envelope tends to zero under the existing finite
nonempty Standard Borel, probability, positive horizon/base-floor/proxy,
bounded-mean, uniform selected-reward sub-Gaussian, and path-support contracts.
Retrieval found no exact weighted causal or weighted-Cesaro card; the compiled
causal parent, fixed-window rate calibration, finite-sum/order/log-sqrt/
asymptotic/sub-Gaussian cards, and exact Mathlib `IsLittleO` APIs supply the
route evidence. Status is `leanCompiled` with 20 declarations and external
Bool/Bool terminal projections.

Only the deterministic regret envelope vanishes in this fixed-prefix parent.
The exact finite-prefix model budget accumulates early failures and is not a
vanishing sequence. The natural causal route above now consumes this result by
discarding a finite burn-in in its tail event and diluting the early regret;
this parent alone still proves no convergence statement.

## Closed Gap: Heterogeneous Causal Realized Successor Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalRealizedSuccessorRegret`.
Successor coordinate `n+1` is generated from the prefix through `n`, contributes
`episodes (n+1)` complete episodes, and is evaluated with the policy that
actually generated that batch. Expected and realized cumulative regret use
the same coordinate weights and divide by the actual successor episode mass
`sum_{t < rounds} episodes (t+1)`. Lean proves the exact identity
`realized = expected - cumulative globally centered deviation`.

The route applies each actual sampled model's optimism/recommended-regret
certificate, adds the next-coordinate exploratory behavior charge, sums the
coordinate planning terms, and unions the causal model event with the
successor-only global-return event. The final theorem exposes measurability,
the exact finite model-plus-return failure budget, all finite-prefix optimism
certificates, and the realized successor-average bound. It retains the finite
State/Action, probability, Standard Borel, positive schedule/proxy/horizon,
bounded-mean, uniform selected-reward sub-Gaussian, and exploratory path-floor
contracts of its parents.

This closes the model/return assembly at a fixed prefix and is now consumed by
the explicit heterogeneous weighted planning/return envelope above. It does
not inherit the old constant-window denominator or rates. No common-space,
uniform-time, pathwise, almost-sure, anytime, minimax, reachability, or
complete-UCB-VI conclusion follows.

## Closed Gap: Heterogeneous Causal Empirical-Model Confidence

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EMPIRICAL-MODEL-CONFIDENCE`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalModelConfidence`.
Initial and successor count/reward model events are pulled back to the dependent
trajectory. The exact initial marginal and prefix/next `compProd` law reduce
each coordinate to its generating policy's iid stochastic family, so no
adaptive-round independence is assumed. Batch sizes and both local shares vary
with the coordinate; the finite-prefix probability bound is their exact finite
`ENNReal` sum.

The self-consistent terminal uses each coordinate's scheduled episodes, local
delta, exploration rate, reward radius, and transition fixed-point budget.
Outside one named measurable event, every actual batch `0..rounds-1` produces
an optimistic empirical model and the recommended-policy expected-regret
certificate. The downstream heterogeneous causal realized-successor route now
unions this event with the successor-only globally centered return event and
assembles the behavior certificate. The cumulative prefix failure budget is
not asserted to vanish with `rounds`; no old-window rate,
independence, uniform-time, pathwise, almost-sure, anytime, minimax,
reachability, or complete-UCB-VI conclusion follows.

## Closed Gap: Heterogeneous Causal Sampled-Return Concentration

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SAMPLED-RETURN-CONCENTRATION`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalReturnConcentration`.
The supporting sampled-return process uses `episodes 0` and the initial policy
at coordinate zero, then `episodes (n+1)` and the policy selected from the
dependent prefix through `n`. It centers each batch at its own sampled initial
state. The regret-facing process instead sets coordinate zero to zero and
globally centers successor coordinates `1..rounds` by the initial-law expected
selected-policy value. Exact iid fibers are mapped through retained-input
kernels, dynamic `condDistrib`, and trimmed `condExpKernel` to obtain
conditional sub-Gaussian MGFs relative to `Filtration.piLE`.

Both fixed-round terminals sum genuine coordinate proxies and prove their
two-sided events have mass at most `ENNReal.ofReal delta`. The global terminal
uses `iidGlobalSampledCumulativeReturnDeviationVarianceProxy`, retaining the
sampled-initial-state value fluctuation. Self-consistent wrappers derive total
proxy positivity from positive rounds, horizon, reward proxy, and every
scheduled batch size. The downstream realized-successor route now combines
this return tail with heterogeneous count/reward empirical-model confidence.
The remaining frontier is an explicit heterogeneous weighted rate; no
fixed-window rate, uniform-time, pathwise,
almost-sure, anytime, minimax, reachability, or complete-UCB-VI claim follows.

## Closed Gap: Heterogeneous Actual-Sampled Causal Projective Law

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SOURCE-PROJECTIVE-LAW`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalSource`.
A dependent source stores a stochastic batch of size `episodes n` at
coordinate `n`. Its Mathlib `Kernel.trajMeasure` is one causal process. The
self-consistent specialization computes the optimistic table from the latest
actual sampled batch with budgets at `n`, then samples coordinate `n+1` with
the next exploration rate and episode count. Lean proves the exact initial
law, every selected iid fiber, next-batch `condDistrib`, prefix/next
`compProd`, and all finite-marginal projection equalities.

Construction needs only the finite measurable probability setup; Standard
Borel State/Action enters at the conditional-law terminal. This source is not
a representation of the old fixed-parameter window laws. Therefore their
confidence, optimism, and regret rates do not transfer. The heterogeneous
sampled-return tail now compiles downstream; empirical-model confidence and
event/regret transport remain before any causal realized-regret theorem.

## Closed Gap: Actual-Sampled Exact-Marginal In-Probability Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-COMMON-SPACE-IN-PROBABILITY-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCommonSpaceConsistency`.
The finite adapter proves an absolute actual-sampled realized successor-average
bound from the model-good expected certificate and two-sided globally centered
return deviation. An independent `Measure.infinitePi` coupling then has each
scheduled trajectory law as an exact evaluation marginal. The pulled-back
three-share bad event and explicit vanishing absolute envelope prove
`TendstoInMeasure` to zero.

No regularity changed: finite nonempty Standard Borel State/Action,
probability, positive horizon/base floor/proxy, uniform selected-reward
sub-Gaussianity, bounded means, and full-exploration path floor remain visible.
This is not a natural nested online run and gives no pathwise, almost-sure,
anytime, reachability, minimax, or complete-UCB-VI theorem. A distinct causal
source and its fixed-round sampled-return concentration now compile, but do not
inherit these independent-window marginals or rates.

## Closed Gap: Scheduled Actual-Sampled Explicit Realized Rate

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-EXPLICIT-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentExplicitRate`.
Writing `scale=n+2`, the compiled schedule gives `rewardBudget<=scale^-2`,
`q<=1/2`, and `q<=4*card(State)*horizon/scale^2`. The new ordered-field
consumer proves the exact fixed-point transition budget is at most `3*q`,
hence at most `12*card(State)*horizon/scale^2`.

The resulting planning envelope is the scale-squared model term plus the
explicit `scale^-1` exploration charge. Adding the compiled normalized return
envelope yields an explicit sum of scale-squared and inverse-scale terms. The
three event shares are exactly `ofReal(3/scale)`, and the failure and regret
rate envelopes tend jointly to zero. The pointwise source terminal keeps the
same actual samples, measurable event, and all-round optimism. No named Lean
`IsBigO` theorem is claimed by this leaf.

No regularity contract changed: the parent finite nonempty Standard Borel,
probability, positive proxy, uniform selected-reward sub-Gaussian law,
bounded-mean, and path-floor assumptions remain exact. This is a sufficient,
loose, changing-window rate. It is not a natural shared process, reachability,
almost-sure/anytime/minimax result, or complete UCB-VI. The next distinct
boundary is the natural shared causal stream or a genuinely tighter rate.

## Closed Gap: Scheduled Actual-Sampled Self-Consistent Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentSchedule`.
For `scale=n+2`, it uses exploration and confidence rate `1/scale`,
`rounds=scale^(horizon+4)`, the path-support floor scaled by
`explorationRate^horizon`, and an episode count one above the maximum of the
calibration, count-shrink, and reward-shrink thresholds.

The schedule proves `rewardBudget < scale^-2` and
`q < 4*card(State)*horizon/scale^2`, while calibration gives `q<=1/2`.
Consequently the reward budget, contraction, exact fixed-point transition
budget, exploration charge, and globally centered normalized return radius all
tend to zero. The named realized successor-average regret bound and the sum of
three `ofReal(delta)` failure shares therefore tend jointly to zero.

For every `n`, the compiled terminal still uses actual sampled rewards and one
measurable count/reward/return union; outside it every selected plan is
optimistic and realized successor-average regret is below the scheduled bound.
The explicit contracts are finite nonempty measurable State/Action with
equality/singletons, Standard Borel State/Action, probability initial law,
positive horizon/base floor/reward proxy, a mean-compatible uniform
sub-Gaussian selected-reward law, means bounded by one, and a full-exploration
path-support floor. Batch regularity and all schedule positivity/margin
obligations are discharged locally.

This is a family of changing finite-window certificates. It is not a common
causal process, state-reachability theorem, almost-sure/anytime/minimax result,
or complete UCB-VI theorem. A distinct heterogeneous causal law now compiles;
its next boundary is conditional concentration/model-confidence transport, or
a sharper algorithm-specific finite-horizon rate, not reopening the compiled
schedule algebra.

## Closed Gap: Actual-Sampled Self-Consistent-Budget Realized Successor Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles across
`FiniteHorizonStochasticRewardIIDSelfConsistentCalibration` and
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentRealizedBehaviorRegret`.
Writing
`q = card(State) * uniformFloorTransitionCoordinateRadius * horizon`, the
strict contract `q < 1` defines
`T = q * (rewardBound + 2 * rewardBudget) / (1 - q)` and proves the exact
identity `q * (rewardBound + 2 * rewardBudget + T) = T`. This closes every
transition-radius/value-envelope sum, the fixed-policy and exploratory
path-support confidence routes, and every adaptively selected actual sampled
model.

The cumulative successor exploratory-behavior expected-regret bound is
`rounds * (2 * horizon * (rewardBudget + T) + explorationCharge)`. The generic
two-budget return transport then yields one measurable three-share event; off
it all sampled plans are optimistic and realized successor-average regret is
at most `2 * horizon * (rewardBudget + T) + explorationCharge` plus the global
return radius over `episodes * rounds`. Actual rewards remain sampled and may
be unbounded; coordinate `n` still selects batch `n+1`, the initial batch is
excluded, and no adaptive-round independence is assumed.

Focused foundation/module builds and the root-imported external canaries pass.
The route removes the coarse budget's forced `2 * horizon * rewardBound` term;
the explicit vanishing schedule is now compiled by the route above. Preserve
this module as the finite-window parent rather than duplicating its confidence,
indexing, or realized-return transport.

## Closed Gap: Actual-Sampled Explicit-Budget Realized Successor Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-EXPLICIT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticExplicitBudgetRealizedBehaviorRegret`.
For every actual sampled plan, `selectedRadiusRemaining` is definitionally
`rewardBudget + transitionBudget`. The probability occupancy recursion and
finite-round sum therefore evaluate exactly to
`rounds * horizon * (2 * (rewardBudget + transitionBudget))`.

With the current uniform-floor calibration
`transitionBudget = rewardBound + 2 * rewardBudget`, positive-round division
closes the planning average as
`2 * horizon * (rewardBound + 3 * rewardBudget) + explorationCharge`.
The three-share parent terminal is then rewritten without changing its event,
tail, optimism, successor indexing, global return centering, or normalized
return radius. Its complete realized successor-average bound is now
trajectory-independent.

The algebraic layer adds no statistical assumptions and omits `Nonempty State`
where unnecessary. The terminal inherits the parent's finite Standard Borel,
probability, sub-Gaussian, positivity/share, path-support and calibration
contracts, still with unbounded sampled rewards. Focused and external-canary
builds pass. This is an explicit fixed-budget comparison, not a vanishing rate:
it contains the irreducible term `2 * horizon * rewardBound`. The compiled
self-consistent route above repairs that obstruction; fixed-budget schedule
tuning does not.

## Closed Gap: Actual-Sampled Realized Successor Average Behavior Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticRealizedBehaviorRegret`.
The measurable sampled-table selector supplies `GlobalReturnMeasurability` for
the concrete source, and exact wrappers identify the generic source cumulative
and average expected-regret APIs with the actual sampled-plan exploratory sum.

The route unions the two-share sampled empirical-model event with a separate
globally centered successor-return event. Thus count, reward-model, and return
failures retain three explicit confidence shares. Outside the union, every
sampled plan is optimistic and realized regret over successor batches
`1..rounds`, normalized by `episodes * rounds`, is at most the actual sampled
occupancy-radius sum divided by `rounds`, plus the exploration charge and the
global return confidence radius divided by `episodes * rounds`.

The result inherits the parent finite Standard Borel, probability,
sub-Gaussian, positivity/share, exploration, bounded-mean, path-support,
strict-margin, and half-contraction contracts. Return concentration adds
Standard Borel regularity for stochastic batches/trajectories and positivity
of the cumulative global-return proxy. It assumes neither bounded sampled
rewards nor adaptive-round independence. Focused and external-canary builds
pass. The explicit-budget consumer above now closes its trajectory-dependent
occupancy term; this parent alone still gives no vanishing, anytime, minimax,
or complete-UCB-VI rate.

## Closed Gap: Actual-Sampled Successor Exploratory Behavior Expected Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-SUCCESSOR-EXPLORATORY-BEHAVIOR-EXPECTED-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticCumulativeExploratoryBehaviorRegret`.
The sampled optimistic action table is definitionally the same policy as its
actual sampled-model plan. Restricting a trajectory through coordinate `n`
then identifies that table's exploratory mixture with the concrete source
`successorPolicy n`; this policy generates coordinate `n + 1`.

A named finite sum records these actual successor policies' expected regrets.
The existing deterministic exploration comparison is applied to every sampled
table, and finite-sum algebra contributes exactly `rounds` copies of
`exploratoryBehaviorRegretCharge`. On the unchanged two-share confidence and
path-support event, all sampled plans remain optimistic and cumulative
successor exploratory-behavior expected regret is bounded by the cumulative
occupancy selected-radius sum plus that explicit charge.

The terminal inherits all finite Standard Borel, probability, sub-Gaussian,
positivity/share, exploration, bounded-mean, path-support, strict-margin, and
half-contraction contracts from the cumulative recommendation parent. The
algebraic transport only needs the valid exploration rate and true mean-reward
bound in addition to the finite spaces and probability initial law. Focused
and external-canary builds pass. The statement excludes the initial policy and,
by itself, realized sampled returns. The realized successor consumer above now
combines it with the globally centered conditional concentration route.

## Closed Gap: Actual-Sampled Cumulative Recommended Expected Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-RECOMMENDED-EXPECTED-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticCumulativeRecommendedRegret`.
Each stochastic batch coordinate is converted to its actual sampled
`EpisodeBatch` and then to the all-coordinate empirical optimistic plan. Named
finite sums collect the resulting recommended policies' expected regrets and
their occupancy selected-radius certificates. `Finset.sum_le_sum` lifts the
parent's pointwise inequalities without changing the confidence event.

Under the same two-share selected count/reward event and explicit path-support
calibration, every finite-window plan remains optimistic and the cumulative
recommended expected regret is at most the cumulative actual-sampled-model
occupancy-radius sum. The route inherits the parent's finite Standard Borel,
probability, sub-Gaussian, positivity/share, exploration, bounded-mean,
path-support, strict-margin, and half-contraction contracts. The pure finite-
sum assembly needs only the roundwise certificates.

Focused/root-facing external builds pass, and the existing reward-swap canary
still prevents a known-mean substitution. The successor exploratory-behavior
consumer above now adds the per-plan exploration charge. This parent remains
recommendation-level expected regret and by itself supplies no sampled-return
deviation, realized regret, explicit scalar rate, anytime/minimax control, or
complete UCB-VI theorem.

## Closed Gap: Finite-Round Sampled-Reward Adaptive Confidence

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CONFIDENCE`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticConfidence`.
Generic initial and successor event pullbacks transfer a uniform measurable
history-fiber bound through the adaptive Ionescu--Tulcea trajectory law. The
concrete source applies this transport to the fixed-policy sampled count and
reward event with separate local confidence shares, then unions the first
`rounds` batches to obtain the exact global bound
`ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta`.

Outside that event, every actual sampled-reward batch avoids the event for the
policy that generated it. Exploratory path support supplies the common count
floor, while the compiled fixed-policy explicit calibration fixes reward and
transition budgets. Consequently every finite-window empirical model is
globally optimistic and every recommended policy satisfies the existing
selected-radius one-episode expected-regret bound.

The terminal requires finite measurable nonempty Standard Borel State/Action,
equality and measurable singletons, a probability initial law, positive
rounds/episodes/proxy, a mean-compatible uniform sub-Gaussian reward source,
two positive confidence shares at most one, valid exploration, bounded true
means, path support, a strict local count margin, and the scalar
half-contraction. The generic event transport itself needs neither Standard
Borel nor concentration. Focused and external-canary builds pass. The
cumulative recommendation consumer above now sums the per-round selected-
radius bounds. This parent still proves no exploratory behavior, realized,
explicit-rate, anytime/minimax, or complete-UCB-VI regret theorem by itself.

## Closed Gap: Sampled-Reward Adaptive Optimistic Source

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SOURCE`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSource`.
The selector reads actual sampled rewards from the latest stochastic batch,
not the known-mean projection. A fixed-order finite argmax and a dynamic
empirical-transition kernel make the complete optimistic Bellman recursion
measurable; the source exposes exact selected-policy iid laws in every history
fiber.

The route uses finite measurable nonempty State/Action, equality/singletons, a
probability initial law, a mean-compatible reward source, fixed budgets, and a
valid exploration rate. Local retrieval is exact; Mathlib kernel-integral,
finite-sum, and order APIs close regularity. Focused modules and `Tests.Basic`
compile, and the reward-swap canary proves sampled-reward sensitivity. The
finite-round selected count/reward consumer above now closes global adaptive
confidence and pointwise optimism/recommended-regret transport, and the next
consumer now sums those recommendation bounds. Source construction alone still
gives no exploratory behavior or realized regret, anytime/minimax rate, or
complete UCB-VI theorem.

## Closed Gap: Stochastic-Reward IID Explicit Exploratory Calibration

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EXPLORATORY-PATH-SUPPORT-EXPLICIT-CALIBRATION`
now compiles in `FiniteHorizonStochasticRewardIIDExplicitCalibration`. One
common path-support visit floor replaces every coordinatewise expected-count
margin. The simultaneous reward-sum radius divided by the resulting positive
denominator gives an explicit uniform reward budget.

The transition budget is `rewardBound + 2 * rewardBudget`. Consequently the
stochastic value envelope is exactly twice that budget per remaining stage;
the existing finite-state uniform transition radius and one scalar
half-contraction prove the complete transition cover. The practical endpoint
derives the count floor for a deterministic table's exploratory policy and
invokes the sampled-reward confidence, optimism, and recommended-regret
terminal.

This remains fixed-policy iid calibration. It is a sufficient finite-sample
condition, not count-adaptive or minimax tuning, and it does not provide
history-selected policy updates, cumulative/realized regret, anytime control,
or complete UCB-VI.

The horizon-two Bool/Bool canary uses 4194304 episodes, visit floor `1/8`,
uniform exploratory actions, and nondegenerate symmetric `+/-1` rewards. Four
public axiom audits are baseline-only and placeholders are clean. Independent
review confirmed the denominator and half-contraction directions and found no
P0-P2; its unnecessary helper-regularity P3 was removed. Focused/root/Tests
and the full project gate pass.

## Closed Gap: Stochastic-Reward IID All-Coordinate Empirical-Model Confidence

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-ALL-COORDINATE-EMPIRICAL-MODEL-CONFIDENCE`
now compiles in
`FiniteHorizonStochasticRewardIIDEmpiricalRewardConfidence` and
`FiniteHorizonStochasticRewardIIDAllCoordinateEmpiricalModelConfidence`.
The route maps complete reward-bearing trajectories to `EpisodeBatch` without
replacing sampled rewards by `mdp.reward`. A visit-masked reward deviation has
a stage-coordinate sub-Gaussian MGF under the generated trajectory law; finite
iid episode sums use the conservative proxy `episodes * varianceProxy`.

The pulled-back simultaneous count event and finite reward-coordinate union are
measurable and retain separate `countDelta` and `rewardDelta` budgets. Outside
their union, strict expected-count margins control both the random empirical
reward denominator and transition-frequency denominator. Fixed reward and
transition covers then construct every field of `FiniteBatchModel.Confidence`.
The sampled-reward empirical model is globally optimistic and its recommended
policy satisfies the existing selected-radius one-episode expected-regret
bound.

This is fixed-policy iid reward-mean estimation with an intentionally coarse
reward proxy. It does not provide a count-adaptive radius, an adaptive history
source, cumulative or realized regret, anytime confidence, a minimax rate, or
complete UCB-VI.

Focused/root/`Tests.Basic` and the full project gate pass. The external
Bool/Bool horizon-one canary uses 16384 episodes and nondegenerate symmetric
`+/-1` rewards, proves all margins and covers internally, and verifies that an
actual sampled reward can be `1` while the stored mean reward is `0`.
Independent review's vacuity finding is repaired; placeholder and public-axiom
audits are clean/baseline-only.

## Closed Gap: Stochastic Common-Space L1 Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-BEHAVIOR-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceL1Consistency`.
Every scheduled realized-behavior regret coordinate is integrable and belongs
to `MemLp` at exponent one. Its expected absolute value and exact exponent-one
`eLpNorm` tend to zero, and the named `Lp Real 1` process converges to zero.

The proof does not bound sampled rewards. The deterministic `2H` envelope is
used only for selected-policy expected regret in the bounded mean-reward MDP.
The globally centered stochastic return deviation is integrated from its
sub-Gaussian MGF at tilt `1 / sqrt(proxy)`, giving the required square-root
first-moment scale. The expectation bound pays one count-event confidence
share; the parent's two-share in-probability theorem remains unchanged.

This is L1 convergence on the explicitly independent product of complete
scheduled experiments. It is not a natural nested stream and gives no
pathwise, almost-sure, anytime, stochastic reward-mean estimation, minimax, or
complete-UCB-VI result.

## Closed Gap: Stochastic Common-Space In-Probability Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceConsistency`.
The finite-window stochastic certificate is strengthened from a one-sided
realized-regret bound to an absolute bound by combining selected-policy
expected-regret nonnegativity with the exact expected-minus-global-deviation
identity and the existing two-sided return event.

The changing scheduled laws are coupled on a dependent `Measure.infinitePi`.
Every evaluation coordinate has exactly its complete stochastic trajectory law,
the realized-regret coordinate is measurable, and the pulled-back bad event has
the same two-share failure budget. The vanishing absolute envelope and failure
budget prove `TendstoInMeasure` of realized successor-average behavior regret to
zero.

This closes literal convergence in probability under the explicitly
independent product coupling. It does not construct one nested causal online
stream and gives no pathwise, almost-sure, anytime, stochastic reward-mean
estimation, minimax, or complete-UCB-VI result.

## Closed Gap: Composite Standard Borel Regularity For Stochastic Cumulative Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REGULARITY-CLOSED-REALIZED-BEHAVIOR-CONSISTENCY`
now compiles in `FiniteHorizonEpisodeBatchStandardBorel` and
`FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationRegularityClosedConsistency`.
The custom product-coordinate measurable structure on `EpisodeStep` is
identified with `State × Action × Real × State`; an induced Polish topology and
measurable embedding recover its Borel structure. Mathlib's generic countable
product then synthesizes deterministic batch trajectories; one dedicated
constant-family instance stabilizes stochastic batch-trajectory synthesis.

The finite- and all-window stochastic realized-consistency endpoints now need
only Standard Borel State/Action spaces. Callers no longer supply four indexed
batch/trajectory witnesses. The probability, support, reward-law, bounded-mean,
positive-horizon, and positive-floor contracts are unchanged. This closes only
the composite regularity boundary: scheduled windows still live on changing
sample spaces, with no shared process, convergence in probability, almost-sure
or anytime claim, reward estimation, minimax rate, or complete UCB-VI theorem.

## Closed Gap: Stochastic Cumulative Decaying-Exploration Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REALIZED-BEHAVIOR-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationConsistency`.
The source selects cumulative empirical-optimistic exploratory tables only from
the known-reward projection of stochastic history. Initial, selected-batch,
prefix/next, conditional, and complete-trajectory laws identify that projection
exactly with the deterministic cumulative source.

The deterministic decaying count/optimism/expected-behavior certificate is
pulled back and combined with the globally centered stochastic return event.
The final finite-window theorem exposes a measurable union, the exact sum of two
scheduled confidence shares, a named realized-regret violation set and its tail,
and optimism plus realized successor-average regret outside the union. The
episode-linear global variance proxy yields a normalized stochastic radius
tending to zero; the two-share failure budget and complete realized bound tend
jointly to zero.

The parent all-window theorem exposes indexed deterministic and stochastic
batch and trajectory `StandardBorelSpace` witnesses because every schedule
index has a different sample space. The downstream regularity-closed wrapper
now infers those witnesses from State/Action Standard Borel instances. This is
still not a common-process, convergence-in-probability, almost-sure, anytime,
reward-estimation, minimax, or complete-UCB-VI theorem.

## Closed Gap: Concrete Stochastic Empirical-Optimistic Realized Behavior Regret

`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EMPIRICAL-OPTIMISTIC-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticRealizedBehaviorRegret`.
The route derives global-return measurability from the finite projected table
selector, identifies the actual stochastic successor policies with projected
exploratory policies, charges their expected regret against the recommended
policies, closes the fixed-bonus occupancy average, and adds the globally
centered stochastic return radius.

The count and return events retain separate `countDelta` and `returnDelta`
budgets, with union mass bounded by the sum of their `ENNReal.ofReal` images.
The external terminal is instantiated both on the small Unit model and on the
positive Bool/Bool path-support calibration with two actions, non-degenerate
symmetric stochastic rewards, positive reward/transition bounds, and distinct
`1/2` and `1/4` confidence shares. The theorem remains successor-only and
fixed-window; schedule/vanishing-rate, initial-batch, anytime/common-space,
minimax, reward-estimation, and complete-UCB-VI claims remain open.
The final two-action canary locks the complete endpoint proposition. Its
dependent deterministic/stochastic batch and infinite-trajectory
`StandardBorelSpace` instances are still explicit assumptions, not locally
synthesized instances; a future measurable-space leaf must close that boundary.

## Closed Gap: Adaptive Stochastic Known-Mean Projection Confidence

The compiled route is
`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-KNOWN-MEAN-EMPIRICAL-OPTIMISTIC-PROJECTION-CONFIDENCE`.
`FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticProjection` constructs
the table-indexed stochastic kernel and adaptive source with every selected
policy factoring through the projected stochastic prefix. Each selected batch
maps to the deterministic fiber, and dependent `Measure.compProd` transport,
regular conditional laws, and projective-limit uniqueness identify the complete
projected trajectory with the deterministic exploratory source law.

The terminal theorem pulls back the deterministic adaptive count bad event,
proves the same `delta` mass bound under the stochastic trajectory measure, and
reuses the projected optimism and recommended-policy expected-regret conclusion.
The evidence includes the complete trajectory equality, not only a source
constructor or pointwise next-batch map.

The full-law endpoint adds a Standard Borel/nonempty deterministic batch
contract. It does not add sampled-reward boundedness or infer reward confidence,
realized behavior regret, minimax rates, or complete UCB-VI.

## Closed Gap: Stochastic Reward Erasure IID Episode-Batch Law

The route
`RL-FINITE-HORIZON-STOCHASTIC-REWARD-ERASURE-IID-EPISODE-BATCH-LAW`.
It proves that coordinatewise reward erasure maps the stochastic finite
trajectory kernel to the ordinary action/next-state trajectory kernel, then
lifts that equality through the initial-state law, finite iid episode family,
and the existing known-reward `EpisodeBatch` conversion. This is the exact law
transport needed before the deterministic empirical-transition selector can be
reused by a stochastic-reward source. It now compiles in
`FiniteHorizonStochasticRewardErasureLaw`.

Fourteen declarations cover measurable coordinate erasure, exact `Fin.cons`
commutation, a reusable two-output `compProd` map theorem, recursive finite
trajectory kernel equality, the initial-state law, finite iid family, and final
known-reward `EpisodeBatch` law. Root-imported external canaries use sampled
rewards `7` and `-3`, verify that next state `true` remains, instantiate the
two-episode law, and check that the projected empirical reward is the known
mean `0`. Focused and Tests builds pass; placeholder scanning is clean and four
representative axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`. Independent review found no P0/P1 or mathematical-law defect. Its
P2 regularity finding is repaired by recording that the final measurable
`EpisodeBatch` projection additionally needs measurable singletons for State
and Action, while the kernel, full-trajectory, and iid-erasure laws do not.
The review's P3 test findings are repaired with a Bool-action uniform policy,
a symmetric non-degenerate reward source with reward-one mass `1/2`, explicit
action preservation, and zero-horizon and zero-episode canaries.

The route retains actions and next states and discards only sampled Real reward
values. Its projected batch deliberately uses the known deterministic mean
`mdp.reward`. It therefore does not establish stochastic reward estimation,
reward confidence, adaptive count/optimism transport, realized regret, or
complete UCB-VI.

The remaining boundary is the adaptive source: its prefix-dependent selector,
exact successor stochastic iid law, projected count event, and expected-regret
consumer are not supplied by this fixed-policy transport.

## Closed Gap: Adaptive Stochastic Realized Behavior Regret Transport

The route
`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT`
now compiles in
`FiniteHorizonAdaptiveStochasticRewardRealizedBehaviorRegret`. The global
batch deviation is actual sampled return minus the selected policy's expected
return under the initial-state law. Its missing initial-state value
fluctuation is proved sub-Gaussian from the deterministic reward-mean bound,
summed over iid complete episodes, and combined with the existing
per-sampled-state return deviation using the honest
`(sqrt c_return + sqrt c_value)^2` same-space proxy.

An explicit `GlobalReturnMeasurability` contract supports the dynamic
prefix-selected statistic. The retained-input conditional law and trimmed
`condExpKernel` map feed successor coordinates `1..rounds` into the compiled
strongly-adapted tail; coordinate zero is deliberately zero. Exact cumulative
and averaged identities then rewrite realized behavior regret as expected
regret minus the globally centered return deviation. The terminal theorem
unions a caller-supplied count/optimism bad event with the return bad event and
charges two `delta` shares.

Fifty-four declarations, the root import, and external Bool/Unit canaries
compile. The canaries cover the initial marginal, both MGF layers, exact
global-centering identity, dynamic conditional law, successor conditional
MGF, positive two-round proxy, tail, regret identity, and full event transport.
Placeholder scanning is clean and four representative axiom audits report only
the standard `propext`, `Classical.choice`, and `Quot.sound` baseline.
Independent review found no P0-P2. Its P3 constant-policy test gap is repaired
by a history-sensitive Bool-action `Kernel.piecewise` global-measurability and
dynamic-law canary. A concrete nonzero terminal regret test remains assigned to
the next empirical-policy/count-event consumer.

The remaining boundary is a concrete stochastic empirical-policy source and
its count/optimism event. This route does not provide a selector, schedule,
anytime statement, minimax rate, or complete UCB-VI theorem.

## Closed Gap: Adaptive Stochastic Episode Sampled Return Tail

The route
`RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EPISODE-BATCH-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`.
now compiles in
`FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration`. It combines
the complete-episode iid sampled-return MGF with an adaptive
Ionescu--Tulcea/`piLE` martingale route. The generic `retainedInputKernel`
keeps the conditioning prefix with the next batch, and
`condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd` maps the resulting
pair through the history-selected sampled-return deviation. The source
contract records measurability of this prefix×batch statistic rather than
silently assuming a measurable policy selector.

The initial coordinate and every successor coordinate inherit the compiled iid
MGF, the increment process is strongly adapted, and the finite-round two-sided
tail uses exactly
`rounds * iidSampledCumulativeReturnDeviationVarianceProxy`. External canaries
instantiate a concrete Bool/Unit source and check the dynamic law, successor
conditional MGF, proxy `22`, and two-round tail. A second, history-sensitive
Bool-action `Kernel.piecewise` source proves that two observed prefixes select
different successor policies and unequal complete conditional batch laws. The
infinite real-reward trajectory's `StandardBorelSpace` is an explicit
regularity input because the current Mathlib instance search does not
synthesize it automatically. Independent review's weak-adaptivity-canary and
overbroad-regularity findings are repaired; only `Nonempty Action` is required
at the MGF/tail endpoints.

The theorem does not use global initial-law mean centering, cross-round
independence, or within-episode stage independence. Its globally centered
expected-to-realized regret consumer now compiles above. Concrete stochastic
policy construction, uniform/anytime confidence, optimistic planning, minimax
rates, and complete UCB-VI remain open downstream.

## Closed Gap: Finite IID Episode Sampled Return Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EPISODE-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`
now compiles in
`FiniteHorizonStochasticRewardIIDTotalReturnConcentration`. The module
constructs a finite `Measure.pi` product of complete reward-bearing
trajectories, proves exact coordinate marginals and episode-level independence,
lifts the initial-law MGF to every coordinate, and applies Mathlib's independent
sub-Gaussian finite-sum theorem. The resulting proxy is exactly
`episodes * (horizon * rewardVarianceProxy +
meanBellmanInnovationVarianceProxy rewardBound horizon)`, followed by the
fixed-sample two-sided delta tail.

The zero-episode product is also covered: it remains a probability measure,
the deviation sum and total proxy are zero, and the zero-proxy MGF compiles.
The tail intentionally requires a positive total proxy, so it does not claim a
separate zero-episode confidence-radius endpoint.

Independence is across complete episodes only. No independence between stages
inside one trajectory is introduced. Adaptive policy updates, conditional
successor episode laws, uniform/anytime control, regret, optimism, minimax
rates, and complete UCB-VI remain open.

## Closed Gap: Initial-Law Sampled Return Sub-Gaussian Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-INITIAL-LAW-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`
now compiles in
`FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration`. A reusable
finite-index `Measure.compProd` theorem lifts a common fiberwise
`HasSubgaussianMGF` proxy through an arbitrary probability mixing law. It uses
the exact Mathlib integrability/Fubini surface, then instantiates the statewise
sampled-return theorem on the full stochastic trajectory measure.

The statistic is centered by the policy value of its sampled initial state.
This does not prove concentration around the global initial-law expected value.
Its finite iid episode product/sum consumer now compiles downstream. Adaptive
confidence events, uniform/anytime
control, regret, optimism, minimax rates, and complete UCB-VI remain open.

## Closed Gap: Sampled Return Around Policy Value Sub-Gaussian Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL`
now compiles in `FiniteHorizonStochasticRewardTotalReturnConcentration`.
The actual sampled cumulative return minus `policy.valueRemaining` splits
pathwise into selected-reward noise and the mean Bellman innovation. Exact
retained-coordinate reward-kernel maps and Mathlib `add_compProd` give the
additive proxy
`remaining * rewardVarianceProxy +
meanBellmanInnovationVarianceProxy rewardBound remaining`, followed by the
fixed-horizon two-sided delta tail.

This closes the conditional composition boundary between the two preceding
concentration routes. Its initial-state-law mixture now compiles downstream,
but it does not yet provide an iid episode family, adaptive confidence event, uniform/anytime statement,
regret, optimism, minimax rate, or complete UCB-VI. Arbitrary correlated
reward/next-state sources also remain outside the product-source contract.

## Closed Gap: Mean Bellman Innovation Sub-Gaussian Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-MEAN-BELLMAN-INNOVATION-SUBGAUSSIAN-TAIL`
now compiles in
`FiniteHorizonStochasticRewardBellmanInnovationConcentration`. The statistic
sums
`mdp.reward state action + valueRemaining tail nextState - valueRemaining current state`
along the generated reward-bearing trajectory. This jointly centers policy
action and transition randomness at the recursive policy value.

The proof bounds `valueRemaining` by its remaining reward envelope, identifies
the one-step action/transition integral with the current Bellman value, and
applies the bounded-centered Hoeffding wrapper. Dropping the sampled reward
from `actionRewardStateKernel` recovers `actionStateKernel`; the recursive
kernel proof then retains next state beside the tail, uses an a.e. equality for
the duplicated next-state coordinate, and applies `add_compProd`. The total
proxy is exactly `sum k=1..remaining, (k * rewardBound)^2`, followed by the
fixed-horizon two-sided delta tail.

The randomized-action canary computes policy value `1/2`, witnesses innovation
`3/2`, computes proxy four, and instantiates the generated MGF/tail. A second
two-stage Bool-state canary gives both transition outcomes mass `1/2` and proves
that traces with first next state `true/false` have cumulative innovations
`+1/2/-1/2`. Independent review found no route defect and confirmed the
conservative `O(H^3 rewardBound^2)` proxy; its initial compile and semantic
coverage findings are resolved by these canaries. Sampled reward noise remains
separate in the preceding cumulative-deviation route, while their exact
conditional composition now compiles in the sampled total-return route above.
No uniform/anytime, regret, optimism, minimax, or complete UCB-VI claim follows
from this parent alone.

## Closed Gap: Stochastic Reward Cumulative Deviation Sub-Gaussian Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-CUMULATIVE-DEVIATION-SUBGAUSSIAN-TAIL`
now compiles in `FiniteHorizonStochasticRewardCumulativeConcentration`. The
new sampled cumulative deviation subtracts `mdp.reward` at every actual
pre-step state and sampled action. Its generated-trajectory MGF has proxy
exactly `remaining * varianceProxy`, and the module exposes the corresponding
fixed-horizon two-sided delta tail.

The recursive proof retains the sampled next state with
`Kernel.id ×ₖ tailKernel`, promotes pointwise fiber MGFs to
`Kernel.HasSubgaussianMGF`, and applies Mathlib `add_compProd`. An exact
map/compProd equality then rebuilds the original generated trace. This avoids
the weaker `horizon^2` bounded-total-return shortcut. The source's
`rewardNextStateKernel` is the conditionally independent reward/transition
product given state/action; no independence across trajectory stages is
assumed. Horizon-zero and two-step symmetric-reward canaries check the base
case, proxy two, recursive MGF, exact all-positive event mass `1/4`, and a
strict-positive-mass `delta = 3/4` tail endpoint.

This closes cumulative reward-law noise only. Transition randomness, the
Bellman value innovation, total sampled return around `valueRemaining`,
uniform/anytime control, regret, optimism, minimax rates, and complete UCB-VI
remain open.

## Closed Gap: Stochastic Reward Head Conditional Sub-Gaussian Tail

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-SUBGAUSSIAN-TAIL`
now compiles in `FiniteHorizonStochasticRewardConcentration`. It packages one
common selected-reward sub-Gaussian proxy, constructs that contract from a
common a.s. interval using the mean-compatible reward identity, and transports
it to the actual generated first reward conditioned on its sampled action.

The exact centered variable is
`headReward - mdp.reward state headAction`; the conditioning sigma-algebra is
`comap headAction`. The compiled conditional-law map feeds the local centered
conditional-MGF bridge. Mathlib `HasSubgaussianMGF.trim` and
`add_of_hasCondSubgaussianMGF` give the global MGF, and a constant full
filtration specializes the existing strongly-adapted finite-sum theorem to a
one-step two-sided delta tail.

A nondegenerate symmetric `{-1,1}` reward canary proves common interval
support, computes `intervalVarianceProxy (-1) 1 = 1`, and instantiates the
conditional MGF, global MGF, and `delta = 1/2` tail. The multi-step cumulative
reward-deviation MGF and tail now compile downstream. Transition/Bellman
innovation concentration, regret tails, and complete UCB-VI remain open.

## Closed Gap: Stochastic Reward Trajectory Head Conditional Law

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-LAW`
now compiles in `FiniteHorizonStochasticRewardConditionalLaw`. The one-step
action/reward law is exactly the policy action measure composed with the
state-frozen selected reward kernel. Consequently, the first generated reward
conditioned on the first generated action equals that selected kernel almost
everywhere at every positive recursive horizon.

The route uses `Kernel.sectR`, `Measure.ext_prod`, `Measure.fst_compProd`, and
`condDistrib_ae_eq_iff_measure_eq_compProd`, then invokes the compiled local
Real-valued bridge to obtain a trimmed `condExpKernel.map` equality. The base
conditional-law layer needs no new measurable-singleton or reward-moment
contract. The final conditional-expectation wrapper explicitly requires
standard Borel State/Action and nonempty Action; nonempty State is constructed
from its explicit starting-state argument.

Randomized Bool-action canaries instantiate the joint, `condDistrib`, and
`condExpKernel.map` statements and verify that the selected law at action
`true` assigns mass one to reward `2`; a second canary transports the
action-dependent mass-one event through the generated `condDistrib`. This
distinguishes the selected law from the reward-only mixture. This closes only
the first-step conditional-law adapter. Its bounded/sub-Gaussian selected-law
consumer, conditional/global MGF, and cumulative reward-noise tail now compile
downstream; transition/Bellman innovation and regret consumers remain open.

## Closed Gap: Stochastic Reward Trajectory Head Marginal Factorization

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-MARGINAL-FACTORIZATION`
now compiles in `FiniteHorizonStochasticRewardMarginal`. At every positive
recursive horizon, mapping a generated trace to its first
`(action,reward,nextState)` coordinate recovers `actionRewardStateKernel`.
Mapped action/reward and reward-only kernels are Markov, and the route proves
exact measurable joint-rectangle and reward-event policy-mixture formulas.

The proof uses `map_comp_right`, `fst_compProd`, measurable projection
preimages, `compProd_apply_prod`, and `prod_apply_prod`. It retains the random
policy action and actual sampled reward: a Bool-action canary gives mass `1/2`
to joint `(true,2)` and reward-only `-1` events under uniform action mixing.
A horizon-two canary checks that a one-step suffix uses stage one, and the
nondegenerate symmetric generated reward mass transports through the new
reward map to `rewardMarginalKernel`. No new boundedness, moment,
measurable-singleton, Standard Borel, or `condDistrib` contract was introduced.

This closes the generated first-coordinate marginal interface, not a regular
conditional distribution or concentration theorem. The next boundary is an
explicit filtration/disintegration transport with its Standard Borel
contracts, or a separately packaged bounded/sub-Gaussian source consumed by a
concentration route.

## Closed Gap: Stochastic Reward Trajectory Value Identity

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-VALUE-IDENTITY` now compiles
in `FiniteHorizonStochasticRewardTrajectory`. Generated finite coordinates
retain the actual sampled `(action,reward,nextState)`. The cumulative reward
sums those Real reward coordinates and is not a rewrite of `mdp.reward`.

The Real coordinate makes the trace non-finite, so the proof does not reuse
the deterministic trajectory's automatic finite-type integrability. It
recursively combines selected reward `L1`, tail `L1`, a measurable tail norm
envelope, nested `integrable_compProd_iff`, map transport, and Fubini. The
statewise expectation is `stochasticValueRemaining`; the full initial-state
expectation is both stochastic `valueAt 0` and the existing mean policy value.
Independent review found no semantic defect. Its coverage finding was resolved
by an exact canary showing that the generated symmetric source assigns mass
`1/2` to the first sampled reward being `1`.

No boundedness, second moment, sub-Gaussian, or Standard Borel contract was
added. Exact retrieval found no existing reward-bearing consumer. The explicit
first-coordinate marginals now compile downstream; remaining boundaries are
their finite-history regular-conditional transport and trajectory
concentration under separately packaged bounded or sub-Gaussian assumptions.
Correlated reward/next-state laws and complete UCB-VI remain open.

## Closed Gap: Stochastic Reward Kernel Bellman Transport

`RL-FINITE-HORIZON-STOCHASTIC-REWARD-KERNEL-BELLMAN-TRANSPORT` now compiles in
`FiniteHorizonStochasticRewardBellman`. A `MeanCompatibleRewardKernel` records
integrability of every selected Real reward and identifies its integral with
the existing `mdp.reward state action`. Its reward/next-state product kernel is
Markov and explicitly models conditional independence given `(state,action)`.

Mathlib product integrability, `Kernel.prod_apply`, and Fubini prove that the
sampled one-step value is exactly `mdp.bellmanQ`. The identity is integrated
under each policy action kernel and propagated through a separately defined
backward stochastic recursion to `valueRemaining` and `valueAt`. The existing
deterministic reward has a compiled `RewardKernel.deterministic` embedding.

Exact local/memory retrieval found no prior consumer. The route uses compiled
kernel/integral APIs, not a theorem card. It does not construct a correlated
reward/next-state law, stochastic-reward trajectory, realized return,
concentration bound, optimism theorem, regret theorem, or complete UCB-VI.
The next supporting boundary is a stochastic trajectory/value identity.

## Closed Gap: Common-Space L1 Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceL1Consistency`.
Every scheduled realized-behavior regret coordinate is `MemLp` at exponent one,
and its `eLpNorm` is exactly `ENNReal.ofReal` of the compiled expected absolute
regret. The canonical norm of `process n - 0` tends to zero.

The route also packages each coordinate as a named `Lp Real 1` value, proves
its coercion agrees almost everywhere with the original process, and proves
convergence to zero in the `Lp` topology. It uses
`memLp_one_iff_integrable`, `MemLp.eLpNorm_eq_integral_rpow_norm`,
`ENNReal.continuous_ofReal`, `eLpNorm_congr_ae`, `MemLp.toLp`, and
`Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; the standard Lp-to-measure bridge
recovers `TendstoInMeasure`.

Regularity is unchanged from the expected-absolute parent. Exact memory/local
retrieval found no prior common-space L1 consumer; the proof is a project-local
wrapper over pinned Mathlib `MemLp`/`eLpNorm`/`Lp` APIs, with RL/UCB-VI cards
serving only as route evidence. The result still concerns the independent
product of complete finite-window experiments, not a nested causal stream;
pathwise, almost-sure, anytime, stochastic-reward, minimax, and complete UCB-VI
claims remain open.

## Closed Gap: Common-Space Expected Absolute Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-EXPECTED-ABSOLUTE-REALIZED-CONSISTENCY`
now compiles in
`FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceExpectedConsistency`.
Generated adaptive successor batches are reward-consistent almost everywhere;
the deterministic reward bound therefore gives every realized-average regret
coordinate a `2*horizon` envelope and proves its Bochner integrability.

The pulled-back common bad event is measurable. Splitting its indicator from
the good event bounds expected absolute realized regret by the compiled
finite-window radius plus `2*horizon` times the real-valued failure budget.
Both terms tend to zero, yielding an explicit `Tendsto` theorem for the
expectations. The route uses the compiled exact marginals together with
`Measure.ae_compProd_of_ae_ae`, `ae_of_ae_map`, `Integrable.mono'`,
`integral_indicator`, `ENNReal.tendsto_toReal`, and `squeeze_zero`.

The regularity contract remains finite measurable nonempty state/action,
probability initial law, positive horizon/base floor, deterministic absolute
reward bound one, path support, and indexed Standard Borel witnesses. Exact
local/memory retrieval found no prior expected-absolute leaf; Mathlib
measure/integral/kernel/asymptotic APIs supply the proof, while RL/UCB-VI cards
are route evidence only. The expectation is still under the independent
product of complete finite-window experiments, not a nested causal stream;
pathwise, almost-sure, anytime, stochastic-reward, minimax, and complete UCB-VI
claims remain open.

## Closed Gap: Episodewise Common-Space Consistency In Probability

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-CONSISTENCY`
now gives the changing scheduled finite-window experiments one explicit common
probability space. `DecayingExplorationEpisodewiseWindowSpace` is a dependent
product of the scheduled trajectory types, and
`decayingExplorationEpisodewiseCommonMeasure` is the Mathlib
`Measure.infinitePi` of their exact adaptive trajectory laws. The coordinate
marginal theorem proves that projection `n` has precisely the source law used
by the compiled finite-window certificate.

The route first proves successor expected regret is nonnegative and combines
the existing expected upper bound with the sharp two-sided episodewise return
deviation. Outside the measurable count/return union, the absolute realized
average regret is therefore bounded by the same deterministic decaying bound.
Pulling this event back through each coordinate preserves its doubled failure
budget. Since both the deterministic bound and failure budget tend to zero,
the terminal theorem proves Mathlib `TendstoInMeasure` of the common-space
realized-behavior regret process to zero.

The random-variable regularity is explicit rather than implicit: finite sums
of measurable episode-return coordinates make finite-window cumulative and
average realized regret measurable, and composition with coordinate evaluation
makes every common-space regret-process coordinate measurable. The terminal
returns this family together with exact marginals and convergence in measure.

Verification closes at 17 registered declarations. The focused module builds
in 3043 jobs, the root in 3529, and full Tests in 3531; external probability,
marginal, process/measurability, finite-window, and terminal canaries compile.
Placeholder and generated-index checks are clean, five representative axiom
audits are baseline-only, and `python3 tools/bandit.py check` passes with 17 CLI
tests and one expected skip.

This is the independent-coordinate product coupling of complete finite-window
experiments. It is a valid common-space convergence-in-probability result, but
not the natural nested causal algorithm on one shared stream. It does not imply
pathwise, almost-sure, or anytime control. Stochastic reward laws, minimax
rates, and complete UCB-VI remain open.

## Closed Gap: Episodewise Decaying-Exploration Realized Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`
now closes the within-batch episode decomposition route. Complete generated
episode rows are independent product coordinates under the iid trajectory law;
that independence is transported to `iidEpisodeBatchMeasure` and composed with
full episode return. Each centered return has proxy `horizon^2`, and independent
sub-Gaussian summation yields batch proxy `episodes*horizon^2` without assuming
independence between stages of one trajectory.

The existing total-return conditional-law identification transports this MGF
to adaptive successor increments. Strong adaptation gives cumulative proxy
`rounds*episodes*horizon^2`, a two-sided return tail, and a sharp
expected-to-realized regret transport. The exact normalized radius is
`horizon*sqrt(2*log(2/delta)/(episodes*rounds))`; it is no larger than the
compiled coarse radius, inherits the decaying envelope, and tends to zero.

The concrete source terminal unions the sharp return event with the existing
count event, retains two confidence shares and roundwise optimism, and covers a
named realized-regret violation set. The all-window theorem packages every
finite window under indexed Borel witnesses together with the joint scalar
failure/regret limit. Thirty-three public declarations, focused/root/Tests
builds, numeric and typed canaries, clean placeholders, declaration retrieval,
and baseline-only axiom audits verify the route.

This dependent-family theorem now has a downstream independent-coordinate
common-space `TendstoInMeasure` consumer. It still does not itself identify a
nested shared-stream process or provide pathwise/almost-sure/anytime control,
stochastic reward laws, minimax rates, or complete UCB-VI.

## Closed Gap: Decaying-Exploration Realized Behavior Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY`
now closes the normalized reward-radius boundary of the finite-window realized
transport. The compiled proxy identities are
`batchProxy=(episodes*horizon)^2` and
`cumulativeProxy=rounds*(episodes*horizon)^2`. Consequently, for positive
episodes and rounds, the normalized radius is exactly
`horizon*sqrt(2*log(2/delta)/rounds)`; the scheduled batch size cancels.

For `q_n=n+2`, `delta_n=1/q_n`, and
`rounds_n=q_n^(horizon+4)`, elementary log and power inequalities give the
explicit bound `radius_n<=2*horizon/q_n`. The radius therefore tends to zero.
Adding it to the existing decaying exploratory-behavior expected-regret bound
gives a nonnegative realized bound tending to zero. The union failure budget
`ofReal(delta_n)+ofReal(delta_n)` also tends to zero, and both quantities
converge jointly to `(0,0)`.

At every finite window, a named realized-regret violation set is contained in
the measurable count/return bad-event union. It inherits the two-share outer
measure bound, while the complement retains roundwise optimism and the
realized average behavior-regret certificate. The all-window theorem accepts
indexed `StandardBorelSpace` witnesses for the changing scheduled batch and
trajectory types and returns the complete dependent family plus the joint
scalar limit.

This is not convergence in probability or almost-sure/pathwise convergence on
one process: the sample space and measure may change with `n`. A common-space
coupling is the next route for those modes. A sharper within-batch
episode-level concentration proof is separate; stochastic rewards, anytime
control, minimax rates, and complete UCB-VI remain open.

Independent review found no theorem defect. It did identify that declaration
retrieval truncated the terminal theorem at a multiline result-level `letI`;
the parser now preserves that binder and the complete event certificate. Direct
canaries also lock the two confidence shares and strict membership in the named
realized-regret violation set.

## Closed Gap: Finite-Window Realized Behavior Regret Transport

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT`
now compiles on the exact adaptive `EpisodeBatchTrajectory` law. Recorded
episode and batch returns are measurable, agree with generated
`MDP.cumulativeReward`, and have iid batch mean equal to `episodes` times the
selected policy's trajectory-return mean. Under `|reward|<=1`, the centered
batch return has the whole-batch Hoeffding proxy `(episodes*horizon)^2`.

The successor conditional law is mapped through total return and transported
to the trimmed `condExpKernel`. This yields strongly adapted prefix-kernel
centered increments and a two-sided finite-window return tail. Exact finite-sum
algebra proves realized cumulative regret equals `episodes` times successor
expected cumulative regret minus the centered return deviation. Only source
coordinates `1..rounds` are charged; coordinate zero remains excluded.

A generic theorem unions a measurable count bad event with the return bad
event, preserves any count-good certificate, and adds the normalized reward
radius. The concrete decaying-exploration endpoint retains roundwise optimism,
bounds the union by `ofReal delta_n + ofReal delta_n`, and returns the realized
average behavior-regret bound. The route remains finite-window and uses a
coarse batch proxy. Its normalized reward-radius asymptotic and dependent
all-window realized consistency consumer now compile downstream. This parent
still does not construct a common process across changing batch types or
establish anytime/pathwise/probability/almost-sure, stochastic-reward, minimax,
or complete UCB-VI results.

## Closed Gap: Decaying-Exploration High-Probability Behavior Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-BEHAVIOR-CONSISTENCY`
now removes the fixed-exploration residual charge. The compiled path lemmas
show that the selected state-action path floor at stage `t` is the
full-exploration floor times `gamma^(t+1)`. A full-exploration common floor
therefore yields the uniform horizon floor `baseVisitFloor*gamma^horizon` for
every `0<=gamma<=1`.

With `q_n=n+2`, the route chooses `gamma_n=1/q_n`,
`rounds_n=q_n^(horizon+4)`, `visitFloor_n=baseVisitFloor/q_n^horizon`, and
`delta_n=1/q_n`. The exact identity
`visitFloor_n*rounds_n=baseVisitFloor*q_n^4` converts the scheduled
recommendation envelope to
`16*card(State)*horizon^2/(sqrt(baseVisitFloor)*q_n^2)`. Adding the behavior
charge `horizon*(horizon+1)/q_n` still tends to zero. A product-filter theorem
combines this with the existing `ENNReal.ofReal delta_n -> 0` result.

The finite-window source theorem reuses the scheduled recommendation event,
transports its good-side bound to the exploratory successor behaviors, and
contains the behavior-regret violation set in the same measurable count bad
event. Unit canaries cover `gamma=1/4`, `rounds=1024`, the joint limit, and
typed source projections. A Bool-state/Bool-action horizon-two canary checks
the nondegenerate floor `1/8 -> 1/128` and effective visit mass `32`.

This route itself remains a dependent family of expected-regret certificates: scheduled
episode counts and trajectory types change with `n`. It does not prove that
the violation set is measurable or establish a common process, realized
regret, pathwise/probability/almost-sure convergence, stochastic rewards,
minimax rates, or complete UCB-VI. Those require a coupling/common-space or
realized-regret martingale layer. That finite-window martingale transport now
compiles downstream; common-space and asymptotic reward-radius obligations do not.

## Closed Gap: Exploratory Behavior Expected-Regret Transport

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EXPLORATORY-BEHAVIOR-REGRET-TRANSPORT`
now connects the recommendation route to the exploratory policies that
generate data. The exact PMF integral is a convex mixture of the uniform
action average and the selected action. A bounded-reward Bellman induction
then proves that exploratory-policy expected regret is at most the selected
deterministic policy's expected regret plus
`explorationRate*rewardBound*horizon*(horizon+1)`.

Finite sums give the cumulative charge `rounds*charge`, and positive-round
division gives the average charge. An explicit theorem aligns those terms with
source successor coordinates `1..rounds`; the source's initial-table policy at
coordinate zero is outside this quantity. The finite-window vanishing-delta endpoint
defines a behavior-regret violation set, includes it in the existing
measurable count bad event, inherits the same outer-measure tail, and retains
roundwise optimism. Unit canaries check the nonzero charge and explicitly
typed transport, violation, tail, and good-side projections. A two-action
one-step MDP also checks an exploratory reward expectation of `3/4` and a
nonzero selected/exploratory value gap of `1/4`.

Independent review found no P0-P2. Its three P3 findings about successor
indexing, degenerate behavior canaries, and equality wording were resolved by
the alignment theorem, the two-action canaries, and the bounded-certificate
wording; re-review found no remaining P0-P3.

This closes fixed-rate expected-regret transport only. At a fixed positive
exploration rate, the compiled certificate tends to the nonzero charge rather
than zero. The compatible decaying-exploration zero-limit consumer now
compiles downstream. Violation-set measurability,
common-process convergence, realized regret, stochastic rewards, minimax
rates, and complete UCB-VI remain open.

## Closed Gap: Vanishing-Delta High-Probability Average Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-VANISHING-DELTA-HIGH-PROBABILITY-AVERAGE-CONSISTENCY`
now specializes the explicit scheduled average route to
`delta_n = 1/(n+2)` and `rounds=n+1`. The schedule absorbs the resulting
logarithmic calibration cost while the deterministic recommendation-regret
certificate remains below the parent's delta-independent envelope
`16*card(State)*horizon^2/(sqrt(visitFloor)*sqrt(n+1))`.

The real and `ENNReal` confidence budgets tend to zero, the varying-delta
certificate tends to zero by squeeze, and a product-filter theorem proves
that both quantities converge jointly to `(0,0)`. At every finite window, a
named average-regret violation set is contained in the existing measurable
cumulative-count bad event, so `measure_mono` gives its outer-measure bound at
most `ENNReal.ofReal delta_n`. The violation set itself is not proved
measurable. The same terminal retains roundwise optimism and
the average recommended-policy expected-regret bound outside that event.

The all-window endpoint is deliberately dependent: callers provide one
`StandardBorelSpace` witness for each scheduled batch and trajectory type.
Unit canaries check `delta_0=1/2`, `delta_2=1/4`, joint convergence, a
nontrivial window terminal, and the dependent family interface. Explicitly
typed projection canaries lock violation containment/tail, good-side optimism
and average regret, and the all-window `forall n` certificate. Independent
review found no P0-P2; its P3 inferred-canary gap is resolved.

This is not a fixed-process convergence-in-probability, pathwise, or
almost-sure theorem because the scheduled sample space changes with `n`.
The budgets `1/(n+2)` are also not summable and therefore do not create an
anytime event. Fixed-rate exploratory-behavior transport and its compatible
decaying-exploration support/calibration consumer now compile downstream. The
next exact boundary is an explicit common-space embedding/coupling or a
realized-regret martingale transport; stochastic rewards, minimax rates, and
complete UCB-VI remain open.

## Closed Gap: Scheduled Adaptive Cumulative Inverse-Sqrt Average Consistency

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-SCHEDULED-AVERAGE-CONSISTENCY`
now chooses an explicit natural episodes-per-batch schedule. With `L` the
existing cumulative log factor and `T` the normalized calibration threshold,
the schedule is `Nat.ceil(max T (2*L/visitFloor))+1`.

The strict ceil successor clears `T` and gives
`L < episodes*visitFloor/2`. Consequently the exact parent average bound is at
most
`16*card(State)*horizon^2/(sqrt(visitFloor)*sqrt(rounds))`.
Mathlib's square-root at-top limit, constant-over-at-top division, and
`squeeze_zero` prove that both this envelope and the scheduled scalar bound
tend to zero along `rounds=n+1`.

The finite-window source endpoint instantiates the same measurable bad event,
`ENNReal.ofReal delta` tail, roundwise optimism, and recommended-policy average
bound at the scheduled batch size. Unit canaries at `delta=1/2` cover strict
calibration, log-mass coverage, the exact four-round envelope value eight,
scalar convergence, and the complete source terminal. Focused/root/Tests
builds, placeholder scan, baseline-only axiom audits, an independent local
statement/algebra/sample-space audit, and the full root/Tests/CLI gate pass.

This is scalar guarantee consistency plus one source theorem per finite window.
Since the schedule changes `EpisodeBatchTrajectory` with `n`, it is not a
single-process pathwise, in-probability, or almost-sure convergence theorem.
The downstream vanishing-delta dependent finite-window source family and
fixed-exploration behavior-regret transport now compile. Compatible decaying
exploration/calibration or explicit common-space embedding remains the next
exact boundary.

## Closed Gap: Average Adaptive Cumulative Inverse-Sqrt Recommendation Rate

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-AVERAGE-RECOMMENDATION-RATE`
now divides the compiled normalized recommendation-regret sum by positive
`rounds`. The named average regret remains the finite sum of recommended-policy
expected regrets divided by its number of recommendations; it is not the
exploratory behavior's regret.

The scalar proof rewrites `min rounds x / rounds` as `min 1 (x/rounds)` and
uses positive episodes, rounds, and visit floor to identify
`sqrt(rounds)*sqrt(episodes*visitFloor/2)` with
`sqrt((episodes*rounds)*visitFloor/2)`. The exact average bound is therefore
`2*horizon * min 1
  (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor) /
    sqrt((episodes*rounds)*visitFloor/2))`.

The source theorem reuses the exact normalized bad event, `ENNReal.ofReal
delta` tail, and roundwise optimism conclusion. The Unit canary uses three
recommendations, 1000 exploratory episodes per batch, total count 3000,
`delta=1/2`, and visit floor one. Focused, root, and `Tests.Basic` builds and
both public axiom audits pass.

This is the finite-window parent of the compiled explicit schedule and scalar
consistency theorem. Behavior/realized regret, stochastic rewards, minimax
rates, one-process convergence, and complete UCB-VI remain separate.

## Closed Gap: Normalized Adaptive Cumulative Inverse-Sqrt Rate

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-NORMALIZED-RATE`
now specializes the explicit two-scale route to deterministic rewards with
absolute value at most one. It fixes the zero-count budget to one and chooses
`scale = 4*card(State)*horizon*sqrt(L)/sqrt(visitFloor)` from the existing
logarithmic factor `L`.

The chosen scale satisfies the parent square-cover condition with equality.
The old half-margin threshold is dominated by, and its budget-cover threshold
is exactly,
`32*card(State)^2*horizon^2*L/visitFloor^2`. One strict inequality against the
episode count therefore constructs the complete calibration and normalized
count radius.

The same measurable event, `ENNReal.ofReal delta` tail, and optimism statement
now yield recommended-policy expected regret at most
`2*horizon * min rounds
  (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor)*sqrt(rounds) /
    sqrt(episodes*visitFloor/2))`.
The Unit canary closes three rounds at `delta=1/2`, local delta `1/12`, and
1000 episodes, so the evidence includes a nontrivial probability budget.

This remains a finite-window sum over recommended policies, not behavior or
realized online regret. Its downstream average route now exposes total
exploratory episodes `episodes*rounds`; schedule-level consistency, stochastic
rewards, minimax normalization, and complete UCB-VI remain separate.

## Closed Gap: Explicit Adaptive Cumulative Inverse-Sqrt Calibration And Rate

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-EXPLICIT-CALIBRATION-RATE`
now removes the caller-supplied roundwise calibration from the capped
path-support terminal. Let `L` be the local cumulative-count logarithmic factor
and `C = 2*card(State)*horizon*(rewardBound+budget)`. The explicit episode
threshold is the maximum of `2*L/visitFloor^2` and
`2*C^2*L/(budget^2*visitFloor^2)`; the independent scale condition is
`C^2*L <= scale^2*visitFloor`.

The exact cumulative-radius square is `k*episodes*L/2`. The threshold therefore
leaves at least half the predictable expected visits in every prefix, proves
the budget cover by a strict square comparison, and combines with the scale
condition to prove the inverse-square-root cover. The resulting constructor
builds `CumulativeInverseSqrtPathCalibration` without any roundwise caller
premise.

Every envelope is at most its cap and at most a shifted inverse-square-root
term. The finite sum is bounded by
`min (rounds*budget)
  (2*scale*sqrt(rounds)/sqrt(episodes*visitFloor/2))`; the complete endpoint
multiplies this by `2*horizon` and preserves the parent measurable event,
`delta` tail, and roundwise optimism. The Unit canary uses horizon one, 100
episodes, one round, `delta=1`, zero rewards, `budget=1`, and `scale=3`.
It checks satisfiability and endpoint composition, not a nontrivial tail bound;
an additional `Fin 3` canary expands the shifted inverse-root indices exactly
as `1,2,3` to guard the finite-sum boundary.

This parent is not a tuned/minimax UCB-VI theorem. Its downstream normalized
route now fixes reward bound, budget, and scale and discharges both scalar
calibration premises. The remaining boundary is average recommendation error
through total exploratory episodes, not exploratory behavior or realized
regret.

## Closed Gap: Adaptive Cumulative Inverse-Sqrt Path-Support Regret

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-PATH-SUPPORT-REGRET`
now compiles the deterministic consumer missing from the cumulative
count-martingale route. Its usable radius is
`TransitionCountRadius.cappedInverseSqrt`: it is `budget` at zero visits and
`min budget (scale / sqrt(count))` at positive counts. The cap and statistical
scale are independent nonnegative parameters, and the radius is antitone.

Every initial or history-selected exploratory table inherits the same
path-support expected-visit floor. These batch floors sum over each prefix;
outside the existing global martingale event, subtracting the cumulative
confidence radius yields a strict realized visit-count lower bound. Its
positivity rules out the zero-count planner branch. A roundwise
`CumulativeInverseSqrtPathCalibration` then discharges the complete finite-state
transition-coordinate/value-envelope cover with separate cap and inverse-sqrt
inequalities, and bounds the selected planner radius by
`min budget (scale / sqrt(lowerMargin))`.

The concrete terminal preserves the same measurable bad event and `delta`
tail, proves optimism, and bounds recommended-policy expected regret by the
finite sum of the round-indexed capped inverse-square-root envelopes. No
additional failure budget is introduced. The calibration is nonvacuous: a
Unit MDP with horizon one, 100 episodes, one round, `delta = 1`, zero rewards,
`budget = 1`, and `scale = 3` instantiates the calibration and full terminal.

Independent review rejected the original one-scale radius that reused
`budget` as the inverse-sqrt numerator: already for the zero-reward Unit MDP,
the zero-count value envelope forces an asymptotically incompatible scalar
cover under the current two-sided tail constant. The downstream explicit-rate
leaf now derives a closed-form sufficient two-scale calibration and simplifies
the finite sum. This parent theorem does not identify
exploratory behavior or realized regret, stochastic rewards, a minimax rate,
or complete UCB-VI.

## Closed Gap: Adaptive Cumulative Count Martingale Confidence

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-MARTINGALE-CONFIDENCE-REGRET`
now compiles the probability producer for the cumulative planner contract.
Each adaptive batch visit or joint-transition count is centered by its
measurable history-kernel integral. The exact history-selected iid batch law
and real `condDistrib`/`condExpKernel.map` bridge produce conditional
sub-Gaussian increments with the within-batch Bernoulli proxy `episodes/4` on
`Filtration.piLE`.

The cumulative two-sided tail uses the sum of those proxies, giving the
square-root `rounds*episodes` scale rather than a linear sum of batch radii.
One finite union over prefix rounds and count coordinates gives one measurable
bad event with probability at most `delta`. Outside it, paired visit and
transition deviations plus exact transition-joint factorization yield the
positive realized-denominator empirical singleton bound; zero visits use the
trivial probability-mass radius one.

The downstream inverse-square-root path-support route now constructs the
explicit `AdaptiveCumulativeCountMartingaleCover` and selected-radius envelope
from one deterministic two-scale calibration. Under that cover and envelope,
the module constructs `CoordinateConfidence`, the global cumulative contract,
and generic and concrete exploratory-source optimism/recommended-policy
expected-regret terminals. The downstream explicit-rate route closes the caller
calibration and finite-sum simplification. The next gap is parameter tuning,
not another probability-law wrapper. This
route does not prove behavior or realized regret, stochastic-reward confidence,
a minimax rate, or complete UCB-VI.

## Closed Gap: Cumulative Count-Radius Contract Route

`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-RADIUS-CONTRACT-REGRET`
now compiles the first adaptive planner/source in this branch that consumes all
observed batches rather than only the latest one. Every transition coordinate
is summed over the finite prefix; the summary is measurable, extending the
prefix adds exactly the new batch, and cumulative visit counts are monotone.
A `TransitionCountRadius` is nonnegative and antitone, so its radius decreases
along each accumulated row. The cumulative empirical kernel drives the
optimistic plan, its value is bounded by the zero-count-radius linear envelope,
and its history-selected exploratory iid batch source is measurable.

The route also reaches a global-event consumer. An
`AdaptiveCumulativeCoordinateConfidenceContract` supplies one measurable bad
event, its `ENNReal.ofReal delta` tail, and cumulative coordinate-confidence
witnesses off the event. A selected-radius round envelope then yields optimism
for every recommendation and expected recommendation regret at most
`sum round, horizon * (2 * radiusEnvelope round)`. In the Unit horizon-one
canary, prefix visit counts are `1` and `2`, while `linearDecay 4` radii are
`3` and `2`.

The statistical producer for this contract now compiles in the downstream
cumulative count-martingale route. The remaining exact gap is deterministic
calibration of a concrete antitone planner radius against its random-denominator
coordinate radius and recursive value envelope, followed by a summable
round-radius bound. Known recommendation regret is not behavior or realized
regret; stochastic rewards, minimax rates, and complete UCB-VI remain separate.

## Closed Gap: Fixed-Bonus Occupancy-Radius Envelope

`RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-OCCUPANCY-RADIUS-ENVELOPE`
now compiles through an explicit global-event terminal. A probability
`occupancySumRemaining` with constant stage cost `c` is exactly
`remaining * c`. The concrete known-reward empirical plan has reward radius
zero and fixed transition radius `transitionBonus`, so every selected radius is
that bonus. Consequently,
`adaptiveEmpiricalOptimisticOccupancyRadiusSum` is exactly
`rounds * (horizon * (2 * transitionBonus))`.

Composing this identity with the path-support episode-threshold endpoint keeps
the same measurable bad event, delta tail, and roundwise optimism, and gives
recommended expected regret at most
`rounds * (horizon * (2 * rewardBound))`. The Bool horizon-two, two-round,
bonus-one canary evaluates both the occupancy sum and terminal RHS to `8`.

This closes the abstract RHS only for the current fixed-bonus plan. It is a
linear envelope, not a statistical regret rate. The downstream cumulative
count-radius contract route now replaces latest-batch planning and accepts a
decreasing envelope, and its adaptive cumulative concentration producer now
compiles. A concrete deterministic count-radius cover and summable envelope
are still open. Stochastic rewards, behavior or realized regret, minimax
rates, and complete UCB-VI remain separate.

## Closed Gap: Path-Support Episode-Threshold Calibration

`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EPISODE-THRESHOLD-CALIBRATION`
now compiles through the adaptive global terminal. Define
`q = 4 * card(State) * horizon + 1`. The explicit threshold
`q^2 * log(2/localCoordinateDelta) / (2*visitFloor^2)` uses the exact
simultaneous coordinate share at `delta/rounds`. If the Real episode count is
strictly above it, the exact sub-Gaussian radius-square identity gives
`countRadius < episodes*visitFloor/q`.

Because `q >= 1`, this proves the strict count margin. The stronger scaled
inequality also gives
`4*card(State)*horizon*countRadius < episodes*visitFloor-countRadius`, which
proves the previous half contraction after division by the positive
denominator. The route constructs the positive reward-bound transition cover,
`SourceCalibration`, and the unchanged global confidence, optimism, and
recommended expected-regret endpoint from one episode-threshold premise.

This is a sufficient fixed-batch threshold. Its downstream fixed-bonus
occupancy sum now has an exact linear envelope, but there is still no
accumulated statistic or shrinking statistical rate. It does not model
stochastic rewards, prove arbitrary-MDP support, identify recommendation regret
with behavior/realized regret, or complete UCB-VI.

## Closed Gap: Explicit Path-Support Count And Bonus Calibration

`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EXPLICIT-COUNT-BONUS-CALIBRATION`
now compiles through the adaptive global terminal. A common state-action visit
floor below every recursive path floor times the exploratory action floor
gives every initial and successor policy an expected-count floor. The strict
scalar inequality `countRadius < episodes * visitFloor` makes the denominator
positive and bounds every transition-coordinate radius by
`2*countRadius/(episodes*visitFloor-countRadius)`.

The finite next-state sum is then bounded by `card(State)` times that uniform
radius and the linear remaining-horizon value envelope. Under
`card(State)*uniformRadius*horizon <= 1/2`, choosing
`transitionBonus = rewardBound` closes `SourceTransitionBonusCover`, constructs
`SourceCalibration`, and recovers the existing global-delta confidence,
optimism, and recommended expected-regret sum theorem.

This removes the prior caller `ExploratoryStateCountMargin` and
`SourceTransitionBonusCover` premises under explicit scalar conditions. The
downstream episode-threshold route now discharges both scalar conditions.
Occupancy-radius rates, accumulated samples, stochastic rewards, behavior/
realized regret, and complete UCB-VI remain open.

## Closed Gap: Explicit Path-Support State Reachability

`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-REACHABILITY-CALIBRATION` now
compiles through the existing global terminal. `ExploratoryPathSupport` records
an initial singleton floor and, for every positive-stage target state, one
predecessor state/action and a true-transition singleton floor. The recursive
`exploratoryPathStateLower` multiplies those floors by the uniform exploratory
action floor.

Stage zero is identified with the initial marginal using `Measure.fst_compProd`.
At successor stages, the selected transition event is contained in the target
state event; the exact visit and transition-joint factorizations then propagate
the lower bound. Because the proof is independent of the deterministic table,
it supplies `SourceStateReachability` for the initial and every adaptive
successor behavior and directly constructs `SourceCalibration`.

This closes state reachability under an explicit path-support certificate. The
downstream explicit count/bonus route now discharges the strict margin and a
nonzero cover from a common visit floor plus a half-contraction, and the further
episode-threshold route now discharges those scalar conditions. Arbitrary-MDP
support, all-predecessor sums, accumulated statistics, stochastic rewards,
behavior/realized regret, an explicit final rate, and complete UCB-VI remain
open.

## Closed Gap: Exploratory State-Reachability Calibration

`RL-FINITE-HORIZON-EXPLORATORY-STATE-REACHABILITY-CALIBRATION` now compiles
through a direct terminal theorem. The existing ENNReal uniform-exploration
floor is converted to the Real action-kernel singleton surface, multiplied by
the exact generated stage-state mass, and then by episode count. A strict bound
below this product supplies every `EmpiricalOptimisticCalibration.margin`.

`SourceStateReachability` quantifies the state-only lower envelope over the
initial and every in-horizon successor behavior policy. The unchanged
transition-radius/value-envelope requirement is named by
`SourceTransitionBonusCover`. Together they construct `SourceCalibration` and
directly recover the prior global-delta confidence, optimism, and recommended
expected-regret sum theorem.

This removes separately assumed state-action visit margins; it does not derive
the state reachability envelope, strict episode-count rate, or transition bonus
cover. Accumulated statistics, stochastic rewards, exploratory behavior or
realized regret, an explicit rate, and complete UCB-VI remain open.

## Closed Gap: Generated Stage-Visit Factorization

`RL-FINITE-HORIZON-STAGE-VISIT-FACTORIZATION` now compiles. For every valid
stage, state, and action under a fixed generated Markov-policy trajectory, the
state/action visit mass is exactly the stage-state event mass times the policy
action-kernel singleton mass. The proof follows the remaining-trace recursion,
handles the generated head directly, transports successor coordinates through
`Kernel.compProd_apply`, and then integrates the identity through the initial
state law. A named Real `stageStateProbability` exposes the public factorization.

This closes only a population-law identity. It neither proves that a state is
reachable nor that an action has positive mass. The next calibration leaf can
combine an explicit state-mass lower bound with the already compiled
exploratory action floor. Automatic reachability, bonus coverage, an explicit
rate, behavior or realized regret, and complete UCB-VI remain open.

## Closed Gap: Adaptive Exploratory Empirical Optimistic Confidence

`RL-FINITE-HORIZON-ADAPTIVE-EXPLORATORY-EMPIRICAL-OPTIMISTIC-ALL-COORDINATE-CONFIDENCE-RECOMMENDED-REGRET`
now compiles. Every latest optimistic table is mixed with uniform exploration;
the resulting action PMF gives each action at least
`explorationRate / card Action` mass and indexes the exact iid batch kernel.
Transition-count transport and the linear known-reward value envelope then
feed `EmpiricalOptimisticCalibration` and `CoordinateConfidence`.

Off one global count event, every exploratory batch recommends an optimistic
policy. The finite sum of those recommended policies' expected regrets is
bounded by the selected-radius occupancy sum. Behavior exploration and
recommendation regret are distinct surfaces.

This closes exploratory support and the calibrated recommendation-level
confidence/optimism route. State reachability and bonus coverage remain
explicit calibration assumptions. It does not prove an explicit rate,
accumulated statistics, stochastic reward confidence, behavior-policy or
realized online regret, or complete UCB-VI.

## Closed Gap: Adaptive Empirical-Transition Optimistic Source

`RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-SOURCE-COUNT-CONFIDENCE`
now compiles. Every raw episode batch is measurably compressed to its complete
finite transition-count summary. Each count row is normalized to an empirical
PMF, with an explicit fallback Dirac law at zero visits; the summary then
defines a known-reward empirical transition plan and deterministic optimistic
policy table.

The summary space is countable with measurable singletons, so the arbitrary
finite optimistic-table computation is measurable without treating a
`MarkovPolicy` structure itself as a measurable value. Mathlib
`Kernel.ofFunOfCountable` turns table-indexed generated iid batch laws into a
Markov kernel, and `Kernel.comap` along the latest-batch selector produces the
exact history-dependent source. A finite decomposition over policy tables
proves selected count-event measurability. The parent Ionescu--Tulcea route
then supplies the selected next-batch conditional law and global-delta count
confidence without caller law or measurability premises.

This closes the concrete measurable source boundary. A downstream exploratory
variant now supplies action support and compiles all-coordinate
confidence/optimism plus recommended-policy expected regret under explicit
state-reachability and bonus-cover calibration. Rewards remain known and only
the latest batch is used. Accumulated-history semantics, automatic calibration,
an explicit bonus rate, realized regret, and complete UCB-VI remain open.

## Closed Gap: Adaptive Episode-Batch Count Confidence

`RL-FINITE-HORIZON-ADAPTIVE-EPISODE-BATCH-COUNT-CONFIDENCE` now compiles. It
replaces the offline finite product by a Mathlib `Kernel.trajMeasure`: the
initial coordinate has one policy's generated iid batch law, and every
successor kernel is exactly the generated iid batch law of a policy selected
from the complete preceding batch prefix. The prefix/next-batch law is an exact
`compProd`, and under the explicit standard-Borel batch contract Mathlib's
`condDistrib_trajMeasure` identifies the regular conditional law.

The generic adapted-event layer integrates uniform history-fiber bounds with
`Measure.compProd_apply` and `lintegral_mono`, then uses equal shares
`delta / rounds` for one finite global event. Its RL consumer rewrites every
history fiber to the compiled selected-policy simultaneous-count tail. Outside
the event, all visit and transition count coordinates satisfy their strict
deviation bounds relative to the policy actually selected at that round. No
batch independence is assumed.

This closes the supplied-source adaptive law/count-confidence transport. The
concrete known-reward/latest-batch empirical-transition optimistic producer now
compiles downstream. Adaptive reward consistency, calibrated full model
confidence, accumulated-history updates, cumulative bonus control, and
realized regret remain open.

## Closed Gap: IID Multibatch Cumulative Confidence Regret

`RL-FINITE-HORIZON-IID-MULTIBATCH-CUMULATIVE-CONFIDENCE-REGRET` now compiles.
It places finitely many copies of the fixed-policy iid episode-batch law under
one Mathlib `Measure.pi`. Evaluation is measure preserving, so every pulled-back
round event has exactly the compiled single-batch marginal probability at local
budget `delta / rounds`; the finite equal-share union therefore retains global
failure mass at most `delta`.

Generated reward consistency is pulled back almost everywhere through every
product coordinate. Off the union, the route constructs a confidence witness
for every batch-specific empirical model, proves every model optimistic, and
sums the corresponding optimistic-policy expected-regret inequalities with
`Finset.sum_le_sum`.

This closes an independent offline multibatch theorem. The data-generating
policy is fixed even though the derived optimistic policy varies by batch. The
finite sum is a sum of one-episode expected regrets; it is not realized online
cumulative regret. Adaptive episode histories, cumulative bonus rates, and
complete UCB-VI remain open.

## Closed Gap: IID All-Coordinate Finite-Batch Confidence

`RL-FINITE-HORIZON-IID-ALL-COORDINATE-FINITE-BATCH-CONFIDENCE` now compiles.
The canonical generated empirical model uses reward radius zero and one fixed
transition budget. Its transition coordinate radius is
`2 * countRadius / (expectedCount - countRadius)`: the all-coordinate strict
margin makes the denominator positive, and the simultaneous good event makes
the realized visit count strictly larger, so the random-denominator transition
bound transports in the required direction.

Exact generated rewards and the probability empirical kernel give the explicit
noncircular upper-value envelope
`remaining * (rewardBound + transitionBudget)`. Given a deterministic finite
coordinate-radius cover, the route constructs every field of
`FiniteBatchModel.Confidence`; mapped iid batches have a witness a.e. outside
the unchanged global-delta count event. Each witness then supplies global
optimism and the existing selected-radius one-episode expected-regret bound.

This closes fixed-policy finite-batch confidence, not adaptive multi-episode
UCB-VI. The all-coordinate occupancy margin and deterministic cover are real
contracts, not consequences of partial eligibility. Stochastic rewards,
adaptive policy updates, cumulative bonus summation, and cumulative regret
remain downstream.

## Explicit-Policy Canonical UCB Trajectory Route

`UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-EXPLICIT-POLICY-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. The canonical successor-action conditional law is identified
with `Kernel.deterministic (realHistoryNextArm hK (c * sigma2) n)` almost
everywhere on the relevant finite-history marginal. This is obtained from
Mathlib `condDistrib_comp_self` on the canonical arm stream and transported to
the fresh `Kernel.trajMeasure` process through the complete trajectory
`IdentDistrib` witness.

The route also transports the measurable policy graph, producing one
full-measure event on which the initial action is `initializationArm hK 0` and
every successor action follows `realHistoryNextArm` on its actual finite pair
history. Its terminal theorem pairs that event with the existing `c=4`
armwise-bounded expected-average `Tendsto` result on the same process. The
kernel equality is not global on null histories. Identification of the
adaptive next-unused reward coordinate with the selected stationary law
`nu action` remains a separate route.

## Canonical-Kernel Recursive UCB Trajectory Route

`UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-ARMWISE-BOUNDED-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. It packages the canonical arm-stream initial/successor action
`condDistrib` kernels as a `Thompson.HistoryAlgorithm` and the matching reward
kernels as a `Thompson.HistoryEnvironment`. Mathlib-backed
`Thompson.canonicalHistoryTrajectoryMeasure` then uses `Kernel.trajMeasure` to
generate a fresh pair trajectory, rather than mapping a pre-existing stream
sample through a source function.

The canonical split-source theorem supplies all four exact
`RealStationaryUCBSequence` fields for the generated coordinate process. A
finite-arm wrapper internalizes the Markov instance, and armwise-bounded laws
yield the same nonnegative logarithmic expected-regret envelope and vanishing
`n+1` average with no caller sample space, traces, or law bundle. This closes
the non-reparameterized canonical-kernel generator. Its explicit
`realHistoryNextArm` action-policy consumer now compiles downstream. The
selected `nu` reward-kernel identification and literal LML import remain.

## Measure-Preserving External UCB Source Route

`UCB-REAL-STATIONARY-MEASURE-PRESERVING-SOURCE-ARMWISE-BOUNDED-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. Its generic producer derives the complete
`RealStationaryUCBSequence` bundle by composing canonical arm-stream action and
reward traces with a measurable measure-preserving source. Instead of
rewriting a proof-dependent finite-measure instance inside `condDistrib_map`,
the proof transports the conditioning and joint pair pushforwards, applies
`compProd_map_condDistrib`, and uses conditional-distribution uniqueness.

The concrete terminal specializes the source to `Prod.fst` on
`armStreamMeasure nu` times an arbitrary auxiliary probability measure, then
reuses the armwise-bounded external pointwise and `Tendsto` consumers. This
closes a concrete external product-space producer with no caller split laws,
action/reward traces, means, MGFs, trajectory law, or common support interval.
It is still a canonical process under a measure-preserving reparameterization;
the downstream canonical-kernel trajectory now provides an independent
recursive producer. Independent review found no P0-P2; its
two metadata P3 findings were integrated, and the full project gate passed.

## External Stationary Armwise-Bounded UCB Consistency Route

`UCB-REAL-STATIONARY-ARMWISE-BOUNDED-FINITE-ARM-LAWS-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. The generic support theorem uses the complete trajectory law from
`RealStationaryUCBSequence`, projects it to an action-trace law, and transports
the measurable regret integral exactly. Its practical terminal combines that
transport with the armwise-bounded canonical route to prove a fixed external
process has a logarithmic expected-regret envelope and vanishing `n+1` average.

This closes the asymptotic consumer side of the local LML-compatible field
bundle. Measure-preserving and fresh canonical-kernel trajectory producers now
construct those fields without direct split-law premises, but the pinned LML
declaration is not imported. Explicit deterministic-policy/stationary-reward
kernel identification or a compatible toolchain import remains, while concentration,
split-to-joint assembly, trajectory uniqueness, and asymptotic transport are
already compiled.
Two read-only review passes found no P0-P2 issue, including after the public
statement indexability refactor; their metadata-only P3 findings were
integrated into the obligation, card, generated indexes, trials, and review
report.

## Armwise-Bounded Real Arm-Law One-Policy Route

`UCB-ARM-STREAM-ARMWISE-BOUNDED-FINITE-ARM-LAWS-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. It derives a centered MGF separately under every `armLaw arm`
using `Set.Icc (lo arm) (hi arm)` and that law's own identity integral. The
existing direct consumer preserves this armwise proxy family until its padded
finite maximum is chosen as the shared UCB scale.

This closes the arm-dependent bounded source-law gap for fixed-policy,
fixed-measure expected consistency. There is no common interval, caller mean,
MGF, proxy ceiling/positivity, pointwise nondegeneracy, default action, horizon,
delta, measurability, or integrability premise. External process production
and pathwise/probability/almost-sure/Hannan/minimax routes remain separate.
Independent read-only review found no P0-P2 issue; its metadata-only P3 was
integrated into the obligation, indexes, trial ledger, and review evidence.

## Bounded Real Arm-Law One-Policy Route

`UCB-ARM-STREAM-BOUNDED-FINITE-ARM-LAWS-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. `Kernel.ofFunOfCountable` packages `Fin K -> Measure Real`, and
the pointwise probability witnesses supply `IsMarkovKernel`. A supporting
direct-sub-Gaussian consumer raises armwise proxies to the positive padded
finite maximum; the bounded terminal derives each genuine proxy and centered
MGF from common a.s. interval support and the kernel's own identity integral.

This closes the common-bounded practical source-law gap for fixed-policy,
fixed-measure expected consistency. No caller mean, MGF, proxy ceiling,
positivity, default action, horizon, delta, measurability, integrability, or
`lo<hi` remains. Zero-width support is valid, while `lo>hi` makes the support
contract inconsistent with the probability laws. Arm-dependent bounds now
compile downstream; external process-law production and
pathwise/probability/almost-sure/Hannan/minimax routes remain separate.

## Canonical Arm-Stream One-Policy Consistency Route

`UCB-ARM-STREAM-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY` now compiles. Its
terminal theorem fixes one `armStreamAction` and one `armStreamMeasure` across
all horizons and proves the exact expected Real pseudo-regret divided by
`n+1` tends to zero. The proof specializes the exact LML-shaped finite-horizon
bound at `c=4`, controls its finite inverse-power tail by a convergent cubic
NNReal p-series, obtains a fixed nonnegative finite-arm coefficient, and uses
the existing `O(log(n+1))`, `log=o(n+1)`, and quotient-limit APIs.

This closes the previously open shared-measure, one-policy expected-consistency
gap for the canonical Real arm-stream process. The downstream practical route
now constructs its kernel and centered MGFs from common-bounded Real arm laws;
a non-reparameterized external `RealStationaryUCBSequence` producer remains separate. It
is not pathwise, in probability, almost sure/Hannan, minimax, or a literal LML
import.

## Armwise-Bounded Sampled UCB Explicit Route

`UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPLICIT-EXPECTED-PSEUDOREGRET`
now compiles. Its terminal gives both nonnegativity and the exact fixed-model
coefficient times `1 + log(T+1)` for the named sampled expected pseudo-regret.
It accepts per-arm probability laws, armwise real bounds, a.e. measurable
rewards, a.s. armwise support, exact means, a default arm, and
`2*K <= T+1`.

The direct practical producer derives `0<T` from `model.hK` and the horizon
condition, reconstructs the canonical pair/kernel surfaces, and uses the
positive padded finite-arm proxy. The armwise consumer extracts Hoeffding MGFs
from the existing centered-law producer. Its bounded-MGF theorem accepts
zero-width support without `lo arm < hi arm`; padding separately gives the UCB
proxy strict positivity, while inverted intervals make the support premise
inconsistent. Thus no separate `hT`, direct MGF, law, positivity, or
integrability premise leaks to callers. This closes the practical pointwise
envelope for the current
horizon-indexed sampled family; the separate canonical arm-stream theorem now
closes the one-policy/shared-measure expected-consistency boundary.

## Armwise-Bounded Sampled UCB Consistency Route

`UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. Its public terminal accepts per-arm probability laws, armwise
real intervals, a.e. measurable Rat-to-Real rewards, per-arm a.s. support,
exact integrals equal to `model.mean`, and a default arm. It extracts direct
MGF witnesses from the existing armwise bounded centered-kernel producer,
then reuses the exact sampled Big-O, little-o, and Tendsto parent.

Unlike the older fixed-horizon armwise theorem, this route has no pointwise
`lo arm < hi arm`: the bounded-MGF source accepts zero-width support, and the
parent pads the possibly zero finite maximum before UCB positivity is required.
Inverted intervals make the probability-support premise inconsistent. This closes the armwise
bounded stationary source-law boundary for horizon-indexed expected-average
consistency. It does not prove one-policy anytime, pathwise/probability/a.s.,
minimax, or complete-UCB consistency.

## Common-Bounded Sampled UCB Consistency Route

`UCB-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. Its public terminal accepts per-arm probability laws, a common
real interval, a.e. measurable Rat-to-Real rewards, a.s. interval support,
exact integrals equal to `model.mean`, and a default arm. The bounded centered
Hoeffding theorem supplies direct MGF witnesses internally, after which the
compiled practical parent proves the exact sampled expected family is
`O(log(T+1))`, `o(T+1)`, and average-consistent.

There is intentionally no `lo < hi` contract: the source proxy may be zero,
while the parent uses a finite-arm maximum padded by one for UCB positivity.
This closes the common-bounded source-law boundary only. It does not establish
a single anytime policy, pathwise/probability/almost-sure convergence,
minimax regret, or complete UCB. The arm-dependent bounded-interval consumer
now compiles downstream.

## Practical Finite-Arm UCB Consistency Route

`UCB-FINITE-ARM-SUBGAUSSIAN-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY`
now compiles the stationary finite-arm consumer of the canonical sampled-pair
asymptotic route. Its public theorem assumes only per-arm probability laws,
exact integrals equal to `model.mean`, direct centered `HasSubgaussianMGF`
witnesses, armwise NNReal proxies, and a default arm.

The initial pair law is the measurable pushforward of the default arm reward
law, successors use `contextIndependentOfActionLaws`, and the existing
centered-law constructor derives integrability and mean zero. The padded
finite-arm maximum proves both a uniform cross-horizon variance ceiling and
strict positivity, including all-zero genuine proxy families. The exact
sampled `(trajectory (t+1)).1` expected regret is `O(log(T+1))`, `o(T+1)`,
and its named average tends to zero.

Focused, root, and external `Tests.Basic` builds pass; seven declaration
checks, a full terminal application, an empty placeholder scan, and
baseline-only public axiom audit cover the new surface. The remaining boundary
is not pair-law or variance transport: it is deriving these direct MGF
contracts from practical bounded laws, or separately developing a one-policy
anytime/almost-sure route. No such stronger conclusion is claimed here.

## Latest Conditional-Law Route

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY`
now compiles the fixed-model asymptotic consumer of the sampled-successor Real
theorem. At horizon `T`, it uses the exact canonical pair policy and measure
with `delta_T=1/(T+1)`, names the resulting Real expected pseudo-regret, proves
it is `O(log(T+1))` and `o(T+1)`, and proves expected pseudo-regret divided by
`T+1` tends to zero.

The scheduled algebra keeps the exact positive-gap filter and derives the
fixed coefficient `128*sigma2/gap + 16 + 3*gap` from the parent 32/4/2 budget
and `T*delta_T<=1`. The only strengthened cross-horizon contract is a uniform
variance ceiling for every generated context and arm. No caller integrability,
selected law, reward range, or trajectory-law premise is introduced. This is
not one-policy anytime control, pathwise/probability/almost-sure consistency,
minimax regret, or the complete UCB theorem.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-SAMPLED-SUCCESSOR-REAL-TEXTBOOK-GAP-SUM-PSEUDOREGRET`
now compiles the canonical pair theorem directly for sampled successor actions
`(trajectory (t + 1)).1`. The supporting declaration proves that this complete
shifted sampled action trace agrees a.e. with the reward-generated UCB regret
action by combining the canonical per-time policy law with `ae_all_iff` and
`funext`. `integral_congr_ae` then transports the existing Real endpoint.

The equality is only a.e. under the same pair measure, and pair coordinate
zero is intentionally outside the `T` charged pseudo-regret rounds. No public
assumption changes: variance remains restricted to `i < T - 1`, and there is
no caller integrability, range, selected-law, all-arm positivity, all-time
variance, event-measurability, or `delta <= 1` premise. Its fixed-model
expected-average asymptotic consumer now compiles above; anytime confidence
and a complete UCB theorem remain open.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-REAL-TEXTBOOK-GAP-SUM-PSEUDOREGRET`
now compiles the direct Real/Bochner expectation endpoint on the same
canonical action/reward pair `trajMeasure`. It derives finite-horizon
integrability from measurable reward coordinates and bounded pull counts,
consumes the pair ENNReal theorem, proves the finite RHS is not infinity, and
normalizes it to the explicit positive-gap Real sum. No `ENNReal.toReal`
appears in the public statement.

The regularity surface is unchanged: probability initial pair law, measurable
context/mean, `CenteredRewardKernelLaw`, stationary model means, positive
`T`, `sigma2`, and `delta`, and variance only for `i < T - 1`. No caller
integrability, reward/mean range, selected-law, all-arm positivity, all-time
variance, event measurability, or `delta <= 1` premise is added. Its direct
sampled-successor and fixed-model expected-average consumers now compile
above; anytime confidence and a complete UCB result remain open routes.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET`
now compiles the textbook positive-gap ENNReal pseudo-regret endpoint for the
concrete generated finite-history UCB policy on the canonical action/reward
pair `trajMeasure`. It consumes the exact explicit-threshold theorem below and
the existing finite-arm algebra, with no new probability or conditional-law
argument.

For each strictly positive gap `g`, the threshold contribution is bounded by

```text
32 * sigma2 * logBudget / g + 4 * logBudget + 2 * g.
```

The conclusion filters zero-gap arms and preserves the confidence-failure term
`ofReal(g) * (T * ofReal(delta))` exactly. It retains variance only for
`i < T - 1` and the explicit `CenteredRewardKernelLaw`, including its bundled
pointwise integrability/MGF fields. No selected-reward trajectory law,
raw/mean ranges, all-arm positivity, separate ambient integrability,
`delta <= 1`, or event-measurability premise is added. The result is still
fixed-horizon and ENNReal-valued; its direct pair-surface Real expectation
consumer now compiles above, while sampled-coordinate form, asymptotic
normalization, and anytime UCB remain separate.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`
now compiles the finite-arm ENNReal pseudo-regret endpoint for the concrete
generated finite-history UCB policy on the canonical action/reward pair
`trajMeasure`. It shifts generated successor actions `1, ..., T` onto the
standard pseudo-regret coordinates `0, ..., T - 1`, then applies the generic
gap-weighted count assembly.

Only arms with strictly positive model gap request the preceding canonical
expected-count theorem. `FiniteBanditModel.gap_nonneg` and the generic consumer
remove zero-gap terms, so there is no exposed all-arm positivity assumption.
The exact RHS is the finite sum of

```text
ofReal(gap) * explicitThreshold(gap)
  + ofReal(gap) * (T * ofReal(delta)).
```

The theorem keeps `CenteredRewardKernelLaw`, stationary model means, positive
`T`, sigma2, and delta, and variance only for `i < T - 1`. It adds no caller
selected-reward law, score source, reward/mean ranges, separate ambient/process
integrability premise, event measurability, all-time variance, or
`delta <= 1`; the centered kernel law itself still bundles pointwise
selected-law integrability and sub-Gaussian MGF fields. This is a fixed-horizon
explicit-threshold ENNReal result; its textbook reciprocal-gap consumer now
compiles above. Real expectation, anytime confidence, and asymptotic regret
remain separate.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-EXPLICIT-THRESHOLD-EXPECTED-PULLCOUNT`
now compiles the first concrete generated-UCB expected-count endpoint on the
canonical action/reward `trajMeasure`. For any chosen arm with positive
stationary gap, the supporting theorem bounds the event that its successor
pull count at `T + 1` exceeds the explicit one-more-than-ceiling threshold by
`ENNReal.ofReal delta`. The endpoint integrates that count as an ENNReal lower
integral and obtains

```text
explicitThreshold + T * ENNReal.ofReal delta.
```

The prior canonical generated large-gap theorem is the only probabilistic
input. Existing deterministic threshold inversion supplies the explicit
integer threshold; pair reward-coordinate measurability is automatic, and the
generic consumer derives generated-action/count measurability and the count
bound by `T`. The theorem adds only a positive chosen-arm gap to the preceding
contracts. It has no caller source, selected-reward law, raw/mean ranges,
integrability, all-time variance, or `delta <= 1` premise. This one-arm result
is now consumed by the finite-arm pseudo-regret endpoint above; Real
expectation and anytime confidence remain separate.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-RANDOM-WIDTH-LARGE-GAP-EVENT`
now closes the concrete generated finite-history UCB score event on the
canonical Mathlib action/reward `trajMeasure`. The public theorem constructs
the policy/state and initialized score-max source internally and bounds its
strict random-width large-gap event by `ENNReal.ofReal delta`.

The concentration theorem observes the sampled pair action, whereas the source
uses the reward-history generated action. The proof keeps this distinction:
the canonical successor action law gives only a.e. equality, `ae_all_iff`
assembles every successor time, and shifted-action extensionality transports
pull counts, reward sums, empirical means, and radii from the generated bad
event to the sampled bad event. `K > 0` supplies `Nonempty (Fin K)` locally.
Only `i < T - 1` selected-history variance is required, with no caller source,
selected-reward law, raw/mean ranges, all-time variance, event measurability,
or `delta <= 1`. Its positive-gap explicit-threshold expected-count consumer
now compiles above; anytime confidence, all-arm summation, and regret remain
separate.

`UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-RANDOM-WIDTH-LARGE-GAP-EVENT` now
compiles the first UCB score consumer directly on the canonical Mathlib
Ionescu--Tulcea action/reward trajectory. It takes an initialized score-max
source over the sampled action/reward coordinates and bounds its strict
large-gap event by `ENNReal.ofReal delta`.

The proof consumes the canonical named finite-arm/time empirical-mean event.
Outside that event, the existing deterministic score algebra gives
`meanGap <= 2 * realizedRadius`, contradicting the source event. The measure,
sampled coordinates, confidence radius, and horizon family remain unchanged.
Only `i < T - 1` variance is required; no caller selected-reward law, raw/mean
range, all-time variance, or event measurability is added. The current score
source fixes `Action : Type`. Concrete generated-UCB source construction,
a.e. sampled/generated event transport, expected-count, explicit
pseudo-regret, and textbook gap-sum consumers now compile downstream;
uniform-time confidence, sampled-coordinate presentation, Real expectation,
and asymptotic normalization remain separate.

## Latest Route: One-Policy Power-Of-Two Forcing

The route now compiles through
`OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-HIGH-PROBABILITY-AVERAGE-PSEUDOREGRET-CONSISTENCY`.
One horizon-independent policy has an exact initial/forced/nonforced
pseudo-regret decomposition, a same-measure all-time confidence tail, and a
scalar all-horizon violation budget. The exact threshold includes
`(Nat.log2 horizon + 1) * (2 * S * Real.sqrt L2)` and has fixed-model growth
`O(sqrt (horizon + 1) * log (horizon + 1))`, without another union bound or a
horizon-indexed policy family. It is now also compiled as `o(horizon + 1)`;
the exact average budget tends to zero and bounds complete pseudo-regret per
round outside the unchanged violation event. The compiled endpoint now applies
a pathwise squeeze there, names the exact negated-`Tendsto` failure set, includes
it in the parent event, and bounds its outer measure by the same fixed `delta`
under the same policy and canonical measure.

This closes the selected fixed-confidence power-of-two theorem route. It is
not convergence in probability as the horizon grows, probability-one or
almost-sure/Hannan consistency, or an expected-regret theorem. The subsequent
exact sparse EXP3 route now also compiles: fixed parameters eventually make the
four named schedule inequalities automatic, select the refined
`16 * gamma_T * T` best-arm threshold, and preserve the parent outer-measure
tail surfaces without another union bound or policy change. Its horizons still
index distinct internally tuned generated measures, so it is not an anytime
single-policy result. A new unfinished route remains to be selected.

This audit answers a blunt question: how far is ABRL from fully reproducing the
classic bandit textbook proof weapons and the Mathlib-level foundations they
depend on?

Short answer: ABRL remains incomplete at the full multi-algorithm roadmap
level, but the local OFUL route is no longer only deterministic bookkeeping.
It now contains compiled probability, conditional-expectation, concentration,
generated-trajectory, all-time confidence, explicit regret, stopping-time,
and power-of-two forced-policy consumers. Broad UCB/Thompson/EXP3/Tsallis/RL
completion claims remain out of scope until their own terminal routes compile.

## Current Evidence

Current local evidence:

| Artifact | Count | Meaning |
| --- | ---: | --- |
| LML theorem cards | 6 | external Lean theorem-card routes, not local proofs |
| Mathlib retrieval cards | 17 | import/search routes for reusable leaves |
| textbook cards | 3 | Bubeck-Cesa-Bianchi, Lattimore-Szepesvari, Slivkins |
| paper cards | 18 | algorithm/frontier source routes |
| scenario cards | 18 | current bandit/RL taxonomy |
| proof weapon cards | 8 | upper-agent route inspiration only |
| compiled local finite-bookkeeping leaves | 37 | local dependency-light leaves, including pull-count prefix congruence and the `List.range` pull-count, reward-sum, filtered reward-sum, and pseudo-regret bridges |
| compiled local finite-bandit model-invariant leaves | 6 | `FiniteBanditModel.gap_bestArm`, `FiniteBanditModel.mean_le_bestArm_mean`, `FiniteBanditModel.gap_nonneg`, `FiniteBanditModel.maxGap`, `FiniteBanditModel.gap_le_maxGap`, and `FiniteBanditModel.maxGap_nonneg` |
| compiled local Mathlib finite-wrapper leaves | 3 | `pullCount_eq_finset_filter_card`, `sumRewards_eq_finset_filter_sum`, and `pseudoRegret_eq_finset_sum` |
| compiled local regret-decomposition leaves | 1 | `pseudoRegret_eq_finset_sum_gap_mul_pullCount` |
| compiled local regret-count-bound leaves | 3 | Rat-valued, Nat-valued, and uniform Nat count-bound-to-regret scaffolds |
| compiled local pull-count decomposition leaves | 1 | `finset_sum_pullCount_eq_time` |
| compiled local measure-foundation leaves | 3 | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward` |
| compiled local probability-union leaves | 1 | `ProbabilityUnionBound.measure_biUnion_finset_le`, `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`, and `ProbabilityUnionBound.measure_iUnion_fintype_le_sum`, Mathlib-backed finite-union outer-measure wrappers for explicit `Finset` and `[Fintype]` event families, including nonempty-`Finset` equal-share `delta/card` normalization; no event measurability or probability-measure assumption |
| compiled local UCB tail-summability leaves | 1 | `UCBSummability.finiteHorizonBadEvent`, `UCBSummability.measure_finiteHorizonBadEvent_le_sum`, and `UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum`, an abstract finite-arm finite-horizon bad-event summability wrapper consuming per-arm/per-time ENNReal tail bounds; no UCB log/sqrt tail producer or final regret theorem |
| compiled local UCB confidence-algebra/event leaves | 16 | `UCB.confidenceScore`, `UCB.meanGap`, `UCB.meanGap_le_two_radius_of_confidenceScore_max`, `UCB.not_two_radius_lt_meanGap_of_confidenceScore_max`, `UCB.upperConfidenceBad`, `UCB.lowerConfidenceBad`, `UCB.confidenceBadEvent`, `UCB.meanGap_le_two_radius_of_not_confidenceBadEvent`, `UCB.measure_confidenceBadEvent_le_sum_upper_lower`, `UCB.measurableSet_upperConfidenceBad`, `UCB.measurableSet_lowerConfidenceBad`, `UCB.measurableSet_confidenceBadEvent`, `UCB.confidenceBadEventAt`, `UCB.measurableSet_confidenceBadEventAt`, `UCB.finiteHorizonConfidenceBadEvent`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_sum_upper_lower`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_tail_sum`, `UCB.not_confidenceBadEventAt_of_not_finiteHorizonConfidenceBadEvent`, `UCB.meanGap_le_two_radius_of_not_finiteHorizonConfidenceBadEvent`, `UCB.mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max`, `UCB.scoreMaxEvent_subset_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap`, `UCB.upperConfidenceBad_subset_absDeviation`, `UCB.lowerConfidenceBad_subset_absDeviation`, `UCB.measure_upperConfidenceBad_le_absDeviation`, `UCB.measure_lowerConfidenceBad_le_absDeviation`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum`, `UCB.chebyshevAbsDeviationTail`, `UCB.measure_absDeviation_le_chebyshev_tail`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_chebyshev_tail_sum`, `UCB.subGaussianOneSidedDeviationTail`, `UCB.measure_upperConfidenceBad_le_subGaussian_tail`, `UCB.measure_lowerConfidenceBad_le_subGaussian_tail`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_oneSided_tail_sum`, `UCB.subGaussianOneSidedDeviationTail_le_exp_neg_budget`, `UCB.measure_upperConfidenceBad_le_subGaussian_exp_neg_budget`, `UCB.measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_exp_neg_budget_sum`, `UCB.subGaussianBudgetRadius`, `UCB.subGaussianBudgetRadius_nonneg`, `UCB.subGaussianBudgetRadius_sq_domination`, `UCB.subGaussianOneSidedDeviationTail_budgetRadius_le_exp_neg_budget`, `UCB.measure_upperConfidenceBad_le_subGaussian_budgetRadius`, `UCB.measure_lowerConfidenceBad_le_subGaussian_budgetRadius`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_budgetRadius_sum`, `UCB.exp_neg_log_eq_inv`, `UCB.subGaussianLogBudgetRadius`, `UCB.subGaussianLogBudgetRadius_apply`, `UCB.subGaussianLogBudgetRadius_nonneg`, `UCB.subGaussianLogBudgetRadius_sq_domination`, `UCB.subGaussianOneSidedDeviationTail_logBudgetRadius_le_inv_scale`, `UCB.measure_upperConfidenceBad_le_subGaussian_logBudgetRadius`, `UCB.measure_lowerConfidenceBad_le_subGaussian_logBudgetRadius`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_logBudgetRadius_inv_scale_sum`, `UCB.subGaussianConstantLogBudgetRadius`, `UCB.subGaussianConstantLogBudgetRadius_apply`, `UCB.subGaussianConstantLogBudgetRadius_nonneg`, `UCB.subGaussianConstantLogBudgetRadius_sq_domination`, `UCB.constant_invScale_double_sum`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_constantLogBudgetRadius_card`, `UCB.constant_invScale_double_sum_le_of_real`, `UCB.textbookDeltaScale`, `UCB.textbookDeltaScale_pos`, `UCB.textbookDeltaScale_total_inv_budget_eq_delta`, `UCB.constant_invScale_double_sum_textbookDeltaScale_le_delta`, `UCB.subGaussianTextbookDeltaRadius`, `UCB.subGaussianTextbookDeltaRadius_apply`, `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.measure_scoreMaxEvent_le_subGaussian_textbookDeltaRadius_delta_of_gap`, `UCB.subGaussianAbsDeviationTail`, `UCB.measure_absDeviation_le_subGaussian_tail`, and `UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_tail_sum`, the deterministic and event-level good-event/index-maximality consumers showing `gap <= 2 * chosenRadius` plus single-time and finite-horizon confidence bad-event union-bound, measurability, finite-horizon good-event-to-gap consumer plus large-gap score-max bad-event subset, abstract tail-budget, absolute-deviation tail-adapter, finite-variance Chebyshev tail producer, one-sided sub-Gaussian upper/lower confidence-failure producer, one-sided radius-budget simplification to `exp(-budget)` under `0 < proxy` and `2 * proxy * budget <= radius^2`, concrete square-root budget radius instantiation using `sqrt (2 * proxy * budget)`, schedule-agnostic logarithmic budget radius instantiation using `sqrt (2 * proxy * log scale)` with inverse-scale tails under `0 < scale`, constant-scale inverse-tail double-sum folding into `T` and `Fintype.card Arm` nsmul, textbook finite-horizon delta-scale allocation `2 * T * |Arm| / delta` with `delta` confidence-bad-event and large-gap score-max event bounds, and abstract two-sided sub-Gaussian absolute-deviation producer wrappers; no concrete empirical-mean measurability, expected pull-count theorem, or final regret theorem |
| compiled local UCB selected-action bridge leaves | 1 | `UCB.selectedEvent_subset_scoreMaxEvent_of_action_score_max`, `UCB.measure_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.selectedEventOn_subset_finiteHorizonConfidenceBadEvent_of_action_score_max`, and `UCB.measure_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta`, the abstract action-trace bridge saying selected arms with a UCB score-maximality certificate are contained in the score-max event, and finite-time-set large-gap selected-arm events are covered by the same finite-horizon confidence bad event, so they inherit the textbook `delta` probability budget; no concrete UCB argmax/tie-breaking policy, empirical-mean construction, pull-count summation, or final regret theorem |
| compiled local UCB concrete score-argmax leaves | 1 | `UCB.scoreArgmax`, `UCB.scoreArgmax_spec`, `UCB.confidenceScoreArgmaxAction`, `UCB.confidenceScoreArgmaxAction_score_max`, `UCB.confidenceScoreArgmaxAction_score_max_of_selected`, `UCB.measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta`, and `UCB.measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta`, a concrete finite-arm Real score argmax over `Fin K` that supplies the selected-action score-max certificate and specializes the single-time/finite-time-set large-gap textbook `delta` wrappers; no empirical-mean construction from reward histories, recursive adaptive action trace, pull-count summation, or final regret theorem |
| compiled practical selected-policy random-width UCB consumers | 1 | `UCB.selectedPolicySuccessorEmpiricalMeanAt`, `UCB.selectedPolicySuccessorRadiusAt`, `UCB.selectedPolicySuccessorIndexAt`, `UCB.SelectedPolicySuccessorInitializedScoreMaxSource`, `UCB.SelectedPolicySuccessorInitializedScoreMaxSource.meanGap_le_two_radius_of_not_badEvent`, and `UCB.measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, preserving the sample-dependent realized-count width and converting the practical simultaneous confidence event into an initialized-time large-gap selection probability bound; concrete generated UCB source/initialization, pull-count expectation, and regret remain open |
| compiled local UCB count-budget leaves | 1 | `UCB.sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_selectedLargeGapCountOn_le_card_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_free_or_delta_sum`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeBudget_add_horizon_delta`, `UCB.freeTimes_indicator_sum_le_card`, `UCB.selectedSmallPullCount_sum_eq_min_pullCount`, `UCB.selectedSmallPullCount_sum_le_threshold`, `UCB.selectedSmallPullCount_indicator_sum_le_threshold`, `UCB.lintegral_selectedSmallPullCount_indicator_sum_le_threshold`, `UCB.selectedPullCount_sum_eq_pullCount`, `UCB.selectedPullCount_indicator_sum_eq_natCast_pullCount`, `UCB.selectedPullCount_indicator_sum_eq_selectedSmall_add_selectedLargePullCount`, `UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum`, `UCB.measurableSet_selectedLargePullCount`, `UCB.lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure`, `UCB.measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_subGaussian_textbookDeltaRadius_delta`, `UCB.sum_measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_selectedLargePullCount_indicator_sum_le_horizon_mul_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_threshold_add_horizon_delta_of_selectedLargePullCount`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusRecursiveSampleCount_add_horizon_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_historyAction_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_generatedActionTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.identityActionPolicy`, `UCB.confidenceScoreArgmaxGeneratedState`, `UCB.confidenceScoreArgmaxGeneratedTrace`, `UCB.lintegral_confidenceScoreArgmaxGeneratedTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeCard_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadiusChargedTimes`, `UCB.subGaussianTextbookDeltaRadiusFreeTimes`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusFreeCard_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_sq_lt`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusEightProxyLogThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusProxyThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count`, `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountThreshold_add_horizon_delta`, `UCB.subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound`, and `UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountLowerBound_add_horizon_delta`, a count-facing bridge from concrete finite-arm score-argmax large-gap selected-event probabilities to a finite-time selected-indicator lower-integral bound `|times| * delta`, a `Finset.range T` recursive `pullCount` budget `T * delta` under an all-horizon large-gap contract, a threshold/suffix-shaped split charging explicit free times by `1` while charging all other horizon times by `delta`, an abstract free-time budget consumer yielding `freeBudget + T * delta`, a cardinality wrapper yielding `freeTimes.card + T * delta`, a selected-small pathwise budget proving selected occurrences with prior `pullCount < B` sum to `min (pullCount T) B` and hence at most `B`, a probability-facing lower-integral selected-small budget with the same `B` bound, a selected-small/selected-large-count decomposition, a pointwise ENNReal budget `pullCount <= B + selectedLargeCount`, selected-large-count event measurability under explicit `OpensMeasurableSpace Nat`, selected-large-count finite-sum and lower-integral `T * delta` wrappers from a pointwise large-count-to-large-gap source, a recursive sample-count adapter from `proxy <= varianceProxy / pullCount` plus the real threshold certificate into the concrete `B + T * delta` wrapper, a source-count wrapper that accepts a history-derived `sampleCount` aligned with recursive `pullCount` on selected-large events, a history-action wrapper transferring the same budget to an externally generated trace agreeing with score argmax throughout the horizon, a generated-policy trace wrapper discharging score-argmax measurability from `Policy.generatedActionTrace` state measurability plus pointwise equality, an identity-policy concrete score-argmax generated-trace wrapper discharging the generated-trace equality contract definitionally, concrete textbook-radius large-gap/free-time Finsets instantiating that split, a threshold-cardinality consumer yielding `B + T * delta`, a standard half-gap threshold adapter, square/eight-proxy-log sufficient-condition consumers, a proxy-small threshold consumer under positive log scale, a sample-count threshold consumer from `proxy <= varianceProxy / count`, and a lower-bound-on-count consumer reducing this to a global threshold `B` plus `B <= count`; concrete proxy/count source from empirical rewards, empirical-mean construction, adaptive trace, and final regret theorem remain open |
| compiled local EXP3 potential leaves | 1 | `Exp3Potential.potential`, `Exp3Potential.updatedWeight`, `Exp3Potential.updatedPotential`, updated-potential unfolding, nonnegativity preservation, one-step potential-increment algebra, and finite-horizon telescoping; the downstream deterministic Hedge theorem now compiles |
| compiled local EXP3 deterministic Hedge regret leaves | 1 | `Exp3.cumulativeLoss`, normalized exponential weights, the global `exp(-x) <= 1-x+x^2` bound for `x >= 0`, the one-step log-potential bound, `Exp3.hedge_regret_le_log_card_div_add_eta_mul_mixedSquaredLoss_of_nonneg`, its bounded compatibility wrapper, and `Exp3.hedge_regret_le_log_card_div_add_eta_mul_horizon`; the pathwise second-order theorem now accepts arbitrary nonnegative estimated losses under `eta > 0` |
| compiled local EXP3 importance-weighted moment leaves | 1 | `Exp3.importanceWeightedLoss`, mixed estimate/square definitions, armwise finite-sum identity, pathwise selected-loss cancellation, probability-weighted mixed-loss equality, exact weighted mixed-square identity `sum_a loss(a)^2`, and the `[0,1]` bound by `arms.card`; requires nonzero sampling mass on support, with conditional and generated-process consumers compiled below |
| compiled local EXP3 conditional-moment transport leaves | 1 | `Exp3.FiniteActionDistribution`, finite Dirac action measure/integral wrappers, generic `condDistrib`-to-finite-sum Bochner transport, and specialized armwise/mixed first- and second-moment integral identities; consumes explicit policy/law and score regularity premises |
| compiled local EXP3 generated-action-process leaves | 1 | `Exp3.MeasurableFiniteActionDistribution`, `Exp3.finiteActionKernel`, finite/probability process-measure instances, canonical history-policy `compProd` measure, preserved history marginal, a.e. sampled-action `condDistrib` law, and three canonical moment consumers; its downstream score-regularity producer now discharges the explicit score premises |
| compiled local EXP3 score-regularity leaves | 1 | measurable supported `[0,1]` losses plus `0 < epsilon <= prob` yield armwise/mixed score measurability, pointwise bounds `1/epsilon`, `1/epsilon`, `(1/epsilon)^2`, generated-law integrability, and three canonical consumers without manual `hprob`/`hscore`/`hIntegrable`; generic and concrete sampled-score recursive trajectories compile downstream |
| compiled local EXP3 exploration-mixed recursive-trajectory leaves | 1 | any measurable cumulative score on inclusive finite action/loss histories generates positive exponential weights, normalized and uniformly explored probabilities with floor `gamma / arms.card`, a stochastic `HistoryAlgorithm`, a complete Mathlib-backed adaptive action/loss trajectory, and the exact successor-action `condDistrib`; the concrete sampled-score instantiation compiles downstream |
| compiled local EXP3 sampled-history-score recursive-trajectory leaves | 1 | `Exp3.sampledHistoryScore` recursively adds each observed chosen-action Real loss divided by the exact preceding exploration-mixed probability, proves score measurability and the concrete floor, constructs the stochastic algorithm and complete trajectory, and proves `Exp3.sampledImportanceWeightedTrajectoryMeasure_condDistrib_action` without external `score/hscore`; the predictable-adversary bridge now compiles downstream |
| compiled local EXP3 predictable-adversary leaves | 1 | jointly measurable pre-action initial/successor `[0,1]` loss vectors, deterministic chosen-coordinate Dirac feedback kernels, and the concrete sampled EXP3 action `condDistrib` given `(Env,prefix)` compile; the downstream observed-moment leaf now closes successor reward support and one-round moments |
| compiled local EXP3 predictable expected-regret route | 6 | global next-pair law and conditioning, finite-horizon observed moments, sampled-score/Hedge coupling, predictable-law a.e. control, exploration bias, adaptive pure-q transport, integrability, the unoptimized generated-trajectory theorem, deterministic `4 gamma T` simplification, the large-horizon `4 sqrt(|A| T log|A|)` corollary, realized selected-loss expectation transport, and the all-horizon clipped-rate `min(T, 4 sqrt(|A| T log|A|))` theorem all compile |
| compiled local FTRL one-step leaves | 1 | `FTRL.linearLoss`, `FTRL.finiteSimplex`, `FTRL.regularizedObjective`, `FTRL.IsRegularizedMinimizer`, and the generic/simplex one-step inequalities; consumes explicit minimizer and feasibility certificates under `0 < eta`, and is now consumed by the finite-horizon regularized be-the-leader theorem |
| compiled local Tsallis regularizer leaves | 1 | `Tsallis.powerSum`, `Tsallis.entropy`, `Tsallis.negEntropyRegularizer`, denominator nonzero from `alpha != 1`, nonnegative `Real.rpow` power sum on `FTRL.finiteSimplex`, and the finite-simplex well-definedness package; its exact power-sum penalty is now consumed by the finite-horizon decomposition |
| compiled local Tsallis-FTRL finite-horizon regret decomposition | 1 | `FTRL.cumulativeLoss`, cumulative linear-loss algebra, scaled regularized be-the-leader, generic and finite-simplex stability/penalty comparator-regret theorems, `Tsallis.negEntropyRegularizer_sub_eq_powerSum_sub_div`, and `Tsallis.cumulativeLinearLoss_sub_comparator_le_stability_add_powerSumPenalty`; explicit cumulative minimizers yield the exact stability sum plus `((powerSum p_0-powerSum q)/(1-alpha))/eta`, with no probability/measurability/convexity or hidden minimizer existence; the concrete Hessian/KKT stability estimate, update construction, conditional transport, self-bounding, and tuning remain open |
| compiled local Tsallis importance-weighted power-moment leaves | 1 | `Tsallis.powerWeightedSquaredImportanceWeightedLoss`, its pathwise selected-coordinate identity, the exact sampling-mass-weighted finite sum `sum_a loss(a)^2*p(a)^(1-alpha)`, and the `[0,1]` upper bound by `Tsallis.powerSum arms (1-alpha) p`; finite arms, decidable equality, and strictly positive supported weights are explicit; no probability normalization, conditional expectation, Hessian/KKT stability, minimizer existence, or regret is claimed |
| compiled local half-Tsallis minimizer/stationarity/interiority/horizon leaves | 4 | pairwise simplex shifts, exact half-objective and derivative formulas, minimizer-to-common-multiplier stationarity, the square-root supporting-line converse, boundary strict positivity, compact-standard-simplex minimizer existence, canonical noncomputable current/update/cumulative selectors, successor-update alignment, the direct sampling-law stability consumer with no caller minimizer or positivity proofs, and the no-caller-certificate deterministic finite-horizon decomposition; measurable history-dependent selection, conditional action-law/expectation transport, expected stability assembly, and final regret remain open |
| compiled local finite-history leaves | 1 | `History.FiniteActionHistory`, `History.FiniteRewardHistory`, `History.FiniteHistory`, `History.FinitePairHistory`, finite trace-restriction maps over `Finset.Iic`, pair-coordinate action/reward trace restriction, pair-history successor extension `History.extendPairHistorySucc`, coordinate evaluation measurability, reward projection from finite `(Action x Reward)` pair histories, measurable successor extension, and measurable finite-history restriction from timewise measurable action/reward traces; this is a product-measurability surface, not a filtration, kernel law, conditional expectation, or trajectory theorem |
| compiled local history-filtration leaves | 11 | `History.historyGenerators`, `History.historyGenerators_mono`, `History.historyMeasurableSpace`, `History.historyMeasurableSpace_mono`, `History.historyMeasurableSpace_le`, `History.historyFiltration`, `History.historyFiltration_apply`, `History.historyFiltrationSucc`, `History.historyFiltrationSucc_apply`, `History.measurableSet_action_mem_historyFiltration`, and `History.measurableSet_reward_mem_historyFiltration`, the action/reward past singleton-event history filtration canary plus the one-step shifted generated history filtration |
| compiled local history-filtration finite-pair comap bridge leaves | 1 | `History.measurable_finitePairHistoryOfTrace_mem_historyFiltration_of_lt`, `History.historyFiltration_succ_eq_comap_finitePairHistoryOfTrace`, and `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`, a countable/discrete bridge showing finite pair histories are measurable at later generated-history filtration levels, that `History.historyFiltration ... (n + 1)` is exactly the comap of `History.finitePairHistoryOfTrace ... n`, and that the shifted `History.historyFiltrationSucc ... n` has the same comap form; this aligns the generated filtration with Mathlib finite-prefix conditioning surfaces, but it is not a reward-law, `condExpKernel`, `partialTraj`, trajectory transport, or final theorem |
| compiled local adapted-coordinate leaves | 2 | `History.measurable_action_mem_historyFiltration_of_lt` and `History.measurable_reward_mem_historyFiltration_of_lt`, countable/discrete past-coordinate measurability canaries against `History.historyFiltration`; these are not full policy-predictability or conditional reward-law theorems |
| compiled local policy-measurability leaves | 2 | `Policy.MeasurablePolicy`, `Policy.measurable_action_of_measurable_state`, `Policy.measurable_action_mem_filtration_of_measurable_state`, `Policy.measurable_action_mem_historyFiltration_of_measurable_state`, `Policy.generatedActionTrace`, `Policy.measurable_generatedActionTrace_eval_of_measurable_state`, `Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state`, `Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state`, `Policy.generatedActionTraceSucc`, `Policy.generatedActionTraceSucc_succ_eq`, `Policy.measurable_generatedActionTraceSucc_eval_of_measurable_state`, and `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`, measurable policy/state composition plus policy-generated and shifted policy-generated action trace coordinate-measurability surfaces; these are not kernel-law or trajectory-law theorems |
| compiled local reward-kernel leaves | 8 | `RewardKernel.MarkovRewardKernel`, `RewardKernel.ofKernel`, selected-measure probability and event-probability measurability wrappers, constant/deterministic reward-kernel constructors, context/action plus policy/state reward-kernel lookup wrappers, one-step `RewardKernel.composePolicy` composition, deterministic `RewardKernel.policyActionKernel`, one-step `RewardKernel.composePolicyActionReward` product kernels, selected-reward marginal wrappers for one-step and history-step action/reward kernels, measure-level `Prod.snd` pushforward reward-marginal equalities and `Prod.fst` deterministic action-Dirac equalities for those action/reward kernels, `RewardKernel.CenteredRewardKernelLaw`, centered-reward law transfer through policy-composed and finite reward-history step kernels, `RewardKernel.partialTrajectoryKernel` finite-prefix reward-history assembly, `RewardKernel.actionRewardPartialTrajectoryKernel` finite-prefix action/reward pair trajectory assembly via Mathlib `partialTraj`, one-step `partialTraj` next-coordinate marginal wrappers `RewardKernel.partialTrajectoryKernel_succ_next_map*` / `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map*`, full one-step/history-step fixed-action pushforward wrappers `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk` / `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`, `ConditionalExpectationReward.pair_map_eq_map_prod_mk_of_action_ae_eq_const_reward_map_eq`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure_of_selectedAction_ae_selectedMeasure`, and the full-prefix frozen-extension wrapper `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`; this is not a `condExpKernel` identification, posterior kernel, infinite trajectory law, or final adaptive-regret construction |
| compiled local posterior-kernel leaves | 2 | `PosteriorKernel.MarkovPosteriorKernel`, selector constructors and measurability wrappers, plus `PosteriorKernel.canonicalPosterior`, `PosteriorKernel.canonicalJointMeasure`, `PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq`, and its canonical-product specialization. The second leaf uses Mathlib `posterior`, `compProd_posterior_eq_map_swap`, `Measure.snd_compProd`, and `condDistrib` uniqueness to produce the environment-given-history posterior law from an exact pair pushforward; arbitrary `BayesianPosteriorSurface` values still have no Bayes-law field, and actual algorithm-history pair-law construction remains separate |
| compiled local Thompson posterior-action identity leaves | 1 | `Thompson.PosteriorActionIdentityLedger`, `Thompson.PosteriorActionIdentityLedger.actionKernel_apply_eq_posteriorBest_map`, and `Thompson.PosteriorActionIdentityLedger.actionKernel_apply_singleton_eq_posteriorBest_preimage`, a source contract and event/singleton consumers for the probability-matching identity between a Thompson action kernel and the posterior pushforward by a measurable best-action map; this consumes the identity and is not Bayes-rule identification, posterior sampler construction, LML import, or Bayesian regret |
| compiled local Thompson posterior best-action measurability leaves | 1 | `Thompson.bestAction_measurable_of_countable_env` and `Thompson.PosteriorActionIdentityLedger.ofCountableEnv`, a Mathlib `measurable_of_countable` wrapper and ledger constructor that discharge best-action measurability for finite/countable environment spaces; this still assumes the event-level posterior action law and is not Bayes-rule identification, posterior sampler construction, LML import, noncountable argmax measurability, or Bayesian regret |
| compiled local Thompson posterior-action conditional-law leaves | 1 | `Thompson.PosteriorActionIdentityLedger.ofPosteriorMap`, `Thompson.PosteriorActionIdentityLedger.actionKernel_eq_posterior_map`, `Thompson.BayesianPosteriorActionSource`, and `Thompson.condDistrib_action_ae_eq_bestAction_of_posteriorMap`, a Mathlib `condDistrib` transport from an action law equal to `posterior.map bestAction` plus a posterior/environment conditional-law identity to the conditional law of the random best action; this is the local counterpart of pinned LML `Bandits.TS.hasCondDistrib_action`, but it still consumes the concrete Bayesian posterior identity and is not a Bayes-density proof, literal LML import, regret decomposition, concentration argument, or Bayesian regret theorem |
| compiled local Thompson canonical posterior pair-law leaves | 1 | `Thompson.condDistrib_action_ae_eq_bestAction_of_bayesianPairMap` and `Thompson.condDistrib_action_ae_eq_bestAction_of_canonicalPriorLikelihood` consume the compiled canonical posterior producer, so the posterior/environment conditional-law identity is no longer assumed. The arbitrary-source theorem requires the exact environment/history pair pushforward and the Thompson next-action conditional law; the canonical product theorem discharges the pair law. The canonical one-step sampler discharges both laws in the next leaf; recursive TS trajectory transport, regret decomposition, concentration, and final Bayesian regret remain open |
| compiled local Thompson canonical sampler probability-matching leaves | 1 | `Thompson.canonicalActionKernel`, `Thompson.canonicalSamplerMeasure`, `Thompson.map_compProd_comap_snd`, both canonical sampler marginal identities, `Thompson.canonicalSampler_condDistrib_action_ae_eq_actionKernel`, and `Thompson.canonicalSampler_condDistrib_action_ae_eq_bestAction` construct the canonical one-step TS joint law and prove probability matching without pair-law or action-law premises. The route uses the canonical posterior, `Kernel.map`/`comap`, `Measure.fst_compProd`, finite-measure product extensionality, and `condDistrib` uniqueness; it is not yet a recursive TS process, algorithm-density transport, regret decomposition, concentration proof, or Bayesian regret theorem |
| compiled local Thompson reference-posterior policy sampler leaves | 1 | `Thompson.referencePosterior`, `Thompson.referenceActionKernel`, `Thompson.policySamplerMeasure`, `Thompson.map_compProd_comap_history`, the sampler marginal/conditional-law/posterior-preservation lemmas, and `Thompson.finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance` implement LML's fixed-reference-posterior policy boundary. The actual action law is constructed by `compProd`, including the finite action/reward-prefix specialization; the only remaining law premise is reference-versus-actual posterior invariance. This is not the algorithm-density proof, a recursively coupled TS trace, regret decomposition, concentration, literal LML import, or final Bayesian regret |
| compiled local Thompson algorithm-density posterior-invariance leaves | 1 | `Thompson.compProd_withDensity_left`, `Thompson.AlgorithmDensityPosteriorSource`, `Thompson.referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource`, and the generic/finite-pair `...of_algorithmDensitySource` probability-matching endpoints compile the measure-theoretic core of LML's change-of-algorithm route. One measurable history density must explain both the actual history marginal and actual history/environment joint pushforward; commuting that density through the reference posterior `compProd` and applying `condDistrib` uniqueness produces posterior invariance, which is consumed directly by the constructed action sampler. This does not construct the two density laws from a concrete recursive TS process, couple one global trace, port LML structures literally, decompose regret, prove concentration, or close Bayesian regret |
| compiled local canonical trajectory conditional-law leaves | 5 | `RewardKernel.actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure`, the Mathlib `trajMeasure`/`condDistrib` specialization proving the next action/reward pair conditioned on the finite prefix is a.e. the configured history-step kernel on the canonical Ionescu-Tulcea trajectory measure; `RewardKernel.actionRewardHistoryStepKernelFamily_action_condDistrib_trajMeasure`, the `Prod.fst` action-marginal projection via Mathlib `condDistrib_comp`; `RewardKernel.actionRewardHistoryStepKernelFamily_selectedAction_condDistrib_trajMeasure`, the policy-selected action Dirac form via `RewardKernel.actionRewardHistoryStepKernelFamily_action_map`; `RewardKernel.actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure`, the `Prod.snd` reward-marginal projection via Mathlib `condDistrib_comp`; and `RewardKernel.actionRewardHistoryStepKernelFamily_selectedMeasure_condDistrib_trajMeasure`, the selected context/action reward-law form via `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`; these narrow the `COND-EXPECT-REWARD` law-identification route but do not transport an arbitrary ambient `Omega`/`condExpKernel` or `History.historyFiltrationSucc` |
| compiled local Thompson measurable trajectory, global sampler, regret-decomposition, clipped-score, stationary arm-stream, and deterministic support leaves | 6 | `ThompsonMeasurableTrajectory` builds genuine `Env -> PairTrace` kernels and proves projected successor laws and pointwise canonical equality. `ThompsonRecursiveSampler` defines the non-circular uniform-reference Thompson `HistoryAlgorithm`, discharges finite-action absolute continuity, and proves actual-trajectory probability matching. `ThompsonBayesRegretDecomposition` proves score-expectation matching and the LML-shaped finite-horizon decomposition. `ThompsonClippedUCBScore` implements the pinned score and discharges score/mean integrability. `ThompsonStationaryReward` represents stationary reward kernels by independent latent arm streams, proves all-time deterministic trajectory support, and transports arbitrary-action adaptive-count upper/lower tails to a fixed-environment actual augmented trajectory kernel. No supplied posterior/sampler/AC/support premise remains; augmented-prior mixing, measurable clipped-confidence events, the two concentration terms, and final Bayesian regret remain open |
| compiled local conditional-expectation kernel bridge leaves | 208 | `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero`, `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq`, `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen`, `ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet`, `ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq`, `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc`, `Policy.generatedActionTraceSucc`, `Policy.generatedActionTraceSucc_succ_eq`, `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`, `ConditionalExpectationReward.condExpKernel_pair_map_eq_map_prod_mk_of_action_ae_reward_map_eq`, `ConditionalExpectationReward.random_pair_condExpKernel_map_eq_actual_action_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource_rawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionActualRewardMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionDefinitionalActualRewardMapSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource`, `ConditionalExpectationReward.generatedActionFromRewardHistory`, `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`, `ConditionalExpectationReward.GeneratedActionPartialTrajectoryPairLawSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_partialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_action_ae_eq_policy_reward_map_eq`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource`, `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward`, `ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound`, `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_actual_action`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_historyVarianceSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_varianceCeiling_le`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable`, `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable`, `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen`, `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc`, `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, and `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq`, and `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`, `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk`, `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`, `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`, and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`, narrow wrappers converting trim-a.e. zero conditional-kernel integrals into ordinary conditional mean-zero facts, an explicit law/integral-equality consumer, a reward-coordinate pushforward-map consumer with a frozen-past condition via Mathlib `integral_map`, a deterministic frozen-history-to-centered-target a.e. bridge, a conditional-kernel frozen-past route for conditioning-measurable events/countable variables/finite reward histories, a concrete finite-history measurability hookup for coordinate-measurable reward prefixes plus generated `History.historyFiltrationSucc`, a finite action/reward pair-history frozen-past hookup under `[Countable Action]`, a successor-extension bridge decomposing the `i+1` pair trace into a frozen old prefix plus random next pair under generated `condExpKernel`, a `Measure.map_congr` pushforward form of that successor decomposition, map-law consumer specializations that discharge the frozen-past side condition from those hooks, an action/reward pair-law marginalization consumer via `Prod.snd`, a generated-history specialization that supplies next-coordinate and reward-prefix measurability from `History.historyFiltrationSucc`, a concrete finite trace pair-history/reward-projection specialization, a projection-measurability hookup that derives projected pairContext/pairState measurability from reward-history context/state measurability, a named `History.finitePairHistoryOfTrace` specialization aligned with the pair-coordinate `partialTraj` surface, a partialTraj finite-pair-trace consumer plus reusable projection adapter that reduces an explicit extended finite pair-trace `condExpKernel` law through the `partialTraj` next-coordinate marginal into the pair-map route, a direct history-step next-pair reward-map adapter that projects an explicit next-pair law through `Prod.snd` into the actual-action reward-coordinate law, a full finite-pair-trace reward-map adapter that projects the same law through `Prod.snd` into the actual-action reward-coordinate law, an extension-map partialTraj consumer with a reusable extension-to-full-trace law adapter that narrows the remaining law assumption to the frozen-prefix extension map while still exposing the whole-trace law, an extension-map reward-map adapter that lifts that narrower law back to the full trace law and projects it to the actual-action reward-coordinate law, a pairmap-to-extension law builder that derives that extension-map law from an explicit next-pair condExpKernel law plus the RewardKernel full-extension wrapper, a split-law builder that derives the next-pair law from a conditional action a.e. equality plus a reward-coordinate selected-measure law, a random-pair history-step law adapter that canonicalizes a generated-action random next-pair source law into the RewardKernel.actionRewardHistoryStepKernelFamily shape, an action-freezing hookup that turns countable `F i`-measurable next actions plus trim-a.e. policy equality into that conditional action a.e. equality, a generated-history action-side hookup that derives the action side from visible finite pair histories, measurable pairState, and pointwise policy-generation equality, and a shifted generated-trace source that supplies that pointwise equality from `Policy.generatedActionTraceSucc`, plus a generated-action actual/random-pair reward-law hookup that marginalizes an actual-action pair-product law to the actual-action reward-coordinate map law, or first freezes a fully random next-pair law with `Measure.map_congr`, then rewrites it to the policy-selected action, feeds the split-law builder, pushes the result through the extension-map `partialTraj` route, exposes reusable full finite-pair-trace partialTraj law adapters for reward-coordinate, actual-action pair-product, and fully random next-pair law shapes, and consumes them for succ-indexed conditional mean-zero under integrability; the generated actual reward-coordinate source contract packages only the actual next-action reward map law as a reusable source, that actual reward-coordinate source now also exposes a source-level canonical history-step pair-law consumer by lifting reward-history context/state through History.pairHistoryRewardProjection, the generated definitional actual reward-coordinate source removes explicit action-trace and `haction` inputs from that source by reusing `generatedActionFromRewardHistory`, that definitional actual reward-coordinate source now also exposes a source-level canonical history-step pair-law consumer over generatedActionFromRewardHistory, a standalone full finite-pair-trace `partialTraj` consumer over generatedActionFromRewardHistory, and an independently indexed integrability-based source-level conditional mean-zero consumer, the generated partialTraj pair-law source contract packages the exact full finite-pair source field, feeds it into the definitional generated random-pair source, and now also projects it into the selected-reward finite-pair-history source, the same source can now be constructed from split generated-history next-pair laws through the action a.e. plus selected-reward map builder, and for generatedActionFromRewardHistory the action side is discharged automatically so the selected reward-coordinate law alone constructs that source, the existing definitional random-pair source now also converts into that partialTraj source by projection, the practical definitional raw-range source now projects its packaged definitional map source and context measurability into the same partialTraj source surface, and the same source plus raw/mean range regularity and either a global variance ceiling, a coarser uniform proxy, selected-history variance ceilings, or a coarser selected-history proxy now directly yields exact- or coarser-proxy succ-indexed conditional MGF witnesses, the generated random-pair source contract packages this remaining law assumption as a reusable source with full-trace consumers, an independently indexed integrability-based conditional mean-zero consumer, and an independently indexed raw-range conditional mean-zero consumer, the generated random-pair source now also exposes a source-level canonical history-step pair-law consumer by lifting reward-history context/state through `History.pairHistoryRewardProjection`, the random-pair source can now be weakened into the actual reward-map source by action freezing and `Prod.snd` marginalization, the centered random-pair source now exposes its packaged random-pair map source directly and can also be projected into that weaker actual reward-map source through its packaged map source and state measurability, the bounded-centered random-pair source now exposes its packaged random-pair map source directly and has the same projection into the actual reward-map source while keeping a.e. measurability and interval-bound evidence for integrability consumers, the definitional generated-action map source defines the action trace as the shifted policy-generated trace over finite reward histories, derives timewise action measurability from measurable state extractors plus reward traces, and can now be constructed from a policy-selected reward-coordinate selected-measure law through the frozen-prefix extension-map route, and that bare source route now directly consumes raw/mean range regularity into succ-indexed conditional mean-zero and, with a global variance ceiling or selected-history variance ceilings, into exact- or coarser-proxy succ-indexed conditional MGF witnesses; the definitional generated-action map source now also exposes a canonical history-step pair-law consumer without explicit action or `haction` parameters, and the generated centered-source contract additionally packages context/state measurability, the centered reward-kernel law, and per-step ambient integrability so the mean-zero consumer no longer needs a separate `h_integrable`; the centered random-pair source now also exposes a canonical history-step pair-law consumer while preserving centered law and integrability fields; the definitional centered-source contract removes explicit action-trace and `haction` inputs from that centered layer using `generatedActionFromRewardHistory` plus the definitional map source; the definitional centered source now also exposes the canonical history-step pair-law consumer over `generatedActionFromRewardHistory`; that definitional centered source now also exposes its packaged ambient integrability as a named theorem and projects into the explicit generated random-pair map source through its packaged definitional map source, into the weaker definitional actual reward-map source through the same package, and into the explicit generated actual reward-map source through the definitional actual-map projection; the generated bounded-centered source contract derives centered-source integrability from per-step a.e. measurability plus a.e. interval bounds through Mathlib `Integrable.of_mem_Icc`, and the bounded-centered source now also exposes the canonical history-step pair law through the centered-source route; the generated raw/mean bounded source contract derives centered a.e. measurability and centered interval bounds from separate raw reward and selected mean evidence, exposes the same canonical history-step pair law through the bounded-centered route, exposes its packaged random-pair map source directly, exposes the same projection into the weaker actual reward-map source, then reuses the bounded-centered route; the generated raw-bound/mean-bounded source contract derives raw reward Rat-to-Real a.e. measurability from existing timewise reward trace measurability, exposes the canonical history-step pair law through the raw/mean bounded route, exposes its packaged random-pair map source directly, exposes the same projection into the weaker actual reward-map source, then reuses the raw/mean bounded route; the generated raw-bound/measurable-mean source contract derives selected mean Rat-to-Real a.e. measurability from a measurable mean surface composed with finite reward histories, context/state extractors, and the measurable policy action, now has an independently indexed source-level conditional mean-zero consumer, exposes its packaged random-pair map source directly, exposes the canonical history-step pair law through the raw-bound/mean-bounded route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/mean-bounded route; the generated raw-bound/measurable-mean-range source contract derives selected mean a.e. interval bounds from deterministic pointwise mean range bounds, now has an independently indexed source-level conditional mean-zero consumer, exposes its packaged random-pair map source directly, exposes the canonical history-step pair law through the raw-bound/measurable-mean route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/measurable-mean route; the generated raw-range/measurable-mean-range source contract derives raw reward a.e. interval bounds from deterministic pointwise reward range bounds, now has an independently indexed source-level conditional mean-zero consumer, exposes the canonical history-step pair law through the raw-bound/measurable-mean-range route, exposes the same projection into the weaker actual reward-map source, then reuses the raw-bound/measurable-mean-range route; the generated definitional raw-range/measurable-mean-range source removes explicit action-trace and `haction` inputs from the practical top layer by reusing `generatedActionFromRewardHistory` plus the definitional map source, the actual-action and policy-selected reward-coordinate raw-range routes now directly consume those laws into succ-indexed conditional mean-zero, and the definitional actual reward-map source now directly consumes raw/mean range regularity into succ-indexed conditional mean-zero, exposes the canonical history-step pair law over `generatedActionFromRewardHistory`, exposes a direct projection into the explicit generated random-pair map source, exposes centered successor reward a.e. measurability and centered interval bounds directly, packages those fields into the bounded centered source over `generatedActionFromRewardHistory`, lowers that package into the integrability-based centered source, packages the same evidence into the definitional centered source, exposes the same projection into the weaker definitional actual reward-map source, also exposes the explicit generated-action actual reward-map projection through the definitional actual-map source, constructs the base definitional raw-range/measurable-mean-range source from actual-action and policy-selected reward-coordinate selected-measure laws without adding variance assumptions, and now consumes the actual-action and policy-selected reward-coordinate selected-measure laws plus selected-history variance ceilings into conditional MGF witnesses, consumes the actual-action or policy-selected reward-coordinate selected-measure law, the full finite-pair partialTraj law, the frozen-prefix extension-map partialTraj law, and the canonical history-step next-pair law, plus a selected-history variance ceiling at any coarser deterministic proxy c satisfying varianceCeiling i <= c, consumes the actual-action or policy-selected reward-coordinate selected-measure law, the full finite-pair partialTraj law, the frozen-prefix extension-map partialTraj law, and the canonical history-step next-pair law plus a uniform variance ceiling at any coarser deterministic proxy c satisfying varianceCeiling <= c, constructs the packaged uniform-variance source from the actual-action or policy-selected reward-coordinate selected-measure law, constructs the packaged history-variance source from the actual-action or policy-selected reward-coordinate selected-measure law, projects a packaged uniform-variance source to its base raw-range/measurable-mean-range bounded source, lowers it to the explicit generated random-pair map source, lowers it to the generated full finite-pair partialTraj source, consumes it into the canonical history-step pair law, lowers it to the weaker definitional actual reward-map source, lowers it to the explicit generated actual reward-map source, and lowers it to the bounded centered-source, integrability-based centered-source, and definitional centered-source interfaces, projects a packaged selected-history-variance source to the same base interface, lowers it to the explicit generated random-pair map source, lowers it to the generated full finite-pair partialTraj source, consumes it into the canonical history-step pair law, lowers it to the weaker definitional actual reward-map source, lowers it to the explicit generated actual reward-map source, and lowers it to the bounded centered-source, integrability-based centered-source, and definitional centered-source interfaces, consumes a packaged uniform-variance source through the selected-history variance-source conditional MGF interface with constant ceiling, consumes a packaged uniform-variance source through any coarser deterministic proxy c satisfying varianceCeiling <= c, and consumes a packaged selected-history variance source through any coarser deterministic proxy c satisfying varianceCeiling i <= c; this does not construct the pair/reward-law source, the ambient trajectory-to-`condExpKernel` identification, or final adaptive theorem |
| compiled local selected-reward finite-pair comap source/theorem wrappers | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_reward_map_eq_selected_policy`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_trim_reward_map_eq_selected_policy`, `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_trim_reward_map_eq_selected_policy`, wrappers turning a selected-reward `condExpKernel.map` law conditioned on the finite pair-prefix comap sigma-algebra into both `GeneratedActionSelectedRewardFinitePairHistoryLawSource`, the full `GeneratedActionPartialTrajectoryPairLawSource`, and the theorem-card-shaped full finite-pair `partialTraj`/`condExpKernel` law via `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`; this now accepts either the generated-history trim filter or the comap-trim filter at the selected-source, partialTraj-source, and theorem-wrapper layers and still consumes, rather than proves, the selected-reward law or ambient trajectory transport |
| compiled local partialTraj/comap raw-range source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package measurable mean, centered reward-kernel law, and raw/mean range regularity from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local partialTraj source mean-zero consumers | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeBounded`, a source-level consumer that takes `GeneratedActionPartialTrajectoryPairLawSource` plus raw/mean range regularity and returns ordinary succ-indexed conditional mean-zero for the centered generated reward; this still consumes, rather than proves, the full finite-pair `partialTraj`/`condExpKernel` law and does not add variance/MGF evidence |
| compiled local partialTraj/comap uniform-variance source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package raw/mean range regularity and a global variance ceiling from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and variance ceiling and does not prove ambient trajectory transport |
| compiled local partialTraj/comap history-variance source constructors | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_partialTrajectoryPairLawSource`, `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy`, source constructors that package raw/mean range regularity and selected-history variance ceilings from either an explicit generated full finite-pair `partialTraj` source or the finite-pair comap selected-reward law that constructs that source; the selected-reward law can now be supplied at either the generated-history trim surface or the direct comap-trim surface, and this still assumes the selected-reward law and selected-history ceiling contract and does not prove ambient trajectory transport |
| compiled local condDistrib-to-condExpKernel bridge leaves | 1 | `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable`, a Mathlib-backed countable-target bridge turning an a.e. `condDistrib X Y mu = kernel` law into an a.e. `condExpKernel mu (comap Y)` pushforward law by `X`; this narrows the canonical trajectory-law-to-consumer route but still consumes, rather than constructs, the trajectory law |
| compiled local canonical trajMeasure pair condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure`, a specialization showing that on the canonical Mathlib `trajMeasure`, `condExpKernel` conditioned on the finite pair prefix and pushed forward by the next `(Action, Reward)` coordinate is a.e. `RewardKernel.actionRewardHistoryStepKernelFamily` at that prefix; this gives the downstream next-pair consumers a canonical source but still does not transport an arbitrary generated process |
| compiled local canonical trajMeasure split-route pair condExpKernel-map leaves | 1 | `ConditionalExpectationReward.pair_map_eq_map_prod_mk_of_action_ae_eq_const_reward_map_eq` and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure_of_selectedAction_ae_selectedMeasure`, a split-route reconstruction of the canonical next-pair law from selected-action conditional a.e. equality and selected-reward map law under separate `Countable Action` and `Countable Reward`; this validates the split route on canonical `trajMeasure`, not ambient transport |
| compiled local ambient split-product condExpKernel leaves | 1 | `ConditionalExpectationReward.condExpKernel_pair_map_eq_map_prod_mk_of_action_ae_reward_map_eq` and `ConditionalExpectationReward.random_pair_condExpKernel_map_eq_actual_action_of_generatedActionTraceSucc_reward_map_eq_actual_action`, an ambient split-product adapter that turns conditional action a.e. equality plus a reward-coordinate selected-measure law into the fully random next-pair product pushforward, with a generated `History.historyFiltrationSucc` specialization from `Policy.generatedActionTraceSucc`; this still assumes the reward-coordinate law and does not identify the ambient trajectory law |
| compiled local actual-to-random source-conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionActualRewardMapSource`, a source wrapper upgrading `GeneratedActionActualRewardMapSource` plus state measurability into `GeneratedActionRandomPairMapSource` through the ambient split-product condExpKernel law; this still assumes the actual-action reward-coordinate law and ambient trajectory-to-`condExpKernel` identification |
| compiled local definitional actual-to-generated-random source-conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionDefinitionalActualRewardMapSource`, a source wrapper upgrading `GeneratedActionDefinitionalActualRewardMapSource` into the explicit generated-action `GeneratedActionRandomPairMapSource` over `generatedActionFromRewardHistory` by lowering through the actual-to-random source conversion; this still assumes the definitional actual-action reward-coordinate law and ambient trajectory-to-`condExpKernel` identification |
| compiled local explicit centered map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairCenteredSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit centered generated random-pair source; this still assumes the packaged random next-pair law and centered-source regularity fields |
| compiled local explicit bounded-centered map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit bounded centered generated random-pair source; this still assumes the packaged random next-pair law and bounded-centered source regularity fields |
| compiled local explicit raw/mean map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward/selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/mean-bounded map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/measurable-mean map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/measurable-selected-mean bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-bound/measurable-mean-range map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-bound/measurable-mean-range bounded source; this still assumes the packaged random next-pair law and source regularity fields |
| compiled local explicit raw-range map-source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`, a projection wrapper exposing the packaged `GeneratedActionRandomPairMapSource` from the explicit raw-reward-range/measurable-mean-range bounded source; this still assumes the packaged random next-pair law and top-layer regularity fields |
| compiled local uniform variance to raw-range bounded source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`, a projection wrapper exposing the packaged practical raw-range/measurable-mean-range bounded base source from the uniform-variance source; this still assumes the packaged random next-pair law, raw/mean range regularity, and global variance ceiling |
| compiled local uniform variance to random-pair map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated random-pair map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to partialTraj source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into `GeneratedActionPartialTrajectoryPairLawSource`; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to history-step pair-law consumer leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`, a source-consumer wrapper lowering the packaged uniform-variance source through its generated random-pair map source into the canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to definitional actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to definitional centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the definitional centered-source interface; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local history variance to raw-range bounded source projection leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`, a projection wrapper exposing the packaged practical raw-range/measurable-mean-range bounded base source from the selected-history-variance source; this still assumes the packaged random next-pair law, raw/mean range regularity, and selected-history variance ceilings |
| compiled local history variance to random-pair map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated random-pair map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to partialTraj source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into `GeneratedActionPartialTrajectoryPairLawSource`; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to history-step pair-law consumer leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`, a source-consumer wrapper lowering the packaged selected-history-variance source through its generated random-pair map source into the canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to definitional actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to actual reward-map source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local uniform variance to bounded centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its base bounded source into the bounded centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local uniform variance to centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`, a conversion wrapper lowering the packaged uniform-variance raw-range/measurable-mean-range source through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, and final reward-law identification |
| compiled local history variance to bounded centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the bounded centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local history variance to definitional centered source conversion leaves | 1 | `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`, a conversion wrapper lowering the packaged selected-history-variance raw-range/measurable-mean-range source through its base bounded source into the definitional centered-source interface; this still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, and final reward-law identification |
| compiled local canonical trajMeasure action condExpKernel-map leaves | 3 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_condExpKernel_map_trajMeasure`, the `Prod.fst` projection of the canonical next-pair `condExpKernel` law requiring the countable pair target; `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_actionMarginal_condExpKernel_map_trajMeasure`, the direct countable-`Action` route giving the `Prod.fst` marginal of the history-step kernel; and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_map_trajMeasure`, the selected-action Dirac form built from that marginal law and `RewardKernel.actionRewardHistoryStepKernelFamily_action_map`; these are canonical `trajMeasure` laws, not ambient `Omega`/`History.historyFiltrationSucc` transport theorems |
| compiled local canonical trajMeasure selected-action condExpKernel-a.e. leaves | 1 | `ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac` and `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_ae_trajMeasure`, a Dirac-pushforward-to-a.e.-constant helper plus the canonical selected-action law in the `Filter.EventuallyEq` shape consumed by the next-pair split-law builder; this is still a canonical `trajMeasure` theorem, not ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure extension condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_condExpKernel_map_trajMeasure`, the extension-map form of the canonical next-pair law: pushing the canonical `condExpKernel` next-pair law through `History.extendPairHistorySucc` yields the one-step `RewardKernel.actionRewardPartialTrajectoryKernel` surface; this aligns with extension-map consumers but still does not prove ambient `History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure full-prefix condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_prefix_condExpKernel_map_trajMeasure`, the full finite-prefix form of the canonical `trajMeasure` law: the extension-map law plus `condExpKernel` frozen-prefix evidence rewrites the pushforward to `Preorder.frestrictLe (n + 1)` and recovers the one-step `RewardKernel.actionRewardPartialTrajectoryKernel`; this gives a stronger canonical full-prefix source but still does not prove ambient `History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure finite-pair-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure`, a notation-alignment wrapper restating the canonical full-prefix law with `History.finitePairHistoryOfTrace` for the old and successor pair prefixes; this matches the project theorem-card shape but still does not prove ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure condExpKernel reward-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_reward_condExpKernel_map_trajMeasure`, a specialization showing that on the canonical Mathlib `trajMeasure`, `condExpKernel` conditioned on the finite pair prefix and pushed forward by the next reward coordinate is a.e. the reward marginal of `RewardKernel.actionRewardHistoryStepKernelFamily`; this is not an ambient `Omega`/`History.historyFiltrationSucc` transport theorem |
| compiled local canonical trajMeasure selected-reward condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure`, the selected context/action reward-measure form of the canonical `trajMeasure` `condExpKernel` next-reward law; this gives downstream selected-policy consumers a direct canonical source but still does not transport an arbitrary generated process |
| compiled local reward-only canonical trajMeasure selected-reward condExpKernel-map leaves | 1 | `RewardKernel.instIsMarkovKernel_historyStepKernelFamily` exposes the already-proved reward-history step-family Markov property to Mathlib, and `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure` applies `Kernel.condDistrib_trajMeasure` plus the local countable-target bridge to prove the selected-reward conditional pushforward law at the finite reward prefix; generated finite-pair alignment, trim-selected-source construction, ambient `IdentDistrib` transport, and recursive `condDistrib` source construction are compiled downstream |
| compiled local reward-only generated finite-pair conditioning leaves | 1 | `ConditionalExpectationReward.comap_finitePairHistoryOfTrace_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace` proves equality of the generated finite-pair and reward-prefix comaps, `ConditionalExpectationReward.historyFiltrationSucc_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace` rewrites the shifted filtration, and `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace` exposes the ordinary canonical selected-reward law on the generated finite-pair surface; the sound trim companion is compiled in the downstream canonical selected-source leaf |
| compiled local reward-only trim-selected-source leaves | 1 | `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim` lifts the countable-target bridge to the conditioning trim through measurable singleton probabilities, `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_trim` specializes it to reward-only `trajMeasure`, `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace_trim` transports it to generated finite-pair conditioning, and `ConditionalExpectationReward.historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_trajMeasure` constructs the selected source without a selected-reward source assumption; canonical, ambient `IdentDistrib`, and recursive-`condDistrib` full `partialTraj` routes are compiled downstream |
| compiled local ambient IdentDistrib selected-reward transport leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_of_identDistrib_trajMeasure_trim` transports the canonical finite-prefix/next-reward joint `compProd` factorization through complete reward-trace `IdentDistrib`, uses disintegration uniqueness to identify the ambient conditional law, and derives the trim selected-reward `condExpKernel.map` equality; `ConditionalExpectationReward.historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_identDistrib_trajMeasure` rewrites generated pair-prefix conditioning and constructs the ambient selected source, which the existing converter sends to the full generated `partialTraj` source. The adjacent recursive leaf now constructs the required complete-trace law from initial and successor conditional laws; ambient mean-zero/MGF/tail wrappers remain separate |
| compiled local ambient recursive-condDistrib partialTraj-source leaves | 1 | `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`, promoted to foundation module `BanditRLProof.RewardTraceLaw`, derives the complete reward-trace law from the initial marginal and every successor `condDistrib` given its finite prefix. `ConditionalExpectationReward.historyStepKernelFamily_identDistrib_trajMeasure_of_condDistrib` specializes this to the policy/reward history-step family; `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_condDistrib` and `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_of_condDistrib` then construct the ambient selected and full generated `partialTraj` sources. The caller still must prove the recursive conditional laws; direct ambient MGF and finite-sum tail consumers are compiled in the adjacent concentration leaf |
| compiled local ambient recursive-condDistrib centered finite-sum tail leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource` consumes any generated full `partialTraj` source, measurable mean, `CenteredRewardKernelLaw`, and selected-history variance domination into `HasCondSubgaussianMGF`, deriving exponential integrability without raw/mean range bounds. `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_of_condDistrib` supplies that source from recursive laws, and `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_condDistrib` derives ambient probability from the initial pushforward, proves strong adaptedness, and obtains the ENNReal Azuma-Hoeffding bound for centered rewards `1..n-1`. Arm/sample-count confidence specialization and concrete production of recursive laws remain open |
| compiled local reward-only canonical generated partialTraj law leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure` converts the canonical trim-aware selected source into `GeneratedActionPartialTrajectoryPairLawSource`, and `ConditionalExpectationReward.historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_trajMeasure` proves the theorem-shaped successor finite pair-prefix `condExpKernel.map` equality to `RewardKernel.actionRewardPartialTrajectoryKernel`; no ambient selected-reward, random-pair, or partialTraj source hypothesis remains, but the arbitrary-ambient theorem card, regularity packages, and final adaptive theorem remain open |
| compiled local reward-only canonical centered mean-zero leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure` combines the canonical full generated partialTraj law with `RewardKernel.CenteredRewardKernelLaw` and explicit ambient centered-reward integrability to prove successor conditional expectation zero under generated finite-pair history; it deliberately avoids pointwise raw bounds on every `Nat -> Rat` trace, and its conditional-MGF consumer is compiled downstream while ambient integrability production and arbitrary ambient transport remain open |
| compiled local condExpKernel conditional-MGF integrated-transfer leaves | 1 | `ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq` now derives global exponential integrability from trim-a.e. target `HasSubgaussianMGF` laws: `Measure.integrable_comp_iff` combines target-wise integrability with the common MGF bound, `StronglyMeasurable.integral_kernel` supplies inner-integral measurability, and `Integrable.of_bound` uses finiteness of the trim measure; the strengthening propagates through history-step and generated-history consumers but still assumes centered measurability, the conditional pushforward law, and deterministic variance domination |
| compiled local reward-only canonical centered conditional-MGF leaves | 1 | `ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure` combines the canonical full generated partialTraj law, measurable mean, a deterministic finite-history variance ceiling, and the integrated target-law transfer to prove `ProbabilityTheory.HasCondSubgaussianMGF` for the successor centered reward under generated finite-pair history; it has no ambient `h_integrable_exp` or law-source hypothesis, and its canonical finite-sum tail consumer is compiled downstream, while arbitrary ambient transport and final regret remain open |
| compiled local reward-only canonical centered finite-sum tail leaves | 1 | `ConditionalExpectationReward.generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted` proves the zero-initialized successor centered-reward process strongly adapted to generated `historyFiltrationSucc`, and `ConditionalExpectationReward.historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure` combines that fact, zero-index sub-Gaussianity, the canonical successor conditional-MGF witnesses, and `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` into an ENNReal Azuma-Hoeffding bound for the `Finset.range n` sum covering centered rewards `1..n-1`; empirical-mean/confidence specialization and final bandit theorems remain open |
| compiled local canonical trajMeasure selected-reward finite-pair-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure`, a notation-alignment wrapper restating the canonical selected-reward next-reward law with `History.finitePairHistoryOfTrace` as the finite pair prefix; this matches project history notation but still does not prove ambient `Omega`/`History.historyFiltrationSucc` transport |
| compiled local canonical trajMeasure selected-reward reward-history condExpKernel-map leaves | 1 | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_rewardHistoryOfTrace_condExpKernel_map_trajMeasure`, a projection wrapper specializing the finite-pair-history selected-reward law to pair context/state maps built from `History.pairHistoryRewardProjection`, so the RHS is stated with `History.finiteRewardHistoryOfTrace`; this remains canonical `trajMeasure` only |
| compiled local generated selected-reward finite-pair-history source-contract leaves | 1 | `ConditionalExpectationReward.GeneratedActionSelectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_finitePairHistory_reward_map_eq_selected_policy`, and `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_selectedRewardFinitePairHistoryLawSource`, an ambient generated selected-reward law source and adapter that feeds the existing full finite-pair `partialTraj` source route; it stores and consumes the reward-law field rather than proving ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history partialTraj source-projection leaves | 1 | `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_selectedRewardFinitePairHistoryLawSource`, a direct projection from the generated selected-reward finite-pair-history source to the theorem-card-shaped full `finitePairHistoryOfTrace` partialTraj/condExpKernel law over `generatedActionFromRewardHistory`; it still consumes the selected-reward law field rather than proving ambient trajectory transport |
| compiled local definitional actual-reward source to selected finite-pair-history source leaves | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_definitionalActualRewardMapSource`, a source conversion from the definitional actual-action reward-coordinate source into the generated selected-reward finite-pair-history source by unfolding `generatedActionFromRewardHistory` and projecting finite pair histories to reward histories; it still consumes the actual-action reward-coordinate law |
| compiled local practical raw-range source to selected finite-pair-history source leaves | 1 | `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`, `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_uniformVarianceBoundedSource`, and `ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_historyVarianceBoundedSource`, source-conversion wrappers projecting the practical definitional raw-range/measurable-mean-range generated random next-pair package and its uniform/history variance wrappers into `GeneratedActionSelectedRewardFinitePairHistoryLawSource` through the full finite-pair `partialTraj` source projection; they still assume the packaged random next-pair law and do not prove ambient trajectory transport |
| compiled local practical source via selected finite-pair-history conditional-MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource`, and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le`, route-specific wrappers showing the practical raw-range source and its uniform/history variance packages reach conditional mean-zero and conditional MGF by first constructing `GeneratedActionSelectedRewardFinitePairHistoryLawSource`; they still assume the packaged random next-pair law and variance/proxy contracts |
| compiled local generated selected-reward finite-pair-history source/comap mean-zero leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeBounded`, `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, and `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded`, direct consumers from either the generated selected-reward finite-pair-history source or the finite-pair comap selected-reward law plus raw/mean range regularity into ordinary succ-indexed conditional mean-zero; they still assume the selected-reward law field |
| compiled local generated selected-reward finite-pair-history source conditional-MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, direct consumers from the generated selected-reward finite-pair-history source plus raw/mean range regularity into succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witnesses under global, coarser global, selected-history, or coarser selected-history variance proxies; they still assume the selected-reward law field and variance/proxy contracts |
| compiled local generated selected-reward finite-pair-history source/comap uniform-variance MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity and a global variance ceiling into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness by constructing the full finite-pair `partialTraj` source internally; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history source/comap uniform larger-proxy MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity, a global variance ceiling, and `varianceCeiling <= c` into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at coarser proxy `c`; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law, variance ceiling, and proxy-domination contract |
| compiled local generated selected-reward finite-pair-history source/comap history-variance MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity and selected-history variance ceilings into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `varianceCeiling i` by constructing the full finite-pair `partialTraj` source internally; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law and does not prove ambient trajectory transport |
| compiled local generated selected-reward finite-pair-history source/comap history-variance larger-proxy MGF leaves | 1 | `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le` and `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le`, direct consumers from the finite-pair comap selected-reward law plus raw/mean range regularity, selected-history variance ceilings, and `varianceCeiling i <= c` into the succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at coarser proxy `c`; the route now accepts either the generated-history trim filter or the direct comap-trim filter and still assumes the selected-reward law, selected-history ceiling, and proxy-domination contract |
| compiled local measurable-sum leaves | 1 | `measurable_finset_sum_indicator_reward` |
| compiled local measurable-local-quantity leaves | 1 | `measurable_sumRewards` |
| compiled local measurable-regret leaves | 1 | `measurable_pseudoRegret` |
| compiled local measurable-pullcount leaves | 1 | `measurable_pullCount` |
| compiled local measurable-pullcount-cast leaves | 1 | `measurable_natCast_pullCount` |
| compiled local Rat measurability leaves | 1 | `measurable_rat_div_const`, a Rat division-by-constant wrapper under `[MeasurableSingletonClass Rat]` |
| compiled local integrability-sum leaves | 1 | `IntegrabilitySums.integrable_finset_sum` and `IntegrabilitySums.integrable_univ_sum`, Mathlib-backed finite-sum integrability wrappers for explicit `Finset` and finite-arm `Finset.univ` term families; this is not Bochner expectation linearity |
| compiled local Bochner expectation-sum leaves | 1 | `ExpectationBochnerSums.integral_finset_sum` and `ExpectationBochnerSums.integral_univ_sum`, Mathlib-backed finite-sum Bochner integral wrappers under per-term integrability; the bandit-specific expected-regret decomposition is tracked separately |
| compiled local Bochner/Real expected-regret pull-count leaves | 1 | `integrable_real_pseudoRegret_of_integrable_pullCount` and `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount`, Real-valued Bochner pseudo-regret integrability and expectation decomposition into finite gap-weighted expected pull counts under explicit per-arm pull-count integrability; this is not a Rat-valued expectation theorem, ENNReal lower-integral surrogate, concentration result, or final algorithm theorem |
| compiled local Real mean-regret pull-count leaves | 1 | `realMeanGap`, `realMeanRegret`, `realMeanRegret_eq_sum_gap_mul_pullCount`, and `integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount`, the LML-aligned Real scalar regret and Bochner expected pull-count decomposition; its kernel specialization compiles downstream, while ETC concentration/constants and argmax semantics remain separate |
| compiled local Real kernel-regret pull-count leaves | 1 | `realKernelMean`, `realKernelGap`, `realKernelRegret`, `realKernelGap_nonneg`, `realKernelRegret_eq_sum_gap_mul_pullCount`, and `integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount`, the stationary Real arm-kernel identity-integral specialization; Real ETC expected-count concentration/constants and argmax semantics remain separate |
| compiled local expectation-foundation leaves | 1 | `lintegral_actionTrace_eval_eq_indicator_one` |
| compiled local expectation-sum leaves | 1 | `lintegral_finset_sum_actionTrace_eval_eq_indicator_one` |
| compiled local expectation-pullcount leaves | 1 | `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` |
| compiled local expectation-weighted-pullcount leaves | 1 | `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` |
| compiled local expectation-pullcount-bound leaves | 1 | `lintegral_natCast_pullCount_le_time` |
| compiled local expectation-weighted-pullcount-bound leaves | 1 | `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` |
| compiled local expectation-finite-bandit-bound leaves | 1 | `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` |
| compiled local expectation-finite-bandit-model-bound leaves | 1 | `lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time` |
| compiled local expectation-pseudo-regret-ofReal-bound leaves | 1 | `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg` |
| compiled local expectation-pseudo-regret-rat-bound leaves | 2 | explicit Rat-gap adapter plus model-derived no-explicit-`hgap` adapter |
| compiled local scalar-ENNReal leaves | 1 | `ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg` |
| compiled local scalar-pseudo-regret leaves | 1 | `ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg` |
| compiled local independence foundation leaves | 1 | `IndependenceFoundation.iIndepFun_infinitePi_coord` and `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`, the Mathlib-backed infinite-product coordinate-transform independence wrapper and time-indexed reward-trace specialization |
| compiled local concentration leaves | 9 | `Concentration.intervalVarianceProxy`, `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`, `Concentration.subGaussian_sum_tail_of_iIndepFun`, `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`, `Concentration.condSubGaussian_sum_tail_of_stronglyAdapted`, `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`, `Concentration.variance_chebyshev_tail`, `Concentration.evariance_chebyshev_tail`, and `Concentration.variance_sum_of_pairwise_indep`, the generic bounded-centered Hoeffding MGF source, the Mathlib-backed independent and strongly adapted conditional sub-Gaussian finite-prefix tail wrappers and ENNReal-valued boundary adapters, plus the Mathlib-backed Chebyshev/evariance and pairwise-independent finite-sum variance wrappers |
| compiled local algorithm-wrapper leaves | 4 | thin ETC/UCB wrappers, including ETC round-robin periodicity and modular selector characterization |
| compiled local ETC trace leaves | 3 | fixed-commit phase-switching trace boundaries for exploration, commit, and best-arm commit phases |
| compiled local ETC trace-count leaves | 9 | exploration-prefix transfer, configured exploration-horizon count, exploration-horizon Nat denominator-positivity, Rat-cast denominator-positivity, Rat-cast nonzero denominator, one-step post-commit recurrence, closed-form post-exploration suffix count, and commit-arm/non-commit-arm suffix corollaries for the fixed-commit ETC trace |
| compiled local ETC empirical-mean leaves | 3 | `ETC.empMeanAtExploration`, `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`, `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`, and `ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`, the deterministic fixed-commit exploration-horizon empirical-mean API, positive-denominator finite-sum comparison bridge, and event-shape adapter into abstract fixed-horizon sumRewards tail events |
| compiled local ETC centered-diff finite-sum bridge leaves | 1 | `ETC.centeredPairwiseRewardDiff`, `ETC.centeredPairwiseGapThreshold`, `ETC.sumRewards_le_imp_centered_pairwise_sum_ge`, and `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`, the deterministic bridge from fixed-horizon sumRewards comparison to the concrete centered pairwise reward-difference finite-sum event |
| compiled local ETC centered-diff witness-contract leaves | 1 | `ETC.CenteredDiffSubGaussianWitnesses` and `ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`, the exact reward-law witness package consumed by the centered-diff sub-Gaussian producer |
| compiled local ETC conditional witness-contract leaves | 2 | `ETC.CenteredDiffCondSubGaussianWitnesses`, `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`, `ETC.CenteredRewardCondSubGaussianWitnesses`, and `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`, the conditional centered-diff witness package plus the reward-level source contract that constructs it from sampled centered-reward conditional MGF witnesses; independence plus unconditional centered-reward sub-Gaussianity supplies the fixed-action conditional MGF bridge, and bounded/source assembly is now compiled separately |
| compiled local ETC strongly-adapted history leaves | 1 | `ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc` and `ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`, the shifted generated-history adaptedness field for fixed-commit ETC centered pairwise reward differences; it does not derive conditional MGF or mean-zero witnesses |
| compiled local ETC conditional MGF source leaves | 4 | `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward`, `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward`, `ETC.hasCondSubgaussianMGF_of_indep_comap`, and `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`, the zero-summand MGF source, sampled-arm transfer, action-case assembly from sampled centered-reward conditional MGF witnesses, and independence-based conditional MGF bridge from unconditional centered-reward sub-Gaussianity; fixed-action bounded/source assembly is tracked in the bounded-source conditional route row |
| compiled local ETC bounded-source conditional route leaves | 4 | `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource`, `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource`, `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail`, `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail`, `ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail`, and `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`, the fixed `actionWithCommit` bounded-source assembly from `BoundedRewardTraceSource` to conditional mean-zero, reward-level conditional witnesses, pairwise tail contracts, and argmax wrong-commit probability consumers, including the canonical-tail no-`htail` variant and its infinitePi specialization |
| compiled local ETC conditional mean-zero source leaves | 2 | `ETC.centeredReward_condExp_eq_zero_of_indep`, `ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`, and `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, the Mathlib `condExp_indep_eq` wrapper, shifted-history specialization, succ-indexed Mathlib tail shape, direct reward-coordinate iIndepFun plus full fixed-action history conditional mean-zero wrapper under an explicit zero-integral side condition, and bounded-source wrapper that supplies that side condition from `BoundedRewardTraceSource` |
| compiled local martingale-difference witness leaves | 2 | `MartingaleDiff.SuccMartingaleDifference`, `MartingaleDiff.SuccMartingaleDifference.toPrefix`, `MartingaleDiff.SuccMartingaleDifference.stronglyAdapted'`, `MartingaleDiff.SuccMartingaleDifference.integrable'`, `MartingaleDiff.SuccMartingaleDifference.condExp_succ_ae_eq_zero`, `MartingaleDiff.SuccMartingaleDifferencePrefix`, `MartingaleDiff.SuccMartingaleDifferencePrefix.stronglyAdapted'`, `MartingaleDiff.SuccMartingaleDifferencePrefix.integrable_of_lt`, `MartingaleDiff.SuccMartingaleDifferencePrefix.condExp_succ_ae_eq_zero`, `MartingaleDiff.centeredRewardProcess`, `MartingaleDiff.succMartingaleDifference_centeredRewardProcess_of_condExp`, `MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp`, `MartingaleDiff.partialSumsSucc`, `MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`, `MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp`, `ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc`, `ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc`, `ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource`, and `ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource`, the global and finite-prefix martingale-difference witness contracts, centered reward process builders from adaptedness/integrability/conditional-mean-zero contracts, abstract Mathlib partial-sum `Martingale` wrappers, and fixed deterministic `actionWithCommit` bounded-source centered-reward instance; broad adaptive-policy reward-law construction remains open |
| compiled local stopping-time foundation leaves | 1 | `Budget.budgetExhaustionTime`, `Budget.isStoppingTime_budgetExhaustionTime_of_adapted`, and `Budget.measurableSet_budgetExhaustionTime_le_of_adapted`, the Mathlib `hittingAfter` wrapper showing an adapted `Nat`-valued accumulated-resource process reaches a budget at a stopping time, plus the level-`n` measurability event; this is not a BwK model, optional-stopping theorem, or resource-constrained regret proof |
| compiled local ETC reward-only past independence leaves | 1 | `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward` and `ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`, the reward-coordinate iIndepFun bridge proving centered reward at `i + 1` is independent of the reward-only past coordinate sigma-algebra generated by `j <= i`, plus the infinite-product specialization |
| compiled local ETC fixed-action history independence leaves | 1 | `ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`, and `ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`, the deterministic action-generator inclusion and full fixed `actionWithCommit` `History.historyFiltrationSucc` independence bridge for future centered rewards |
| compiled local ETC bounded-to-integrable source leaves | 1 | `ETC.centeredReward_integrable_of_mem_Icc` and `ETC.centeredReward_integrable_of_boundedRewardTraceSource`, the Mathlib `Integrable.of_mem_Icc` wrapper and action-matched `BoundedRewardTraceSource` wrapper turning bounded rewards into raw reward integrability |
| compiled local ETC centered-reward zero-integral source leaves | 1 | `ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`, `ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, and `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`, the exact raw-mean plus integrability source, bounded-Icc source, and action-matched `BoundedRewardTraceSource` wrapper for the centered reward zero-integral side condition |
| compiled local ETC centered-diff canonical-tail leaves | 1 | `ETC.centeredDiffSubGaussianTail`, `ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`, and `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`, the canonical exponential tail helper for the independent sub-Gaussian centered-diff route |
| compiled local ETC empirical-mean measurability leaves | 4 | `ETC.measurable_sumRewards_actionWithCommit_exploration`, `ETC.measurable_empMeanAtExploration_of_measurable_div_const`, `ETC.measurable_empMeanAtExploration`, and `ETC.measurable_empMeanAtExploration_coordinates`, the numerator bridge, explicit-division wrapper, no-`hdiv_const` wrapper, and coordinate-shaped wrapper |
| compiled local ETC count leaves | 4 | first-cycle count, add-`K` recurrence, `m * K` count, and configured exploration-horizon count |
| compiled local ETC regret leaves | 9 | exploration-only, fixed-commit exploration-horizon, suffix count-budget, coarse suffix, phase-split equality, optimal-commit no-extra-suffix, optimal-commit suffix bound, phase-split suffix-gap bound, and pointwise wrong-commit suffix-penalty assembly scaffolds |
| compiled local ETC measurability leaves | 8 | `ETC.measurableSet_commitArm_ne_bestArm`, `ETC.measurable_empMeanVector_of_forall_measurable`, `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`, `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`, `ETC.measurableSet_commitOracle_ne_bestArm`, `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`, `ETC.measurableSet_empMean_ge_empMean`, and `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`, the wrong-commit event, Mathlib Pi-space empirical-mean vector, countable score-vector oracle-choice, coordinatewise empirical-mean-to-oracle-choice composition, oracle-selected wrong-commit, coordinatewise empirical-mean-to-oracle-wrong-event composition, pairwise empirical-mean comparison, and finite existential wrong-mean event measurability leaves |
| compiled local ETC event-reduction leaves | 2 | `ETC.wrong_commit_subset_exists_empMean_ge_bestArm` and `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`, the pure wrong-commit set-inclusion leaf and the abstract commit-oracle argmax consumer |
| compiled local ETC probability-wrapper leaves | 20 | `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`, `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`, `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`, `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`, `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`, `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`, `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`, and `ETC.real_measure_fixedProductArgmaxCommit_ne_bestArm_le_fixedProductWrongCommitTailBudgetReal_of_infinitePi_bounded_actionMean`, the arbitrary-measure monotonicity, finite-union upper-bound, final elementary assembly, abstract pairwise-tail consumer, if-zeroed nonbest pairwise-tail consumer, filtered-sum tail-consumer wrapper, oracle-specialized pairwise-tail consumers, canonical centered-diff wrong-commit bound, reward-coordinate-law wrong-commit bound, strong all-arm bounded-reward wrong-commit bound, action-matched wrong-commit bounds, source-contract wrong-commit wrapper, bounded-source conditional-route probability wrappers, fixed product-coordinate source wrong-commit wrappers, and the fixed-product `Measure.real` probability bridge |
| compiled local ETC concentration-bridge leaves | 6 | `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`, `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`, `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`, `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`, `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`, and `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, the abstract sub-Gaussian producer surface, the concrete centered-diff independent and conditional specializations for `ETC.PairwiseEmpMeanTailContract`, the deterministic transfer from centered reward sub-Gaussianity to centered pairwise reward-difference sub-Gaussianity, the Mathlib Hoeffding-lemma source from bounded rewards plus exact mean identities, and the action-matched source-contract consumer for that centered reward sub-Gaussian witness |
| compiled local ETC reward-law transfer/source leaves | 26 | `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`, `ETC.centeredPairwiseRewardDiffVarianceProxy`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`, `ETC.centeredRewardBoundVarianceProxy`, `ETC.centeredReward_integrable_of_mem_Icc`, `ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`, `ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward`, `ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`, `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`, `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`, `ETC.BoundedRewardTraceSource`, `ETC.centeredReward_integrable_of_boundedRewardTraceSource`, `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`, `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`, `ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`, `ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`, `ETC.boundedRewardTraceSource_infinitePi_actionWithCommit`, and `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`, the deterministic transfer from reward-trace time-coordinate independence, the action-case variance proxy, integrability and zero-integral source wrappers, reward-only and full fixed-action history independence bridges plus succ-indexed conditional mean-zero/conditional MGF shapes, bounded-source conditional mean-zero, wrong-commit bounds under centered reward sub-Gaussian witnesses and bounded rewards, the action-matched variants keyed to the actually pulled arm, the bounded-reward variance proxy, the compiled action-matched source-contract package plus consumers, and the concrete fixed product-coordinate source |
| compiled local ETC lower-integral regret assembly leaves | 7 | `ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductBadGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean`, and `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean`, the abstract, concrete argmax/infinitePi, polished fixed product-coordinate bad-gap, conservative sum-gap-adapted, polished fixed product-coordinate sum-gap, sharper max-gap-adapted, and polished fixed product-coordinate max-gap `ENNReal.ofReal` lower-integral bridges from wrong-commit probability control to an ETC regret surrogate |
| compiled local ETC Bochner expected-regret assembly leaves | 19 | the abstract/fixed-product/canonical bounded endpoints, complete dependency-light max-gap/per-arm bounded transports, canonical direct-MGF per-arm endpoint, its equal-prefix/external-`condDistrib`/scheduled-arm/full-history/action-dependent selected-kernel transport, and the Real per-arm count-to-commit-probability expected-count endpoint; dependency-light direct-MGF `Rat` law transport, Real kernel scalar bookkeeping, and expected-count integration are closed, while direct LML integration, the concrete Real commit-fiber exponential probability producer, and argmax alignment remain open |
| ETC wrong-commit design cards | 1 | `ETC-WRONG-COMMIT-PROBABILITY-DESIGN`, a theorem-card-only event-reduction route, not a local proof |
| scanned local Lean declarations | 1237 | definitions, structures, and theorems in `BanditRLProof/` after the Real ETC expected pull-count refresh |

The compiled local layer currently covers:

- finite action traces;
- pull counts, segment counts, and a dependency-light `List.range` finite-prefix bridge;
- reward sums, one segment-stability lemma, a dependency-light `List.range`
  fold bridge, and a filtered-list bridge under an explicit right-zero law;
- rational finite-arm mean models;
- a local best-arm dominance invariant showing every arm mean is at most the
  selected `bestArm` mean;
- model-derived Rat gap nonnegativity and finite max-gap invariants for
  `FiniteBanditModel.gap`;
- pseudo-regret zero/segment leaves and a dependency-light `List.range` fold bridge;
- a Mathlib-backed `pullCount` wrapper as filtered `Finset.range` cardinality;
- a Mathlib-backed selected reward-sum wrapper as a filtered `Finset.range` sum
  under `[AddCommMonoid Reward]`;
- a Mathlib-backed pseudo-regret wrapper as a `Finset.range` sum of gaps;
- a deterministic pseudo-regret decomposition as an arm-indexed sum of
  `gap * pullCount`;
- a deterministic scaffold converting per-arm pull-count upper bounds into a
  gap-weighted pseudo-regret upper bound;
- a Nat-count convenience adapter for algorithmic count lemmas that produce
  `pullCount <= B` with `B : Fin K -> Nat`;
- a uniform Nat-count adapter turning `forall a, pullCount a n <= B` into a
  `pseudoRegret <= (sum gaps) * B` bound;
- a deterministic finite-action count partition showing pull counts sum to the
  time horizon;
- first measure-foundation canaries showing measurable action evaluations yield
  measurable action-equality events and measurable constant-valued pull
  indicators;
- finite action/reward history product objects over `Finset.Iic` prefixes,
  with measurable coordinate projections and measurable trace-restriction maps
  from timewise measurable action/reward traces;
- a first expectation/integration canary showing the `ENNReal` lower integral
  of an action-equality pull-event indicator equals the event measure;
- an `ENNReal` lower-integral finite-sum bridge for action-equality pull-event
  indicators;
- an `ENNReal` lower-integral identity connecting scalar-casted recursive
  `pullCount` to the finite sum of action-event measures;
- an `ENNReal` lower-integral finite-arm weighted pull-count bridge,
  converting `sum_a gap a * pullCount a n` to weighted action-event measures;
- an `ENNReal` probability-measure pull-count budget bound, showing the
  lower integral of a scalar-casted pull count is at most the horizon;
- an `ENNReal` probability-measure weighted pull-count budget bound, showing
  a finite weighted lower-integral pull-count sum is bounded by its weighted
  horizon budget;
- a `Fin K`/`Finset.univ` specialization of that weighted probability budget
  bound for finite-arm algorithm theorem scaffolds;
- an `ENNReal.ofReal` surrogate model-gap wrapper bound for
  `FiniteBanditModel.gap : Fin K -> Rat`, explicitly before any faithfulness
  or Bochner expected-regret claim;
- a scalar `ENNReal.ofReal` faithfulness leaf for finite sums of nonnegative
  real weights times natural counts;
- a pointwise scalar/model pseudo-regret faithfulness bridge from Rat-valued
  pseudo-regret to the `ENNReal.ofReal` weighted pull-count expression under an
  explicit gap nonnegativity hypothesis;
- an `ENNReal.ofReal` lower-integral pseudo-regret bound under explicit gap
  nonnegativity, before any Rat-valued or Bochner expected-regret claim;
- a Rat-level gap nonnegativity contract adapter for that lower-integral bound,
  retained as a generic explicit-`hgap` route;
- a no-explicit-`hgap` `ENNReal.ofReal` lower-integral pseudo-regret bound
  using `FiniteBanditModel.gap_nonneg`;
- a Real-valued Bochner expected-regret decomposition, under explicit per-arm
  Real-cast pull-count integrability, from pseudo-regret to the finite sum of
  Real-cast gaps times expected pull counts;
- thin ETC and UCB wrapper lemmas, including ETC round-robin periodicity.
- fixed-commit ETC phase-switching trace boundaries, with exploration-prefix
  agreement to the pure round-robin selector, post-horizon agreement to the
  supplied commit arm, and best-arm agreement when the commit arm is selected
  best arm.
- an exploration-prefix pull-count transfer from the fixed-commit ETC trace to
  the pure round-robin exploration trace.
- a configured exploration-horizon pull-count theorem for the fixed-commit ETC
  trace.
- a deterministic exploration-horizon positive pull-count theorem for the
  fixed-commit ETC trace under `0 < spec.explorationPulls`, serving as the
  first Nat-level denominator-positivity leaf for later empirical means.
- a Rat-cast exploration-horizon positive pull-count theorem for the
  fixed-commit ETC trace, serving as the first rational denominator adapter for
  later empirical means.
- a Rat-cast exploration-horizon nonzero pull-count theorem for the
  fixed-commit ETC trace, serving as the first rational nonzero-denominator
  adapter for later empirical means.
- a one-step post-commit pull-count recurrence for the fixed-commit ETC trace.
- a closed-form post-exploration suffix pull-count theorem for the fixed-commit
  ETC trace.
- a non-commit-arm post-exploration suffix pull-count stability corollary for
  the fixed-commit ETC trace.
- a commit-arm post-exploration suffix pull-count corollary for the
  fixed-commit ETC trace.
- deterministic pseudo-regret scaffolds for the fixed-commit ETC trace through
  the exploration horizon, suffix count-budget, coarse suffix, phase-split
  equality, optimal-commit no-extra-suffix equality, optimal-commit suffix
  bound, and phase-split suffix-gap bound.
- the first ETC wrong-commit event measurability canary:
  `ETC.measurableSet_commitArm_ne_bestArm`.
- the pure ETC wrong-commit event-reduction set inclusion:
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.
- the arbitrary-measure wrapper for the wrong-commit event reduction:
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`.
- the pairwise empirical-mean comparison-event measurability canary:
  `ETC.measurableSet_empMean_ge_empMean`.
- the finite existential wrong-mean event measurability wrapper:
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`.
- the reusable finite-union probability/outer-measure wrappers:
  `ProbabilityUnionBound.measure_biUnion_finset_le`,
  `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`, and
  `ProbabilityUnionBound.measure_iUnion_fintype_le_sum`.
- the abstract finite-horizon UCB bad-event summability wrapper:
  `UCBSummability.finiteHorizonBadEvent`,
  `UCBSummability.measure_finiteHorizonBadEvent_le_sum`, and
  `UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum`.
- the deterministic finite-action EXP3 potential surface:
  `Exp3Potential.potential`, `Exp3Potential.updatedWeight`,
  `Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one`,
  and `Exp3Potential.potentialProcess_telescope_sum_range`.
- the deterministic FTRL one-step surface:
  `FTRL.linearLoss`, `FTRL.finiteSimplex`,
  `FTRL.regularizedObjective`,
  `FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer`,
  and `FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer`.
- the deterministic finite-simplex Tsallis regularizer surface:
  `Tsallis.powerSum`, `Tsallis.entropy`,
  `Tsallis.negEntropyRegularizer`,
  `Tsallis.powerSum_nonneg_of_finiteSimplex`, and
  `Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex`.
- the finite-union probability wrapper for the wrong-mean event:
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`.
- the final elementary probability assembly from wrong commit to the finite
  guarded wrong-mean-event sum:
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`.
- the abstract pairwise-tail consumer wrapper from wrong commit to a finite sum
  of non-best pairwise tail bounds:
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`.
- the if-zeroed nonbest pairwise-tail consumer wrapper from wrong commit to a
  finite sum whose selected best-arm summand is forced to zero:
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`.
- the filtered-sum pairwise-tail consumer wrapper from wrong commit to an
  explicit filtered finite sum over non-best arms:
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`.
- a theorem-card-only wrong-commit probability design reducing non-best commit
  to empirical-mean comparison events, awaiting argmax wiring, actual pairwise
  tail proofs, filtration, and final ETC theorem assembly.
- a fixed-commit ETC empirical-mean measurability wrapper under an explicit
  Rat division-by-constant measurability contract, before deciding the Mathlib
  division import/wrapper route.
- a Rat division-by-constant measurability wrapper under
  `[MeasurableSingletonClass Rat]`, before consuming it to remove the explicit
  `hdiv_const` argument from the ETC empirical-mean theorem.
- a no-`hdiv_const` fixed-commit ETC empirical-mean measurability theorem that
  consumes the Rat wrapper under `[MeasurableSingletonClass Rat]`.

The compiled local layer does not yet cover:

- full policy predictability, conditional reward-law transfer, posterior
  kernels, infinite action/reward trajectory laws, and conditional expectation
  contracts;
- most probability theorem contracts beyond action equality events, indicators,
  finite sums, local quantities, finite-sum Bochner wrappers, the Real-valued
  expected-regret pull-count decomposition, and lower-integral canaries;
- sub-Gaussian, Hoeffding, Chernoff, variance, or martingale tail proofs;
- probability-facing pull-count decompositions beyond the explicit Bochner/Real
  integrability contract;
- Rat-valued expected regret and algorithm-specific expected-regret theorem
  routes beyond the current Real-valued Bochner decomposition and
  `ENNReal.ofReal` lower-integral surrogate;
- imported or ported LML UCB/ETC/Thompson theorems;
- EXP3 estimator/log/regret, KL-UCB, Tsallis-INF/FTRL, OFUL/LinUCB, BwK,
  pure exploration, RL/MDP final theorem surfaces;
- full Markdown/LaTeX exports for closed textbook theorems.

## Distance By Layer

The table below is an engineering audit, not a mathematical impossibility
claim.  `compiled` means the local Lean gate proves it now.  `carded` means the
source or retrieval route exists.  `missing` means the route still needs leaf
statements, imports, or local proofs.

| Layer | Current status | What remains |
| --- | --- | --- |
| Harness and memory workflow | mostly compiled/tooling | add richer population operations and reviewer audits |
| Source/paper/scenario map | broad card coverage | keep current with new papers and check every source route |
| Proof weapons | carded | must be decomposed per task; not proof certificates |
| Finite bookkeeping and model invariants | first Mathlib wrapper layer, best-arm dominance, gap nonnegativity, no-explicit-`hgap` lower-integral bound, deterministic count-bound scaffold, Nat-count adapter, and uniform Nat adapter compiled | reviewer-check before choosing ETC-specific counts or Bochner/integrability |
| Regret decomposition | deterministic pull-count identity and Real-valued Bochner expected-regret pull-count identity compiled | Rat-valued expectation, probability-facing expectation APIs, and algorithm-specific regret decompositions still need separate contracts |
| Measure/probability foundation | event/measurability, finite action/reward history product measurability, pair-coordinate trace-prefix measurability, pair-history successor extension measurability, singleton-history filtration, policy/state measurability, policy-generated action trace coordinate measurability, reward-kernel selected-measure measurability, posterior-kernel selector measurability, Thompson posterior-action identity ledger consumers, finite/countable posterior best-action measurability wrapper, one-step policy/reward Markov-kernel composition, selected-reward event and `Measure.map` marginal wrappers, kernel-level centered-reward law transfer, finite-prefix reward-history `partialTraj` assembly, finite-prefix action/reward pair trajectory kernels, one-step `partialTraj` next-coordinate marginal wrappers, the full-prefix frozen-extension `partialTraj` wrapper, explicit conditional-kernel integral and pushforward-map consumers, frozen-history-to-centered-target bridge, conditional-kernel frozen-past route for conditioning-measurable events/countable variables/finite reward histories, finite-history measurability hookup for coordinate-measurable reward prefixes and generated `History.historyFiltrationSucc`, finite action/reward pair-history frozen-past hookup under `[Countable Action]`, successor-extension decomposition of the generated conditional pair trace, `Measure.map_congr` pushforward form of that decomposition, map-law consumer specializations that discharge the frozen-past side condition from those hooks, action/reward pair-law marginalization into the reward-coordinate map-law consumer, generated-history/concrete trace-pair/projection-measurability/named finite-pair-trace specializations of that pair-law route, the partialTraj finite-pair-trace consumer and reusable next-pair projection adapter, the direct history-step next-pair reward-map adapter, the full finite-pair-trace reward-map adapter, the extension-map partialTraj consumer and extension-to-full-trace law adapter, the extension-map reward-map adapter, the pairmap-to-extension partialTraj law builder, the next-pair split-law builder, the action-freezing policy hookup for the split-law action side, the generated-history action-side hookup for visible finite pair histories, the shifted generated-trace source for pointwise policy generation, the generated-action actual/random-pair reward-law hookup through full finite-pair-trace law adapters and the conditional mean-zero route, the generated random-pair law source contract package, random-pair-to-actual-reward-map source conversion, plus centered-source regularity package and consumers, finite-sum Bochner wrappers, the Real-valued expected-regret pull-count decomposition, and lower-integral canaries compiled | pair/reward law construction, integrability source for the adaptive generated route, `partialTraj`/history-to-`condExpKernel` action/reward pair-law identification, Bayes-rule/regular-conditional posterior identification, posterior action-law construction/import, infinite trajectory laws, and full conditional-expectation contracts |
| Kernels/posteriors | reward-kernel contract, posterior-kernel contract, Thompson posterior-action identity ledger, finite/countable posterior best-action measurability wrapper, one-step policy/reward kernel composition, selected reward event and `Measure.map` marginal wrappers, kernel-level centered-reward law transfer, finite-prefix reward-history `partialTraj`, finite-prefix action/reward pair trajectory-kernel surfaces, one-step `partialTraj` next-coordinate marginal wrappers, the full-prefix frozen-extension `partialTraj` wrapper, the conditional-expectation partialTraj finite-pair-trace consumer, reusable next-pair projection adapter, direct history-step next-pair reward-map adapter, full finite-pair-trace reward-map adapter, extension-map reward-map adapter, and extension-to-full-trace law adapter, the pairmap-to-extension partialTraj law builder, the action-freezing policy hookup for the next-pair split-law action side, the generated-history action-side hookup for visible finite pair histories, the shifted generated-trace source for pointwise policy generation, the generated-action actual/random-pair reward-law hookup through full finite-pair-trace law adapters and the conditional mean-zero route, the generated random-pair source contract package, source-level canonical history-step pair-law consumer, random-pair-to-actual-reward-map source conversion, definitional source-level canonical history-step pair-law consumer, centered-source canonical pair-law consumer, definitional centered-source canonical pair-law consumer, and centered-source regularity package, explicit history-step conditional-kernel consumer surfaces, and reward-coordinate pushforward-map consumers compiled | conditional distributions, construction of the generated random-pair law source, `condExpKernel` reward-law identification, Bayes-rule posterior identification, posterior action-law construction/import, and Bayesian regret |
| Concentration/tails | independent and strongly adapted conditional Mathlib import wrappers, Chebyshev/evariance wrappers, finite union bounds, and abstract finite-horizon UCB bad-event summability compiled | UCB empirical-mean concentration instantiation, ETC pairwise reward-difference conditional instantiation polish, and asymptotic/series simplifications |
| UCB/ETC textbook routes | wrappers plus theorem cards, with abstract finite-horizon UCB bad-event summability, deterministic/event-level UCB confidence-radius consumers, finite-arm confidence bad-event union bound, confidence-event measurability, finite-horizon confidence-event union assembly, finite-horizon good-event gap and large-gap subset consumers, abstract upper/lower tail-budget consumption, absolute-deviation concentration-event adapter, finite-variance Chebyshev UCB tail producer, abstract centered empirical-mean sub-Gaussian UCB tail producer, square-root radius-budget wrapper, schedule-agnostic logarithmic radius wrapper, constant-scale finite-horizon tail-budget folding, textbook delta confidence-budget and large-gap score-max probability wrappers, selected-action single-time/finite-time-set large-gap delta bridges, concrete finite-arm confidence-score argmax wrappers, finite-time selected-count lower-integral budget wrappers, an all-horizon recursive pull-count budget wrapper, a threshold/suffix-shaped pull-count split, an abstract free-time budget consumer, a free-time cardinality consumer, selected-small pathwise and lower-integral pull-count budgets, selected-small/selected-large count decomposition, selected-large-count `T * delta` wrappers, recursive sample-count UCB count adapter, a source-count wrapper for history-derived sample counts, a history-action transfer wrapper, a generated-policy trace wrapper, an identity-policy concrete score-argmax generated-trace wrapper, a concrete textbook-radius split instantiation, a threshold-cardinality consumer, a half-gap threshold adapter, square/eight-proxy-log threshold consumers, a proxy-small threshold consumer, a sample-count threshold consumer, and a lower-bound-on-count consumer now compiled | concrete empirical-mean construction from reward histories, recursive adaptive UCB action trace, concrete proxy/count source from empirical rewards, and final regret; ETC expected-regret assembly remains separate |
| Thompson sampling | posterior-action ledger, canonical/reference samplers, posterior-invariance and recursive density transport, measurable environment-indexed trajectories, global uniform-reference recursive sampler coupling, premise-free actual-trajectory probability matching, finite-horizon Bayesian mean-regret decomposition, exact clipped-UCB score regularity, stationary reward-kernel arm-stream representation, all-time latent-stream trajectory support, and fixed-environment actual augmented-trajectory tails compiled; the pinned final LML declaration remains a theorem card | mix the pointwise tails through the augmented prior, build measurable clipped-confidence events and the two concentration expectation bounds, then close the final regret inequality |
| EXP3/adversarial | finite-action exponential-weights potential, importance-weighted conditional moments, generated exploration-mixed trajectory, predictable `[0,1]` feedback, finite-horizon Hedge/moment integration, the unoptimized expected predictable-regret theorem, deterministic parameter simplification, the large-horizon `4 sqrt(|A| T log|A|)` corollary, realized selected-loss expectation transport, and the all-horizon clipped-rate min bound compiled | high-probability regret, stochastic rewards, broader adversary models, and other EXP3 variants remain separate |
| Tsallis-INF/FTRL | generated expected environment regret, fixed-gap self-bounding, the paper-shaped all-arm-to-suboptimal consumer, deterministic ordinary-IW conjugate-potential stability, uncollapsed refined expected penalty, unified refined stability/penalty assembly, and concrete square-root-schedule harmonic and logarithmic fixed-gap theorems compile | transport broader stochastic/corrupted reward laws into the self-bounding contract |
| Linear/OFUL/LinUCB | the deterministic elliptical-potential, vector self-normalized concentration, scalar-ridge confidence, optimism, measurable recursive selection, concrete generated-trajectory reward law, selected-width, normalized all-round high-probability gap, measurable bad-event integration, finite-window expected fixed-optimal-arm pseudo-regret, explicit finite-window rate, fixed-model asymptotic expected regret, and horizon-indexed expected-average convergence routes compile; the algorithm parameter is `1/(T+1)^2` | anytime/one-policy consistency, minimax, contextual, dynamic-regret, pathwise/probability convergence, uniform-over-parameter, and broader linear-bandit routes remain separate |
| RL/MDP | finite state/action MDP data, Mathlib Markov transition kernel, measurable deterministic reward, stage-indexed Markov policy, induced state kernel, measurable policy Bellman operator, backward policy value, terminal condition, and chronological Bellman recursion compiled | generated finite policy trajectory and expected cumulative-reward/value identity, finite-action Bellman optimality, occupancy measures, UCB-VI optimism, and episode regret |
| Proof export | skeleton exists | exports must be generated from compiled theorem declarations |

## Textbook-Scope Completion Estimate

For the three current textbook/survey roots, ABRL has a broad map but not a
full proof library.

| Source root | Current coverage | Remaining proof strata |
| --- | --- | --- |
| Bubeck-Cesa-Bianchi 2012 | stochastic/adversarial routes and paper cards | UCB/EXP3 tails, lower bounds, minimax routes, final theorem exports |
| Lattimore-Szepesvari 2020 | main scenario tree and Mathlib routes | probability foundation, concentration chapters, ETC/UCB/MOSS/KL-UCB/linear proofs |
| Slivkins 2019/2024 | scenario atlas, Bayesian, Lipschitz, BwK, agents | Bayesian/posterior formalization, Lipschitz/metric trees, BwK and incentive proofs |

Pragmatic estimate: for the desired textbook-scale proof weapon library, the
current compiled Lean is under one tenth of the needed proof surface.  It is
useful because it sets stable harness rules and proves the first finite
bookkeeping leaves, but the major Mathlib-backed layers still need to be
imported, adapted, or proved.

## Required Next Milestones

1. Treat `ETC-EXPLOREARM-EQ-IFF-MOD` as the compiled modular selector helper
   for future ETC count theorems.
2. Treat `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` as the compiled first-cycle ETC
   round-robin count scaffold.
3. Treat `ETC-ROUND-ROBIN-ADD-K-COUNT` as the compiled full-cycle extension
   recurrence for ETC pull counts.
4. Treat `ETC-ROUND-ROBIN-MUL-K-COUNT` as the compiled multiple-full-cycle ETC
   count theorem.
5. Treat `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` as the compiled configured
   exploration-horizon count adapter.
6. Treat `ETC-EXPLORATION-REGRET-BOUND` as the compiled deterministic
   exploration-only ETC pseudo-regret scaffold.
7. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` as the compiled fixed-commit
   ETC trace boundary on the exploration prefix.
8. Treat `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` as the compiled fixed-commit
   ETC trace boundary after the exploration horizon.
9. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` as the compiled
   exploration-prefix pull-count transfer for the fixed-commit ETC trace.
10. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` as the compiled
   configured exploration-horizon pull count for the fixed-commit ETC trace.
11. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` as the
   compiled deterministic pseudo-regret scaffold for the fixed-commit ETC trace
   at the exploration horizon.
12. Treat `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` as the compiled
   one-step post-commit pull-count recurrence for the fixed-commit ETC trace.
13. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` as the compiled closed-form
   post-exploration suffix pull count for the fixed-commit ETC trace.
14. Treat `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` as the compiled
   non-commit-arm post-exploration pull-count stability corollary.
15. Treat `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` as the compiled
    commit-arm post-exploration pull-count corollary.
16. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` as the compiled
    reviewer-approved deterministic count-budget pseudo-regret scaffold for
    the fixed-commit ETC trace after the exploration horizon.
    The reviewer prompt was
    `reports/extended_pro_after_commitarm_suffix_count_candidate_prompt_2026-06-29.md`;
    the recorded answer is
    `reports/extended_pro_after_commitarm_suffix_count_response_2026-06-30.md`.
17. Treat `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` as the compiled
    reviewer-approved coarse uniform post-exploration suffix regret bound.  The
    reviewer prompt was
    `reports/extended_pro_after_suffix_budget_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_suffix_budget_regret_response_2026-06-30.md`.
18. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` as the compiled
    reviewer-approved fixed-commit post-horizon phase-split pseudo-regret
    equality. The reviewer prompt was
    `reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_coarse_suffix_regret_response_2026-06-30.md`.
19. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` as the compiled
    reviewer-approved phase-split exploration-plus-suffix-gap regret bound. The
    reviewer prompt was
    `reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_phase_split_regret_response_2026-06-30.md`.
20. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` as the compiled
    reviewer-approved optimal-commit no-extra-suffix-regret equality. The
    reviewer prompt was
    `reports/extended_pro_after_gap_bestarm_candidate_prompt_2026-06-30.md`;
    the recorded answer is
    `reports/extended_pro_after_gap_bestarm_response_2026-06-30.md`.
21. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` and
    `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the current deterministic
    ETC boundary: if the commit arm is the selected best arm, the post-horizon
    trace and regret contribution are controlled.
22. Treat `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as the theorem-card-only
    bridge, not as a completed probability proof.
23. Treat `ETC-MEAS-COMMITARM-NE-BESTARM` as the first compiled wrong-commit
    event measurability canary.
24. Treat `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` as the compiled pure
    wrong-commit set-inclusion leaf.
25. Treat `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` as the
    compiled arbitrary-measure monotonicity wrapper.
26. Treat `ETC-MEAS-EMPMEAN-GE-EMPMEAN` as the compiled pairwise
    empirical-mean comparison-event measurability canary.
27. Treat `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` as the compiled
    finite existential wrong-mean event measurability wrapper.
28. Treat `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` as the
    compiled finite-union probability upper-bound wrapper.
29. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` as the compiled
    final elementary event-probability assembly wrapper.
30. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` as the compiled
    abstract non-best pairwise-tail consumer wrapper.
31. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` as the compiled
    if-zeroed nonbest pairwise-tail consumer wrapper.
32. Treat `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled filtered-sum pairwise-tail consumer wrapper.
33. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the compiled
    deterministic Nat denominator-positivity leaf for fixed-commit ETC
    exploration counts.
34. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the
    compiled Rat denominator-positivity adapter for fixed-commit ETC
    exploration counts.
35. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` as the
    compiled Rat nonzero-denominator adapter for fixed-commit ETC exploration
    counts.
36. Treat `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` as the compiled
    deterministic fixed-commit exploration-horizon empirical-mean definition
    and denominator rewrite.
37. Treat `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled numerator-measurability bridge for fixed-commit ETC empirical
    means under stochastic reward traces.
38. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
    as the compiled full empirical-mean measurability wrapper under an
    explicit Rat division-by-constant measurability contract.
39. Treat `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` as the compiled
    Rat division-by-constant measurability wrapper under
    `[MeasurableSingletonClass Rat]`.
40. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled no-`hdiv_const` empirical-mean measurability theorem consuming
    the Rat wrapper.
41. Treat `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` as the compiled
    coordinate-shaped empirical-mean measurability wrapper selected by
    Extended Pro after the no-`hdiv_const` theorem.
42. Treat `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` as the compiled deterministic
    abstract commit-oracle argmax consumer for the wrong-commit event
    reduction.
43. Treat `ETC-COMMIT-ORACLE-PROB-WRAPPER` as the compiled oracle-specialized
    abstract pairwise-tail probability consumer selected by Extended Pro.
44. Treat `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` as the compiled
    oracle-specialized filtered-sum pairwise-tail probability consumer selected
    by Extended Pro.
45. Treat `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` as the compiled
    oracle-specialized if-zeroed nonbest pairwise-tail probability consumer
    selected by Extended Pro.
46. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` as the compiled
    oracle-selected wrong-commit event measurability wrapper under direct
    composed choice measurability, selected by Extended Pro.
47. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` as the compiled
    Mathlib-backed countable score-vector oracle-choice measurability wrapper
    selected by Extended Pro as an immediately compilable candidate.
48. Treat `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` as the compiled Mathlib
    Pi-space coordinate-to-vector empirical-mean measurability wrapper selected
    by Extended Pro.
49. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-choice measurability
    composition wrapper selected by Extended Pro.
50. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-wrong-event measurability
    composition wrapper selected by Extended Pro.
51. Treat `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled concrete argmax-oracle filtered-sum pairwise-tail consumer wrapper.
    `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally, packaging the
    fixed-commit ETC empirical-mean pairwise-tail assumption and its concrete
    argmax consumer.  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is also compiled
    locally as the positive-denominator bridge from empirical-mean comparison
    to fixed-horizon reward-sum comparison.  The tail contract itself is still
    not proved.  `TAIL-HOEFFDING-BOUNDED` is now compiled locally as the
    bounded-centered Hoeffding MGF source; `TAIL-SUBGAUSS-SUM`,
    `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, and `TAIL-COND-SUBGAUSS` are now compiled
    locally as Mathlib-backed sub-Gaussian finite-prefix tail wrappers, including the `ENNReal`
    event-probability shape for both independent and strongly adapted
    conditional routes.
    `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is also compiled locally, producing
    `ETC.PairwiseEmpMeanTailContract` from explicit non-best-arm sub-Gaussian
    witnesses and event-subset hypotheses.  The generic event-shape adapter
    from ETC empirical-mean comparison to abstract fixed-horizon `sumRewards`
    tail events is also compiled locally.  `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`
    now instantiates that implication with a concrete centered
    reward-difference finite-sum event, and
    `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` specializes the abstract
    producer to those summands.  `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`
    packages the exact reward-law witness fields consumed by that producer.
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` fixes the exact
    exponential tail budget, and
    `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` connects that budget to the
    concrete argmax-oracle wrong-commit probability consumer.  The
    reward-law route then compiles the trace-coordinate independence transfer,
    the centered reward sub-Gaussian transfer, the bounded-reward Hoeffding
    source, the bounded-to-integrable source, the centered reward
    zero-integral source, the strong all-arm bounded-reward wrong-commit
    bound, the action-matched bounded-reward
    wrong-commit bound, the
    `ETC.BoundedRewardTraceSource` contract wrapper, and the fixed
    product-coordinate source theorem.  Downstream work now needs the
    fixed-commit wrong-commit probability bound connected to expected-regret
    assembly before starting final adaptive ETC theorem work.
    On the canonical reward-only conditional route,
    `COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-AVERAGE-TAIL` now
    compiles the strictly-positive-denominator specialization from a centered
    successor sum tail to an aggregate average tail.  It does not provide an
    arm-wise empirical mean, a UCB/ETC confidence event, or a regret theorem;
    the `COND-EXPECT-REWARD` conversion-window and proof-obligation entries
    named by the retrieval index are absent from this worktree and must not be
    treated as current route evidence.
    The ETC fixed-product Bochner route now also has
    `ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET`: the public coordinate
    source contract is stated directly over `ETC.exploreArm`, with the former
    base commit arm eliminated from the theorem interface.  It is a compiled
    Real expected-regret theorem for the fixed product source, not a proof of
    the adaptive LML `Bandits.ETC.regret_le` target; action-dependent adaptive
    reward-law transport remains the precise missing technology.
    `ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` now provides the narrow
    deterministic history-reconstruction prerequisite: two reward traces that
    agree below the exploration horizon have equal fixed-commit empirical means
    at every arm. It has no probability or regularity contract and does not
    establish a generated action trace or adaptive reward law.
    `ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now turns that fact into the
    shifted generated-action state contract: completing
    `finiteRewardHistoryOfTrace reward t` by zero after `t` reproduces the
    ambient empirical score when `spec.explorationPulls * K <= t + 1`. It still
    does not construct or prove equality of the finite-history policy action.
    `ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now completes that action
    layer: the measurable policy over completed reward histories generates
    exactly `ETC.explorationArgmaxAction` when exploration pulls are positive.
    The remaining blocker is strictly the action-dependent reward-law and
    conditional-law transport, not policy definition, score recovery, or action
    measurability.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now proves the
    action-dependent full `partialTraj` law under the canonical Markov-kernel
    trajectory measure. The remaining transport is therefore specifically from
    that canonical kernel measure to the fixed-product or arbitrary adaptive
    environment surface, plus the model regularity identification required by
    the final theorem.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now supplies
    the conditional sub-Gaussian MGF for successor rewards centered at the
    selected arm's finite-bandit model mean, under an explicit centered kernel
    law and selected-history variance ceiling. The remaining deficit is the
    construction/transport of the centered regularity contracts and the
    tail/regret assembly, not conditional-MGF plumbing.
    `ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now constructs the raw
    context-independent Markov reward kernel from per-arm probability laws and
    proves exact selected-measure equality.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now constructs its
    centered model-mean law from common bounded arm laws and directly proves
    the canonical successor conditional MGF at the Hoeffding proxy. Time-zero
    initial-law alignment and the full selected centered-reward finite-sum tail
    are now compiled by `ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL`.
    `ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT` now removes the
    bounded-support premise from the canonical pairwise concentration layer:
    direct per-arm centered MGFs at one common proxy and exact model means
    construct the kernel law, initial/successor fixed-filtration witnesses, and
    the empirical-mean pairwise tail contract. This remains a `Rat` theorem and
    does not yet provide commit-fiber probability, per-arm regret consumption,
    external law transport, or exact LML tie semantics.
    `ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now additionally compiles the
    actual empirical-mean pairwise tail contract and finite-union wrong-commit
    probability under canonical `trajMeasure`, using exploration-prefix action
    and filtration equality rather than coordinate independence.
    `ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now closes the remaining
    canonical adapter: finite ENNReal-to-Real probability conversion,
    empirical-mean argmax/wrong-event measurability, finite-valued integrability,
    and the generated-action Real expected-regret theorem all compile. The
    external exploration-prefix law consumer now also compiles: the regret
    integrand factors through `m*K` rewards and `Measure.integral_map`
    transports the bound from equality of finite-prefix pushforwards. The new
    external conditional-law consumer derives that equality from the zeroth
    marginal and successor `condDistrib` laws through exploration, on an
    arbitrary sample space. The scheduled exploration-arm adapter now removes
    the local step kernel from that contract: callers provide only the initial
    arm law and conditional laws of the scheduled exploration arms. The
    remaining environment work is a concrete source or `IsAlgEnvSeq` bridge.
    The full action/reward-history consumer now closes the local conditioning
    coarsening that mirrors `IsAlgEnvSeq.hasCondDistrib_feedback`; the remaining
    seed-specific law step of reducing the action-dependent stationary kernel
    with exploration action a.e. equality is now compiled in dependency-light
    form. A direct newer-toolchain wrapper is optional integration work.
    The direct-MGF contract now compiles through canonical per-arm regret,
    exploration-prefix equality, generic initial/successor conditional laws,
    the scheduled exploration-arm external endpoint, and the LML-shaped full
    action/reward-history constant-law consumer and its action-dependent
    selected-kernel adapter. Dependency-light direct-MGF `Rat` law transport is
    therefore closed. Exact LML alignment next requires porting the remaining
    reward/model surface to Real and aligning argmax ties and exact pull-count/
    RHS semantics; a direct toolchain wrapper remains separate integration.
52. Extend the Mathlib-backed probability layer only with explicit
    measurable/integrable contracts.
53. Convert retrieval cards for sub-Gaussian tails into exact imported theorem
    packets and local wrappers.
54. Close one narrow textbook theorem end-to-end, likely a small UCB/ETC
   bookkeeping or concentration-dependent theorem.
55. Export that theorem to Markdown and LaTeX from compiled declarations.
56. Only then expand to TS, EXP3, Tsallis-INF/FTRL, OFUL, BwK, and RL/MDP final
   theorem branches.

## Non-Negotiable Leaf Discipline

Every new leaf must satisfy the local contract:

- decompose aggressively;
- target a lemma that fits within one lower-agent context window;
- specify more than the theorem: local APIs, imports, assumptions, intended
  proof route;
- treat persistent failure as mathematical signal;
- promote hidden regularity into reusable theorem contracts;
- do not frequently change the proof route without a reviewer-visible reason.

The point of the audit is not to lower ambition.  It is to prevent agents from
mistaking a broad tree for completed Lean mathematics.

## ETC Per-Arm RHS Update

The generic per-arm Bochner assembly compiles as
`ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob`.
It preserves `sum_a (r * gap a) * P(commit=a)` instead of charging the entire
wrong event by `maxGap`. The arm-specific canonical ENNReal commit-event bound
and its finite Real conversion now feed
`ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal`.
The proof substitutes the non-best bounds termwise and removes the best-arm
summand with `gap_bestArm`, without a union. External exploration-prefix
transport now also compiles: equality of finite prefix pushforwards gives equal
regret integrals and transfers the same per-arm RHS without full trajectory or
suffix laws. The initial marginal plus successor `condDistrib` consumer now
constructs that identity and pulls the integral back to the original sample
space. The scheduled exploration-arm per-arm adapter now compiles as well: it
uses the deterministic exploration step-kernel equality with `Context := Unit`
and preserves the same gap-weighted RHS. The full action/reward-history
constant-law adapter now compiles too, using generic conditional-law coarsening
and marginal extraction. Its action-dependent selected-kernel per-arm adapter
now closes the dependency-light bounded-Rat law chain. The canonical pairwise
concentration layer also accepts direct common-proxy arm MGFs without bounded
support. Its concrete commit-fiber probability, finite Real tail, and canonical
gap-weighted per-arm Bochner theorem now compile as well, without a max-gap
collapse or arm union. Its direct-MGF endpoint now also propagates through the
external conditional-law chain. The separate Real scalar regret/pull-count
leaf below closes the target-side bookkeeping mismatch. Downstream leaves now
also close kernel means, native Real concentration/constants, per-arm counts,
finite-prefix law transport, and scheduled conditional-law transport. The
remaining exact-route work is upstream field/tie alignment; a direct
newer-toolchain LML wrapper remains optional integration work.

## Real Mean-Regret Pull-Count Foundation

`REAL-MEAN-REGRET-PULLCOUNT` now compiles in
`BanditRLProof.RealMeanRegretPullCount`. It defines the exact-route Real gap as
`iSup mean - mean a`, defines finite-horizon Real regret, proves its
gap-times-pull-count identity, and proves the Bochner expected pull-count
identity under explicit per-arm pull-count integrability. It reuses the local
Mathlib-backed finite-sum and pull-count wrappers and assumes no probability,
kernel, reward law, concentration, or argmax semantics.

The downstream `REAL-KERNEL-REGRET-PULLCOUNT` leaf now also closes stationary-
kernel identity-integral specialization, including kernel-gap nonnegativity and
the kernel-facing Bochner pull-count equality. Downstream leaves now also close
the exact canonical per-arm producer and the cast-pushforward Real-kernel
finite-sum assembly. Later native Real product, prefix-law, and action-dependent
source leaves close the external selected feedback-law transport. Remaining
exact ETC work is horizon action equality and selector tie equivalence. If that
route fails, isolate its first action or tie-equivalence fact; do not mark
`LML-ETC-REGRET` as ported.

## Real ETC Expected Pull-Count Endpoint

`REAL-ETC-EXPECTED-PULLCOUNT` now compiles in
`BanditRLProof.Algorithms.ETCExpectedPullCount`. It proves finite-measure
integrability for the Real cast of each measurable `actionWithCommit` pull
count, integrates the deterministic suffix formula exactly, and exposes the
LML-shaped probability consumer `m + (n - K*m) * p`. This closes the counting
and Bochner integration half of the per-arm expected-count route.

## Exact Common-Sub-Gaussian ETC Per-Arm Endpoint

`ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT` now compiles in
`BanditRLProof.Algorithms.ETCExactSubGaussianTail`. On the existing canonical
generated-history model with `Rat` arm laws and Real centered MGFs, it proves
the exact proxy sum `2*m*sigma2`, the non-best threshold `m*gap`, the LML
exponent `exp (-m*gap^2/(4*sigma2))`, the corresponding commit-fiber bound,
and the full per-arm Real expected pull-count inequality. The zero-proxy case
is handled explicitly because Lean's division is total.

This closes the exact common-proxy constant arithmetic and its canonical
per-arm count producer. This leaf itself is not a native Real reward-kernel
theorem, but downstream leaves now provide the native Real product theorem,
kernel gaps, and external scheduled conditional-law transport. The remaining
route is the actual `IsAlgEnvSeq` field wrapper and upstream
`measurableArgmax` tie semantics, not a weaker exponent or another Rat leaf.

## Rat Arm-Law Pushforward Real-Kernel Exact Regret

`ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRatArmLawRealKernel`. It maps each Rat arm law to
Real, proves the resulting countable arm kernel is Markov, identifies its
identity-integral means and `iSup` gaps exactly with the cast model values, and
assembles the exact per-arm count inequalities into the full LML-shaped finite
sum for `realKernelRegret`. The best-arm summand is eliminated explicitly.

This closes kernel-gap alignment and finite-arm summation for the canonical
Rat-law route. The Real kernel here remains a cast pushforward with Rat sample
coordinates, but downstream native Real product and finite-prefix leaves now
close that separate law-transport gap. The precise remaining blocker is
mapping the actual upstream `IsAlgEnvSeq` fields and proving ETC
action/`measurableArgmax` tie equivalence.

## Native Real Empirical Mean, Argmax, And Count Surface

`ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` now compiles in
`BanditRLProof.Algorithms.ETCRealEmpiricalMean`. It defines exploration
empirical means directly on `RewardTrace Real`, proves a deterministic finite
argmax maximality certificate, and proves that selector measurable from
timewise measurable rewards. The proof does not countabilize `Fin K -> Real`:
it rewrites a dynamically selected score as a finite indicator sum and then
proves the comparison fold measurable step by step. The resulting native Real
action instantiates both the exact expected pull-count identity and its
abstract commit-fiber probability-bound consumer.

This closes the local native Real algorithm/count surface, including explicit
keep-the-old-arm tie behavior. The subsequent canonical product-law, prefix,
and action-dependent source leaves supply native Real concentration and map the
upstream-shaped selected feedback laws. Upstream horizon action equality and
selector tie equivalence remain separate obligations.

## Native Real Infinite-Product Exact ETC Regret

`ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealInfinitePiTail`. For a Markov Real reward
kernel with a common centered sub-Gaussian proxy, it chooses a finite
identity-integral best arm and works under the action-matched law
`Measure.infinitePi (fun t => nu (ETC.exploreArm spec t))`. It proves the
native Real empirical-comparison event inclusion, coordinate independence and
MGF transport, exact `2*m*sigma2` proxy sum, single-arm
`exp (-m*gap^2/(4*sigma2))` commit bound, matching expected pull count, and
the complete LML-shaped finite sum for `realKernelRegret`. The `sigma2 = 0`
case is handled explicitly.

This closes canonical independent native Real concentration, count, kernel
gap, and regret assembly. The external finite-prefix transport below now
removes the canonical ambient-space restriction; upstream structure and
selector alignment remain explicit.

## Native Real External Prefix-Law Exact ETC Regret

`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealPrefixLawTransport`. It proves that native Real
empirical means, commit, action, and horizon regret factor through the finite
`Fin (m*K)` reward prefix, transports the canonical exact theorem across an
equality of prefix pushforward laws, and permits an arbitrary external action
that agrees a.e. with the local action only through horizon `n`.

The strongest endpoint removes the abstract prefix-law premise as well. It
uses the generic finite reward-prefix uniqueness theorem with the scheduled
exploration-arm zeroth marginal and successor `condDistrib` laws, identifies
the resulting constant-kernel Ionescu-Tulcea trajectory with
`Measure.infinitePi` via projective-limit uniqueness, and concludes the full
external exact finite-sum regret bound. It requires no
`StandardBorelSpace Omega`, external-action measurability, full reward-trace
law equality, or infinite-horizon action equality.

The downstream source adapter below now constructs `hzero` and scheduled
successor `hcond` from action-selected full-history feedback laws. The only
remaining exact LML blocker is horizon action generation and tie alignment.

## Native Real Action-Dependent Source Exact ETC Regret

`ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealSourceAdapter`. Its endpoint accepts the
upstream `IsAlgEnvSeq` feedback-law shape directly: reward zero conditioned on
action zero through `Kernel.ofFunOfCountable`, and reward `i+1` conditioned on
the complete finite action/reward history plus action `i+1` through the
stationary action-selected kernel.

The proof freezes those kernels with the a.e. round-robin exploration action,
extracts the zeroth marginal, projects full pair histories to reward prefixes,
and invokes the compiled native Real exact theorem. It adds no
`StandardBorelSpace Omega`, full trajectory law, independence, or
infinite-horizon action equality.

The pinned LML source audit at commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74` confirms the exact field shapes.
The downstream least-encoded action leaf now closes the selector and
`hactionETC` assembly obligations; this source leaf should not be reopened.

## Native Real Least-Encoded Action Exact ETC Regret

`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealArgmaxTie`. The local strict-improvement fold
is identified with Mathlib's first-occurrence `List.argmax`; combining
`index_of_argmax` with `idxOf_finRange` proves least-`Encodable.encode`
selection. A specialized `Nat.find` selector matching the pinned LML
definition is then proved equal to the fold.

The same module combines a.e. round-robin exploration, least-encoded commit at
`K*m`, and post-commit persistence into equality with the native Real ETC
action at every time. Its strongest endpoint consumes those action fields and
the upstream-shaped selected feedback laws and returns the exact finite regret
sum without a caller-supplied horizon action equality. No
`StandardBorelSpace Omega`, full law, independence, or stronger action premise
is introduced.

The downstream history-score source leaf now closes that finite-history score
mapping. The remaining direct LML blocker is symbol-level compatibility:
instantiate the actual `measurableArgmax` and `IsAlgEnvSeq` source fields. LML
remains card-only until that source/toolchain wrapper compiles.

## Native Real History-Score Source Exact ETC Regret

`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealHistoryScore`. It mirrors inclusive finite-
history pull counts, reward sums, and empirical means, proves they equal the
trace quantities at `n+1`, and identifies the `K*m-1` history score with
`realEmpMeanAtExploration` under the round-robin exploration action law.

Its strongest endpoint accepts a source-shaped finite-history least-encoded
commit law and returns the same exact native Real finite regret sum. The proof
intersects all finite exploration action equalities a.e., rewrites the score
vector, and reuses the prior action/source endpoint. It adds no standard-Borel,
full trajectory-law, independence, local-score commit, or preassembled action-
equality assumption. Focused and external canary builds pass.

The remaining direct-port boundary is no longer mathematical score mapping.
The downstream local field compatibility layer now compiles; only a true
cross-toolchain import of the concrete LML symbols remains.

## Native Real LML Field Compatibility Exact ETC Regret

`ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` now compiles in
`BanditRLProof.Algorithms.ETCRealLMLCompat`. The proposition
`ETC.RealStationaryETCSequence` records exactly the measurable action/reward,
round-robin exploration, finite-history least-encoded commit, persistence, and
stationary selected-feedback laws consumed from the pinned source.

`ETC.regret_le_of_realStationaryETCSequence` projects those fields into the
history-score theorem and returns the exact finite-arm LML-shaped sum. It adds
no standard-Borel sample-space, full-law, independence, local-score, or
preassembled action-equality premise. Focused and external canary builds pass.

This is a local compatibility theorem, not an imported LML declaration. The
toolchain audit found ABRL on Lean/mathlib `v4.29.1`, while pinned LML commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74` uses Lean `v4.32.0-rc1` and
mathlib commit `9ca31d8b72cf8c317e49c301bfdbfbe91fc49136`. The only remaining direct
boundary is a repository-level toolchain/dependency decision and proof over the
actual upstream symbols.

## Native Real UCB History Index

`UCB-NATIVE-REAL-HISTORY-INDEX` now compiles in
`BanditRLProof.Algorithms.UCBRealHistoryIndex`. It replaces the placeholder or
deterministic-proxy score boundary with the pinned-source quantities:
`sumRewards/pullCount` and
`sqrt(2*c*log(n+1)/pullCount)` on each realized trace.

Inclusive finite-pair-history mean, width, score, and least-encoded selector
are proved equal to their trace versions at time `n+1`. The Real index action
is score-maximal and measurable from timewise measurable action/reward
coordinates. No probability law, MGF, filtration, independence, or positive
pull-count premise is hidden in this leaf; division is the totalized Real
operation used by the source before initialization behavior supplies positive
counts.

The pinned LML audit shows the next missing theorem is not another generic
confidence-radius wrapper. Its one-sided UCB tail proof first invokes
`prob_pullCount_prod_sumRewards_mem_le`; generic fixed-count peeling,
complete-stream law transport, and next-unused-coordinate reward consumption
now compile in the following leaves. The remaining source boundary is the
recursive UCB action on that stream space and its stationary/product measure
law before specializing one-sided tails and expected pulls.

## UCB Fixed-Count Peeling And Law Transport

`UCB-FIXED-COUNT-PEELING-LAW` now compiles in
`BanditRLProof.Algorithms.UCBFixedCountPeeling`. The module defines a latent
`Nat -> Fin K -> Real` arm stream, measurable fixed-prefix sums, and a
`FixedArmPrefixSource` whose key field is the pathwise equality
`sumRewards = armPrefixSum pullCount`. From that equality and
`pullCount_le_time`, the adaptive pair event is contained in the finite union
of fixed-count prefix events. The local Mathlib-backed outer-measure union
bound then gives the finite sum.

A second theorem assumes one `IdentDistrib` law for the complete latent stream
and obtains every fixed-count law by measurable composition with
`armPrefixSum`. This exactly isolates the mathematical role of pinned LML
`identDistrib_sum_range_snd` plus
`prob_pullCount_prod_sumRewards_mem_le`, without importing the incompatible LML
toolchain or hiding the law inside a concentration hypothesis.

The regularity contract is measurable source/canonical spaces and stream
coordinates, measurable pair event, and a decidable projected-count filter.
No probability measure, independence, MGF, filtration, or positive count is
needed for the compiled theorem. Its pathwise source premise is now discharged
by `UCB-ARM-STREAM-REWARD-SOURCE`; the process/product and index-tail
instantiations are recorded separately below.

## UCB Arm-Stream Reward Source

`UCB-ARM-STREAM-REWARD-SOURCE` now compiles in
`BanditRLProof.Algorithms.UCBArmStreamSource`. `rewardFromArmStream` reads the
selected arm's next unused latent coordinate. Induction on the horizon proves
that selected `sumRewards` is exactly `armPrefixSum` at the realized
`pullCount`, and the module packages this theorem into general measurable and
canonical `FixedArmPrefixSource` adapters plus direct peeling consumers.

The only regularity in the general adapter is measurable stream coordinates;
the canonical Pi stream space discharges that automatically. No action
measurability, probability measure, stationarity, independence, MGF,
filtration, or positive count is assumed. Retrieval evidence is pinned LML
`ArrayProbSpace.reward_eq` and `SumRewards.sumRewards_eq`, together with local
count/sum recurrences and the compiled peeling interface.

`UCB-ARM-STREAM-PROCESS-LAW` now compiles the recursive inclusive history,
round-robin/native-index action, next-unused reward trace, exact actual-history
invariant, measurable history/action/reward coordinates, canonical
double-product arm-stream measure, and actual-process peeling endpoint.
`UCB-ARM-STREAM-INDEX-TAIL` compiles the product coordinate laws, independent
centered MGF transport, positive adaptive-count peeling, actual random-width
event algebra, logarithmic finite-sum collapse, and both LML-shaped bounds
`1 / (n+1)^(c-1)`.

`UCB-ARM-STREAM-EXPECTED-PULLCOUNT` now compiles the deterministic threshold,
selected-large failure union, `2*constSum` summation, ENNReal lower-integral
bound, pull-count integrability, and the Real Bochner expected-count endpoint
`8*c*sigma2*log(n+1)/gap^2 + 2 + 2*(constSum c n).toReal`.

`UCB-ARM-STREAM-LML-REGRET` then rewrites expected `realKernelRegret` as the
finite gap-weighted sum of expected pulls, removes zero-gap arms, and compiles
the exact pinned LML RHS
`sum a, 8*c*sigma2*log(n+1)/gap a + gap a*(2+2*constSum.toReal)`.
Its regularity contract is `0<K`, `0<c`, nonzero common NNReal proxy, a Markov
Real arm kernel, and centered sub-Gaussian MGF witnesses for every arm. The
canonical mathematical route is closed. Literal upstream `IsAlgEnvSeq` symbol
import remains separate cross-toolchain work and is not claimed by this
canonical theorem.

`UCB-EXTERNAL-ACTION-LAW-LML-REGRET` now closes the generic external-process
adapter when the complete external action trace is `IdentDistrib` to the
canonical arm-stream UCB action. The compiled proof makes the canonical trace
and finite-horizon regret functional measurable, composes the law witness via
`IdentDistrib.comp`, transports the Bochner integral with
`IdentDistrib.integral_eq`, and reuses the exact theorem above. Its only new
contract is the complete action-trace law identity; it adds no external
probability-measure, separate integrability, reward-process, filtration, or
standard-Borel premise. At this layer, the remaining compatibility input is a
construction of that action-law witness or literal import on a compatible
toolchain.

`UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET` is a compiled optional stronger
adapter.
Given a latent `ArmRewardStream` with complete law `IdentDistrib` to the
identity stream under `armStreamMeasure`, and a.e. equality of the external
action with recursive `armStreamAction` on that latent stream, the compiled
constructor derives the required complete action law and its consumer returns
the exact regret RHS. It uses `IdentDistrib.comp/of_ae_eq/trans` and derives
action a.e. measurability rather than assuming it separately. Pinned LML does
not require this external latent array law.

The source audit at commit `19dc3ab...` shows the faithful route is
`IsAlgEnvSeq.identDistrib_trajectory` against
`ArrayModel.isAlgEnvSeq_arrayMeasure`: transport the complete observable
action/reward pair trajectory, then project to actions. The compiled
`UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET` leaf now performs this
measurable Pi/`Prod.fst` projection and returns the exact regret RHS.
`UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now also compiles the missing
trajectory-uniqueness layer: common initial pair marginal and successor pair
`condDistrib` kernels determine both complete laws via finite-prefix transport
and Mathlib projective-limit uniqueness, then yield the exact regret RHS. The
canonical specialization now chooses the canonical initial pushforward and
regular conditional kernels internally, so callers only prove external-vs-
canonical initial and successor pair-law equalities. The remaining source gap
is deriving those equalities from actual upstream environment/action fields or
literal import, not trajectory uniqueness, canonical law-bundle construction,
or reconstruction of independent unused-arm arrays.
## UCB IsAlgEnvSeq Split-Law Leaf

The local UCB route now compiles from the four pinned `IsAlgEnvSeq`-shaped law
surfaces rather than a preassembled observable pair law. Initial and successor
action/feedback laws are composed with Mathlib `compProd`; complete trajectory
uniqueness and the exact regret sum then follow. This closes local split-to-
joint law assembly. Literal LML symbols remain unimported, and the next honest
gap is proving those four fields from a concrete upstream sequence under a
compatible toolchain.

## Thompson Recursive Finite-History Density Leaf

`Thompson.finitePairHistory_map_eq_withDensity` now compiles in
`ThompsonAlgorithmDensityProcess`. From LML-shaped initial and successor
action/feedback conditional laws plus pointwise action-law absolute
continuity, it proves the actual inclusive finite pair-history law is the
reference law weighted by the recursive initial/policy RN density. The proof
uses Mathlib `condDistrib`, `compProd`, kernel RN derivatives, and
`withDensity`; it no longer assumes RN densities are pointwise finite.

This closes the local counterpart of pinned LML
`IsAlgEnvSeq.hasLaw_history_withDensity`. The downstream conditional-process
source now applies it under `condDistrib id env mu`, derives the Bayes
conditional-history density law, and closes finite-prefix Thompson probability
matching. `ConditionalHistoryAlgorithmDensitySplitSource` now constructs that
source from the four initial/successor action/feedback law families by gathering
the time-indexed fields with `ae_all_iff` and applying the local split-law
assembler. The next honest gap is one concrete recursive TS/reference
trajectory producer for those four fields. Global sampler coupling, regret
decomposition, concentration, and final Thompson regret remain open.

## UCB Local Field Compatibility Theorem

`UCB.RealStationaryUCBSequence` and
`UCB.regret_le_of_realStationaryUCBSequence` now compile. This is the faithful
local theorem-level endpoint: the pinned measurability and split law fields are
bundled, the canonical process supplies a witness, and arbitrary bundle
instances inherit the exact finite-arm UCB bound. The route is not an imported
LML proof. The remaining gap is exclusively a concrete producer using actual
upstream symbols or a common-toolchain import.

## Thompson Stationary Empirical-Mean Tail Transport

`TS-STATIONARY-EMPIRICAL-MEAN-TAIL-TRANSPORT` is now compiled in
`ThompsonStationaryReward`. The route removes the zero-pull fiber, integrates
the fixed-environment adaptive-count tails through the augmented prior with
Mathlib `Measure.compProd_apply`, specializes to the clipped-UCB square-root
radius, evaluates the finite exponential count sum, and transports the result
through `MeasurableEquiv.prodAssoc.symm` onto the left-associated canonical
trajectory measure used by `TS-DECOMP`.

For every fixed arm and horizon, both lower- and upper-confidence failure
events are bounded by `(n : ENNReal) * ENNReal.ofReal delta`. The contract is a
probability prior, Standard Borel environment, finite nonempty arms, a Markov
stationary reward kernel, measurable mean, pointwise centered
`HasSubgaussianMGF`, nonzero variance proxy, and `0 < delta <= 1`. This closes
prior mixing and decomposition-shape transport. It does not close finite
arm/time unions, either clipped-score expectation, or final Bayesian regret;
those failures belong to `TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS`.

## Thompson Selected-Arm Horizon Lower Tail

`TS-STATIONARY-SELECTED-ARM-HORIZON-LOWER-TAIL` is now compiled. Its canonical
endpoint accepts a measurable `selectedArm : Env -> Fin K` and bounds the event
that some `t < n` has positive selected-arm count and lower-confidence failure
by `((n - 1 : Nat) : ENNReal) * ENNReal.ofReal delta`.

The proof rewrites actual trajectory rewards to the latent arm stream a.e.,
maps each bad time to its realized pull count, and unions only the prefix events
for `k in Finset.Icc 1 (n - 1)`. This preserves the pinned LML constant; unioning
the existing fixed-time `t * delta` bounds would not. Selected-arm measurability,
prior mixing, and product-associativity transport are discharged locally. Its
best-action expectation consumer now compiles; the next leaf is the
selected-action clipped-UCB-minus-mean expectation bound.

## Thompson Best-Action Clipped-UCB Expectation

`TS-CLIPPED-UCB-BEST-ACTION-EXPECTATION` is now compiled. On the stationary
canonical augmented trajectory measure, the integral of
`sum_{t<n} (mean(env,bestAction env) - clippedUCB(bestAction env,t))` is at most
`(u - l) * (n - 1) * n * delta`, matching the first concentration expectation
in pinned LML `BayesRegretTS`.

The proof splits over the compiled selected-arm horizon event. Its complement
makes every summand nonpositive; on the event, the mean and clipped score range
contracts bound every summand by `u-l`. The ENNReal event bound is converted to
`Measure.real` without weakening constants. The remaining concentration gap is
the selected-action clipped-UCB-minus-mean expectation, which needs a finite-arm
horizon upper event and the deterministic clipped-score sum inequality.

## Thompson Selected-Action Expectation And Final Bound

`TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS` and the stationary `TS-FINAL` route
are now compiled. `finset_sum_comp_pullCount` reindexes selected-time sums by
arm and realized pull number; `sum_clippedUCB_action_sub_mean_le` gives the
pathwise square-root bound. The all-arm horizon upper event is count-collapsed
before the arm union, so its cost is exactly `K * (n-1) * delta`. Splitting the
canonical integral yields the pinned second expectation bound.

The general-`delta` theorem then joins both expectations through the compiled
recursive Thompson decomposition. Specializing `delta = 1/n^2` proves
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)` in
`stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le`.
Contracts are a probability prior, Standard Borel nonempty environment, finite
nonempty arms, a stationary Markov reward kernel, measurable bounded means and
best action, pointwise centered `HasSubgaussianMGF`, and nonzero `sigma2`.
This is a compiled local stationary theorem, not a literal LML import or a
nonstationary/contextual/RL result; broader routes require explicit adapters.

## EXP3 Conditional Moment Transport

`EXP3-CONDITIONAL-MOMENT-TRANSPORT` now compiles in
`BanditRLProof.Exp3ConditionalMoments`. It packages a normalized nonnegative
finite action vector as a finite Dirac probability measure and proves that an
actual history-adaptive `condDistrib` law transports measurable integrable
history/action scores to finite conditional weighted sums. The specialized
consumers give armwise importance-weighted unbiasedness and exact mixed-loss
and mixed-square Bochner-integral identities.

The proof is Mathlib-backed through
`condDistrib_ae_eq_iff_measure_eq_compProd`, `integral_map`,
`Measure.integral_compProd`, and finite Dirac integral rules, then reuses the
compiled deterministic EXP3 moment identities. Its explicit contracts include
finite ambient measure, Standard Borel action regularity, a Markov policy equal
a.e. to the finite action law, the actual conditional distribution equality,
strictly positive supported probabilities, and score measurability/integrability.
Because the ambient measure is only finite, the equalities are unnormalized
integral identities unless a probability-measure instance is supplied.
The downstream generated-process leaf now supplies the policy and conditional
law premises; score regularity and finite-horizon moment assembly now compile
downstream. The integrated expected-regret and large-horizon tuned square-root
consumers, realized selected-loss expectation adapter, and uniform-horizon
clipped-rate theorem also compile on this EXP3 route.

## EXP3 Generated Action Process

`EXP3-GENERATED-ACTION-PROCESS` now compiles in
`BanditRLProof.Exp3ActionProcess`. A measurable family of normalized finite
probability vectors is converted into a finite-Dirac Markov kernel. Composing a
finite history measure with that kernel produces a canonical joint
history/action measure whose first marginal is the supplied history law and
whose sampled action `condDistrib` is a.e. the generated policy. The joint
measure is finite for a finite history measure and is a probability measure
when the history measure is a probability measure.

The proof establishes kernel measurability from finite sums of measurable
coordinate probabilities, obtains Markovness from the pointwise distribution
contract, and uses Mathlib `condDistrib_ae_eq_iff_measure_eq_compProd` for the
law identification. Canonical armwise, mixed-loss, and mixed-square wrappers
then consume `EXP3-CONDITIONAL-MOMENT-TRANSPORT` without external policy or law
assumptions. The downstream score-regularity leaf now also removes the explicit
score measurability and integrability premises. Recursive finite-horizon
trajectory generation, expectation assembly, the unoptimized expected-regret
endpoint, its large-horizon tuned square-root consumer, realized selected-loss
transport, and uniform-horizon clipped-rate theorem now compile downstream.

## EXP3 Score Regularity

`EXP3-SCORE-REGULARITY` now compiles in
`BanditRLProof.Exp3ScoreRegularity`. Its
`BoundedMeasurableLossWithProbabilityFloor` contract records `epsilon > 0`,
`epsilon <= prob(history, action)` on the finite support, measurable supported
loss coordinates, and supported losses in `[0,1]`. The module proves
measurability of the armwise importance-weighted score and both mixed scores,
with pointwise norm bounds `1/epsilon`, `1/epsilon`, and `(1/epsilon)^2`.

`Integrable.of_bound` turns those bounds into generated `compProd`-law
integrability. Three final wrappers feed the resulting positivity,
measurability, and integrability witnesses into `Exp3ActionProcess`, so callers
no longer supply `hprob`, `hscore`, or `hIntegrable`. Root import and external
integrability/premise-free mixed-square canaries compile. This remains a
one-round regularity result, but its downstream score-driven recursive
trajectory and its concrete sampled importance-weighted score instantiation now
compile. The generated scalar-feedback law transport, finite-horizon moments,
integrated expected-regret endpoint, large-horizon tuned square-root consumer,
realized selected-loss transport, and uniform-horizon clipped-rate theorem now
compile downstream.

## EXP3 Exploration-Mixed Recursive Trajectory

`EXP3-EXPLORATION-MIXED-RECURSIVE-TRAJECTORY` now compiles in
`BanditRLProof.Exp3RecursiveTrajectory`. For any measurable cumulative score on
inclusive finite action/loss histories, it defines positive exponential
weights, normalizes them over a nonempty finite arm set, and mixes the result
with the uniform distribution. The resulting probability coordinates are
nonnegative, sum to one, are measurable in finite history, and have the
pointwise floor `gamma / arms.card` when `0 <= gamma <= 1`; `gamma > 0` makes
that floor strictly positive.

The module packages these laws as `MeasurableFiniteActionDistribution`, builds
an exploration-mixed `Thompson.HistoryAlgorithm`, and uses the existing
Mathlib-backed Ionescu-Tulcea trajectory layer to construct the complete
environment-indexed action/loss process. Its endpoint theorem identifies every
successor action's `condDistrib` given the finite trajectory prefix with the
explicit finite action kernel. Root import and external score, floor, kernel,
and full conditional-law canaries compile.

Regularity is explicit: nonempty finite support; measurable action, loss, and
environment spaces with measurable action singletons; measurable supported
score coordinates; `0 <= gamma <= 1`; nonempty action/loss targets for
trajectory construction; Standard Borel environment/action/loss spaces and a
finite prior for the conditional-law endpoint. Its downstream sampled-score
module now closes the arbitrary-score boundary, and its predictable-moment
consumer now compiles finite-horizon integral sums. The integrated expected
EXP3 regret endpoint and large-horizon eta/gamma square-root optimization also
compile downstream; the realized selected-loss transport and uniform-horizon
clipped-rate theorem compile as well.

## EXP3 Sampled History Score Recursive Trajectory

`EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY` now compiles in
`BanditRLProof.Exp3SampledHistoryScore`. The Real-valued inclusive pair history
is restricted measurably to its previous prefix. At time zero the score uses
the initial action law; at each successor it adds the newly observed scalar
loss divided by the exploration-mixed probability generated from the prior
score and prefix. `sampledHistoryScore_zero` and
`sampledHistoryScore_succ` expose these exact equations.

Structural induction proves every supported score coordinate measurable, so
the generic trajectory layer can be instantiated without an external
`score/hscore`. The module exposes the concrete probability floor, stochastic
history algorithm, complete environment-indexed trajectory kernel, Markov
instance, and `sampledImportanceWeightedTrajectoryMeasure_condDistrib_action`,
which identifies every successor action law with the finite action kernel
computed from the recursively accumulated sampled score. Root import and
external recursive-equation and full conditional-law canaries compile.

Regularity contracts are Real-valued observed feedback; measurable action
singletons and decidable action equality; nonempty finite arms; `0 <= gamma <=
1`, with `gamma > 0` for strict downstream positivity; a measurable history
environment; Standard Borel environment/action; and a finite prior. Eta
positivity and `[0,1]` loss bounds are deliberately absent from process
construction and remain downstream regret contracts. Failure policy: this
sampled-score module alone returns only a sampled scalar; the downstream
predictable-adversary module now closes that law boundary.

## EXP3 Predictable Adversary

`EXP3-PREDICTABLE-ADVERSARY` now compiles in
`BanditRLProof.Exp3PredictableAdversary`. `Exp3.PredictableLossVector` records
jointly measurable initial and finite-history successor loss vectors selected
before the current action, together with pointwise `[0,1]` bounds. Its
`environment` uses `Kernel.deterministic`; the initial and successor feedback
apply theorems reduce exactly to Dirac measures at the chosen coordinates.

`trajectoryMixture_condDistrib_action_given_environment_history` lifts a
common fixed-environment history/action law through a finite prior while
retaining the environment in the conditioning variable. The concrete theorem
`sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment`
therefore identifies the sampled EXP3 action law given `(Env,prefix)` with the
same exploration-mixed policy, comapped along the prefix projection. The route
uses measurable event sections, `Measure.ext_prod`, Tonelli through
`Measure.lintegral_compProd`, and the canonical fixed-environment trajectory
law. Root import, module/root builds, external declaration and Dirac canaries,
and `Tests.Basic` compile. Regularity is pre-action joint measurability,
pointwise `[0,1]`, measurable action singletons and decidable equality,
nonempty finite arms, `0 <= gamma <= 1`, Standard Borel environment/action,
and a finite prior. Failure policy: the next leaf must combine these two law
surfaces with the existing one-round estimator identities and prove the needed
roundwise measurability/integrability; no expected-regret claim is available.

### EXP3 predictable observed moments

`EXP3-PREDICTABLE-OBSERVED-MOMENTS` now compiles in
`BanditRLProof.Exp3PredictableMoments`. The module transports the canonical
prefix/next-pair law through an environment prior, identifies initial and
successor reward coordinates with selected predictable losses almost surely,
packages the `(Env,prefix)` sampled policy and its positive `gamma / |arms|`
floor, and proves observed-scalar armwise first-moment unbiasedness together
with the exact probability-mixed estimator-square moment. It reuses
`Exp3ConditionalMoments`; no integrability premise remains at the public
endpoint. Contracts are predictable jointly measurable `[0,1]` losses,
nonempty finite arms, `0 < gamma <= 1`, measurable action singletons,
decidable equality, Standard Borel environment/action, a finite prior, and a
supported comparator. Its downstream finite-horizon consumer now compiles;
these remain moment identities rather than a potential inequality, optimized
bound, or regret theorem.

### EXP3 predictable finite-horizon moments

`EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS` now compiles in
`BanditRLProof.Exp3PredictableMoments`. It exposes uniform actual-time
probability and predictable-loss surfaces, including `t = 0`, proves observed
and latent score integrability under the finite prior mixture, transports the
initial and successor moment identities to the common full trajectory law, and
uses `ExpectationBochnerSums.integral_finset_sum` to sum both identities over
`t < horizon`; this includes `t = 0` when `0 < horizon`. Contracts remain jointly measurable predictable
`[0,1]` losses, nonempty finite arms, `0 < gamma <= 1`, measurable singleton
actions with decidable equality, Standard Borel environment/action, finite
prior, and supported comparator; no positivity assumption on `eta` is used.
Failure policy: this is not the pathwise sampled-score/Hedge inequality,
exploration-bias estimate, optimized parameter choice, or final EXP3 regret.

## EXP3 Sampled-Score/Hedge Join

`EXP3-SAMPLED-HEDGE` now compiles in `BanditRLProof.Exp3SampledHedge`.
The concrete actual-time observed estimator is packaged as
`sampledTrajectoryObservedLoss`. Structural induction proves that the
inclusive `sampledHistoryScore` through `n` is exactly Hedge
`cumulativeLoss` at `n + 1`. The successor Hedge distribution is then
identified with `normalizedHistoryDistribution` of that score, and the
actual trajectory probability is rewritten as its explicit
`(1 - gamma) q + gamma / |arms|` exploration mixture.

The endpoint `sampledHistoryScore_hedge_regret_le` is a concrete pathwise
finite-horizon second-order Hedge inequality with the comparator cumulative
term exposed as the sampled score. Contracts are nonempty finite arms,
decidable equality, `eta > 0`, `0 <= gamma <= 1`, comparator membership, and
nonnegative observed scalar losses on the finite prefix. No measurable-space,
prior, integrability, or probability-law premise is needed. Retrieval is
`LOCAL-LEAF-EXP3-HEDGE-DETERMINISTIC-REGRET`,
`LOCAL-LEAF-EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY`,
`LOCAL-LEAF-EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS`, Mathlib finite sums and
order/exponential algebra, the EXP3 paper/textbook cards, and the
inspiration-only weapon card. Root import and a full external theorem canary
compile. Its finite-horizon a.e. predictable reward support,
pure-vs-explored distribution bias, integration, expected-regret, tuned
square-root, realized selected-loss, and uniform-horizon consumers now compile
downstream. Failure policy: this leaf alone remains pathwise and must not be
reported as an expected-regret theorem.

## EXP3 Predictable Hedge Almost-Sure Endpoint

`EXP3-PREDICTABLE-HEDGE-AE` now compiles in
`BanditRLProof.Exp3PredictableHedge`. The module rewrites the observed reward at
time zero and every successor to the selected coordinate of the predictable
`[0,1]` loss vector, derives reward nonnegativity almost surely, and uses
`ae_all_iff` to place all `t < horizon` facts on one common full-trajectory
event. On that event the compiled pathwise sampled-Hedge theorem applies
without an external `hreward_nonneg` premise.

Public endpoints are
`sampledPredictableTrajectoryMeasure_hedge_regret_le_ae` for any horizon and
`sampledPredictableScoreHedge_ae` with the comparator cumulative estimator
exposed as `sampledHistoryScore`. Contracts are predictable jointly measurable
`[0,1]` losses, nonempty finite arms, measurable-singleton decidable actions,
Standard Borel environment/action, a finite prior, `eta > 0`,
`0 <= gamma <= 1`, and comparator membership. Gamma positivity, probability
normalization of the prior, and integrability are not needed for this a.e.
endpoint. Retrieval uses the sampled-Hedge, predictable-observed-moment, and
finite-horizon-moment local cards, Mathlib measure/kernel/finite-sum APIs, and
the EXP3 paper/textbook route; the weapon card remains inspiration only.
Failure policy: this is not an integrated regret theorem. Next prove the
pure-Hedge `q` versus explored `p` bias and second-moment inequalities plus
integrability, then integrate before optimizing eta/gamma.

## EXP3 Exploration Bias

`EXP3-EXPLORATION-BIAS` now compiles in
`BanditRLProof.Exp3ExplorationBias`. The module unfolds the concrete sampling
mixture `p_t = (1-gamma)q_t + gamma/|arms|`, proves
`q_t(a) <= p_t(a)/(1-gamma)`, and uses it to compare the pure-Hedge estimator
square with the actual probability-mixed estimator square. A separate
`[0,1]` argument bounds actual predictable loss by pure loss plus `gamma`.
`sampledTrajectory_finiteHorizon_explorationBias_secondMoment` sums both
inequalities over an arbitrary `Finset.range horizon`.

Contracts are a nonempty finite arm set, decidable equality, measurable spaces
needed by `PredictableLossVector`, and `0 <= gamma < 1`; eta positivity, a
prior, Standard Borel structure, probability normalization, integrability,
and a comparator are not used. Retrieval uses the predictable-Hedge,
sampled-Hedge, finite-horizon-moment, and importance-weighted local cards plus
Mathlib finite-sum/order algebra and the EXP3 paper/textbook route; the weapon
card is inspiration only. Status is compiled with root import and a full
external finite-horizon canary. Failure policy: this remains pathwise algebra,
not expected regret by itself. Its adaptive pure-q transport, integrability,
and expected-regret consumer now compile; its tuned square-root consumer also compiles.

## EXP3 Predictable Expected Regret

`EXP3-PREDICTABLE-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3PredictableIntegration`. Its public endpoint
`sampledPredictable_expectedRegret_le` bounds the expected finite-horizon
exploration-mixed predictable loss minus any supported comparator by
`log |arms| / eta + eta/(1-gamma) * |arms| * horizon + gamma * horizon` on the
actual generated trajectory law.

The Lean-facing route adds a cross-weight estimator with sampling weights `p`
and predictable Hedge weights `q`, proves the finite-sum identity
`E_p[q dot hat-loss] = q dot loss`, transports it through the identified
conditional action law, constructs measurable pure-Hedge sources at every
time, aggregates their first moments, integrates the a.e. Hedge inequality,
and applies the exploration-bias and exact second-moment bounds. Imports and
local APIs are `Exp3ExplorationBias`, `normalizedHistoryDistributionSource`,
the conditional-moment transport, generated reward a.e. identification,
`IntegrabilitySums.integrable_finset_sum`, and
`ExpectationBochnerSums.integral_finset_sum`.

Contracts are a probability prior, Standard Borel environment and action,
measurable action singletons, decidable equality, nonempty finite arms,
jointly measurable predictable `[0,1]` losses, a supported comparator,
`eta > 0`, and `0 < gamma < 1`. There is no independence, stationarity,
oblivious-adversary, concentration, or supplied-integrability assumption.
Retrieval evidence is the compiled exploration-bias, predictable-Hedge,
finite-horizon-moment, conditional-moment, and score-regularity local cards;
Mathlib measure/kernel/finite-sum/order APIs; the EXP3 paper and textbook
cards; and the inspiration-only weapon card. Status is `leanCompiled`, root
imported, with a full external theorem canary. Failure policy: this is a real
expected predictable-regret theorem, but not the optimized classical EXP3
corollary by itself; its tuned square-root consumer now compiles downstream.
Its left side is the `p_t`-mixed predictable loss; the separate realized
selected-loss expectation consumer and all-horizon clipped-rate consumer now
compile. Preserve this reusable p-mixed endpoint when extending to broader
adversary or high-probability routes.

## EXP3 Tuned Expected Regret

`EXP3-TUNED-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3ExpectedRegret`. The deterministic theorem
`expectedRegretBudget_le_four_mul_gamma_mul_horizon` reduces the unoptimized
budget to `4*gamma*T` under `eta=gamma/K`, `gamma<=1/2`, and
`K*log K<=gamma^2*T`. The final generated-trajectory theorem
`sampledPredictable_expectedRegret_le_four_mul_sqrt` instantiates
`gamma=sqrt(K*log K/T)` and `eta=gamma/K`, yielding
`4*sqrt(K*T*log K)`.

Local APIs/imports are `Exp3PredictableIntegration`, the compiled unoptimized
endpoint, `Real.sqrt_pos`, `Real.sqrt_le_iff`, `Real.sq_sqrt`,
`Real.sqrt_div'`, field simplification, ring normalization, and Nat/Real cast
transport. The proof is deterministic after the expectation theorem: bound
the log term by `gamma*T`, use `gamma<=1/2` for the second-order denominator,
then normalize the square-root expression.

Contracts retain the prior probability, Standard Borel, predictable `[0,1]`,
finite-arm, and supported-comparator assumptions, and add `2<=K`, `0<T`, and
the large-horizon regime `4*K*log K<=T`. There are no new law, independence,
stationarity, concentration, or integrability assumptions. Retrieval evidence
is `LOCAL-LEAF-EXP3-PREDICTABLE-EXPECTED-REGRET`, `MLIB-REAL-LOG-SQRT`,
Mathlib order/measure APIs, EXP3 paper/textbook cards, and the inspiration-only
weapon card. Status is `leanCompiled`, root imported, with a full external
canary. Its realized selected-loss and uniform-horizon consumers now compile.
Failure policy: this theorem remains the square-root branch under the stated
large-horizon regime; arbitrary horizons use the separate clipped-rate theorem.

## EXP3 Realized Expected Regret

`EXP3-REALIZED-EXPECTED-REGRET` now compiles in
`BanditRLProof.Exp3RealizedRegret`. The generated scalar reward is identified
almost surely with the predictable coordinate at the sampled action. The
existing initial and successor action `condDistrib` laws are then consumed by
`integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure`
to prove, at every actual time,
`E[realizedLoss_t] = E[sum_a p_t(a) * loss_t(a)]`. Mathlib-backed finite-sum
Bochner integration lifts this equality to arbitrary finite horizons.

The unoptimized theorem
`sampledPredictable_realizedExpectedRegret_le` therefore has the same
`log(K)/eta + eta*K*T/(1-gamma) + gamma*T` bound as the compiled mixed-loss
endpoint. The tuned theorem
`sampledPredictable_realizedExpectedRegret_le_four_mul_sqrt` gives
`4*sqrt(K*T*log K)` for the actual generated scalar losses under `2<=K`,
`0<T`, and `4*K*log K<=T`.

Local APIs/imports are `Exp3ExpectedRegret`, the generated reward a.e. laws,
initial/successor action conditional laws, finite-action conditional integral
transport, `Measure.integral_map`, `ExpectationBochnerSums.integral_finset_sum`,
`IntegrabilitySums.integrable_finset_sum`, and `integral_sub`. Contracts are the
existing finite/probability prior, Standard Borel, measurable-singleton,
finite-arm, predictable `[0,1]`, rate, and comparator assumptions. No
independence, stationarity, obliviousness, concentration, or new integrability
premise is introduced. Retrieval is recorded by
`LOCAL-LEAF-EXP3-REALIZED-EXPECTED-REGRET` plus the predictable/tuned,
conditional-moment, adversary, Mathlib measure/kernel/finite-sum, and EXP3
paper/textbook cards; the weapon card remains inspiration-only. Status is
`leanCompiled`, root imported, with declaration canaries and a full external
tuned theorem canary. Failure policy: this transport remains reusable for legal
rates; the all-horizon clipped-rate consumer now compiles, while high-probability
and broader adversary models remain separate.

## EXP3 Uniform-Horizon Realized Regret

`EXP3-UNIFORM-HORIZON-REALIZED-REGRET` now compiles in
`BanditRLProof.Exp3UniformRegret`. The support theorem
`sampledPredictable_realizedExpectedRegret_le_horizon` bounds expected realized
regret by `T` for arbitrary legal `eta` and `0 <= gamma <= 1`. The public endpoint
`sampledPredictable_clippedRealizedExpectedRegret_le_min` defines
`gamma = min(1/2, sqrt(K*log K/T))`, `eta = gamma/K`, and proves
`E[R_T] <= min(T, 4*sqrt(K*T*log K))` for every natural horizon, including zero.

Local APIs/imports are `Exp3RealizedRegret`, the realized-to-explored
finite-horizon expectation equality, explored-loss unit-interval control,
finite-sum integrability, `integral_mono_ae`, `integral_sub`, `Real.log_pos`,
and `Real.sq_sqrt`. The proof route first derives the trivial horizon bound,
then splits on `4*K*log K <= T`: in the large branch the clipped rate equals
the tuned rate and the compiled square-root theorem applies; in the small branch
ordered-ring algebra proves `T <= 4*sqrt(K*T*log K)`, so the minimum is `T`.

Regularity contracts are a probability prior, Standard Borel Env/Action,
measurable action singletons, decidable nonempty finite arms with `2 <= K`, a
jointly measurable predictable `[0,1]` loss vector, and a supported comparator.
There is no positive-horizon, independence, stationarity, obliviousness,
concentration, or supplied-integrability premise. Retrieval uses the realized
and tuned local cards, Mathlib Real log/sqrt, measure/integral, finite-sum, and
order-algebra cards, EXP3 paper/textbook cards, and the weapon card only as
inspiration. Status is `leanCompiled`, root imported, with declaration canaries
and a full external theorem canary. Failure policy: this closes expected realized
regret for the generated predictable-adversary model at all horizons; it does
not claim high-probability regret, stochastic reward regret, arbitrary
non-predictable adversaries, or other EXP3 variants.

### Conditional-kernel measurable-state freeze leaf

`COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE` now compiles in
`BanditRLProof.ConditionalExpectationReward`. The kernel theorem states that
if `X` is measurable in `mcond`, then `(condExpKernel mu mcond).map X` is
`mu.trim hm`-a.e. the deterministic kernel at `X`; the companion theorem
rewrites each pushed-forward measure as `Measure.dirac (X omega)`.

The proof maps Mathlib's diagonal `compProd_trim_condExpKernel` identity through
`X`, identifies the deterministic composition-product, and applies
`Kernel.ae_eq_of_compProd_eq`. Its contracts are finite `mu`, Standard Borel
ambient `Omega`, `mcond <= mOmega`, a countably generated target, and
`Measurable[mcond] X`. In particular, it does not require a countable target,
so Real-valued finite prefixes are supported. Status is `leanCompiled` with two
external canaries. Failure policy: this freezes conditioning-measurable state
only; the generated successor action law and realized-deviation conditional MGF
now compile downstream, while initial-time alignment, Azuma aggregation, and a
high-probability EXP3 theorem remain open.

## EXP3 Successor Realized-Deviation Conditional MGF

`EXP3-REALIZED-DEVIATION-SUCC-COND-MGF` now compiles in
`BanditRLProof.Exp3RealizedConcentration`. The final Lean endpoint
`sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF` conditions the
joint `(Env, trajectory)` law on `(Env, finite pair prefix)` and proves a
Mathlib `HasCondSubgaussianMGF` witness with
`Concentration.intervalVarianceProxy 0 1` for realized loss minus the
exploration-mixed predictable loss at time `n + 1`.

The proof recovers the complete finite-support action measure from singleton
`condExpKernel` masses, freezes the predictable environment/history state,
and applies the bounded centered Hoeffding MGF theorem on `[0,1]`. The generated
feedback a.e. law then transports the selected predictable deviation to the
realized scalar deviation. Contracts are finite prior, Standard Borel and
nonempty Env/Action, measurable action singletons, decidable nonempty finite
arms, `0 <= gamma <= 1`, and predictable measurable `[0,1]` losses. No
`Countable Action`, independence, stationarity, probability prior, or supplied
exponential integrability is required. Status is `leanCompiled`, root imported,
with declaration checks and an external theorem canary. Failure policy: this
leaf closes successor one-step MGF only; initial-time alignment, strongly
adapted process assembly, finite-horizon Azuma, confidence events, and
high-probability EXP3 regret remain open. The initial-time and finite-sum items
are now discharged by the downstream leaf below.

## EXP3 Finite-Horizon Realized-Deviation Tail

`EXP3-REALIZED-DEVIATION-SUM-TAIL` now compiles in
`BanditRLProof.Exp3RealizedDeviationTail`. Its Lean endpoint
`sampledPredictableRealizedDeviation_sum_tail_ennreal` bounds the probability
of
`eps <= sum_{t<horizon} (realizedLoss_t - explorationMixedLoss_t)` by the
ENNReal lift of
`exp (-eps^2 / (2 * horizon * intervalVarianceProxy 0 1))`.

The route proves the missing time-zero conditional MGF from the initial-action
law, transports selected to realized loss, and defines the shifted filtration
`F 0 = sigma(Env)`, `F (i+1) = sigma(Env,prefix i)`. The shifted process has
`Y 0 = 0` and `Y (i+1)` equal to the actual time-`i` deviation; explicit
finite-prefix factorizations prove `StronglyAdapted`. The zero and successor
MGF branches then feed the Mathlib-backed ENNReal Azuma wrapper, and two local
sum lemmas remove the index shift. Contracts are a probability prior, Standard
Borel nonempty Env/Action, measurable action singletons, decidable nonempty
finite arms, predictable measurable `[0,1]` losses, legal gamma, and
`eps >= 0`. Failure policy: the realized concentration term is closed, but its
delta confidence-radius simplification now compiles downstream. A statement
audit shows that direct combination with the deterministic Hedge theorem is
not sufficient for true comparator regret because that theorem is expressed
through random importance-weighted estimators.

## EXP3 Realized-Deviation Delta Confidence

`EXP3-REALIZED-DEVIATION-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3RealizedConfidence`. The endpoint
`sampledPredictableRealizedDeviation_sum_tail_delta` states that, for positive
`horizon` and `delta`, the probability that cumulative realized loss minus
exploration-mixed predictable loss exceeds
`sqrt (2 * horizon * intervalVarianceProxy 0 1 * log (1 / delta))` is at most
`ENNReal.ofReal delta`.

The proof records strict positivity of the `[0,1]` Hoeffding proxy, derives the
square-root radius from an arbitrary exponential budget, applies the compiled
finite-horizon ENNReal tail, and simplifies `exp (-log (1/delta))` exactly.
Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty finite arms, predictable
measurable `[0,1]` losses, legal gamma, positive horizon, and positive delta.
No `delta <= 1` premise is needed for validity, although that is the informative
confidence regime. Failure policy: full high-probability EXP3 regret still
needs conditional concentration for comparator-estimator minus true comparator
loss and pure-`q` cross-weight estimator minus predictable pure-`q` loss, plus
random second-moment control or an EXP3.P-style estimator modification.

## EXP3 Comparator-Estimator Delta Confidence

`EXP3-COMPARATOR-ESTIMATOR-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3ComparatorConfidence`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_delta` bounds the event
that the fixed comparator's cumulative observed importance-weighted estimator
minus cumulative true predictable comparator loss exceeds
`sqrt(2 * horizon * intervalVarianceProxy 0 (1/(gamma/|arms|)) * log(1/delta))`.

The module proves a reusable finite-action conditional-MGF bridge, generated
time-zero/successor instances, observed-feedback a.e. transport, finite-prefix
strong adaptedness, an arbitrary-epsilon ENNReal tail, and the delta wrapper.
Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable nonempty arms, `0 < gamma <= 1`, predictable
measurable `[0,1]` losses, a supported comparator, and positive horizon/delta.
The comparator concentration obligation is closed. The pure-`q` cross-weight
obligation now compiles downstream; random estimator-square control or an
EXP3.P-style modification remains.

## EXP3 Pure Cross-Weight Delta Confidence

`EXP3-PURE-CROSS-WEIGHT-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3PureConfidence`. The endpoint
`sampledPurePredictableMinusObserved_sum_tail_delta` bounds cumulative
pure-Hedge predictable loss minus pure-Hedge observed cross-weight loss by the
delta radius with proxy `intervalVarianceProxy 0 (1/(gamma/|arms|))`. The
opposite observed-minus-predictable tail remains available as a helper.

The module proves the generic `p`-sampled/`q`-weighted conditional-MGF bridge,
generated zero/successor instances, observed-feedback transport, MGF negation
for the regret-required sign, finite-prefix strong adaptedness, the
arbitrary-epsilon ENNReal tail, and the sqrt/log delta wrapper. Contracts are a
probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable nonempty arms, `0 < gamma <= 1`, predictable
measurable `[0,1]` losses, and positive horizon/delta; no comparator or eta
positivity is needed. Pure-`q` cross-weight concentration is closed and its
generated predictable high-probability consumer now compiles downstream.

## EXP3 Predictable High-Probability Regret

`EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3HighProbabilityRegret`. The support theorem first proves
generated rewards lie in `[0,1]` almost surely and uses
`mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div` plus the exploration
floor to bound the random estimator-square sum by
`horizon / (gamma / |arms|)` almost surely.

The primary endpoint
`sampledPredictable_highProbabilityRegret_tail_total_delta` bounds the
probability that generated exploration-mixed predictable pseudo-regret exceeds
the Hedge term, deterministic reciprocal-floor second-moment term, exploration
bias, and the two confidence radii evaluated at `delta / 2`. Its total failure
probability is `ENNReal.ofReal delta`; the raw two-event endpoint
`sampledPredictable_highProbabilityRegret_tail_delta` remains available.
Contracts are a
probability prior, Standard Borel nonempty Env/Action, measurable singletons,
decidable nonempty arms, `eta>0`, `0<gamma<1`, predictable measurable `[0,1]`
losses, a supported comparator, and positive horizon/delta. This closes the
generated predictable high-probability route and is consumed by the realized
selected-loss theorem below. It is not an ideal-rate result; that still needs a
variance-sensitive/Freedman or EXP3.P route.

## EXP3 Realized High-Probability Regret

`EXP3-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RealizedHighProbabilityRegret`. Its primary endpoint
`sampledPredictable_realizedHighProbabilityRegret_tail_total_delta` controls
cumulative scalar loss stored in the generated trajectory minus a supported
comparator's true predictable cumulative loss. The budget is the predictable
high-probability budget plus the realized-minus-exploration confidence radius,
all evaluated at `delta / 3`, and the total failure probability is
`ENNReal.ofReal delta`.

The proof uses the pathwise decomposition `realized regret = predictable
regret + realized deviation`, contains the target event in the union of the
compiled predictable-regret and realized-deviation bad events, and applies
`measure_union_le`. Contracts are unchanged from the predictable theorem; no
independence, countability, extra integrability, or new law transport is added.
This closes generated realized selected-loss high-probability regret for the
current range-Hoeffding budget, not a tuned or ideal-rate EXP3 theorem.

## Fixed-Tilt Conditional MGF Sum Tail

`CONCENTRATION-FIXED-TILT-CONDITIONAL-MGF-SUM-TAIL` now compiles in
`BanditRLProof.ConcentrationFixedMGF`. The endpoint
`measure_sum_ge_le_of_hasCondMGFUpperBoundAt` gives
`mu.real {sum Y >= eps} <= exp (-tilt * eps + sum psi)` for a strongly adapted
finite process, from one time-zero MGF budget, successor conditional MGF
budgets, and `0 <= tilt`.

The source witnesses retain exponential integrability at every real multiple,
which is the contract needed by kernel `compProd` composition, but impose the
MGF upper bound only at the selected tilt. The route reuses Mathlib's kernel,
conditional-expectation, `MemLp`, filtration, and exponential Markov APIs.
Local Mathlib retrieval found no Freedman, Bernstein, sub-gamma, or predictable
quadratic variation tail theorem. This generic leaf is not a variance tail by
itself; its one-step fixed-comparator EXP3 consumer is now compiled in
`Exp3ComparatorBernstein`, as recorded below.

## EXP3 Fixed-Comparator Variance-Sensitive Tail

`EXP3-COMPARATOR-BERNSTEIN-FIXED-TILT` now compiles in
`BanditRLProof.Exp3ComparatorBernstein`. Its generated-trajectory endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_fixedTilt` proves
`mu.real {sum deviation >= threshold} <= exp (-tilt * threshold +
horizon * tilt^2 / (gamma / |arms|))` whenever
`0 <= tilt <= gamma / |arms|`.

The route uses Mathlib's `Real.abs_exp_sub_one_sub_id_le`, the exact finite-law
centered second moment `loss^2 / prob - loss^2`, its `1 / epsilon` bound, the
compiled `condDistrib`/`condExpKernel.map` bridge, generated zero/successor
action laws, observed/predictable a.e. transport, and the fixed-tilt adapted
sum theorem. Contracts are a probability prior, Standard Borel nonempty
environment/action spaces, measurable singletons, finite nonempty arms,
`0 < gamma <= 1`, predictable measurable `[0,1]` losses, and a supported
comparator. This closes one fixed-comparator arbitrary-tilt tail with linear
reciprocal-floor dependence. Its optimized delta consumer is compiled below;
the pure-cross analogue is also compiled below, while the finite-comparator
union and improved full EXP3 regret theorem remain open.

## EXP3 Fixed-Comparator Variance-Sensitive Delta Confidence

`EXP3-COMPARATOR-BERNSTEIN-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3ComparatorBernstein`. The endpoint
`sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta` uses
`epsilon = gamma / |arms|` and `budget = max (log (1 / delta)) 0`, and bounds
the ENNReal probability of exceeding
`2 * sqrt (horizon * budget / epsilon) + budget / epsilon` by
`ENNReal.ofReal delta`.

The scalar optimizer chooses `sqrt (epsilon * budget / horizon)` when
`budget <= epsilon * horizon`, and the boundary tilt `epsilon` otherwise.
The proof supports zero horizon and every `delta > 0`; it needs neither
`delta <= 1` nor an extra horizon-positivity contract. This closes the
one-comparator delta confidence route, not simultaneous comparator confidence,
the pure-cross route compiled below, a general Freedman theorem, or complete
improved EXP3 high-probability regret.

## EXP3 Pure-Cross Variance-Sensitive Delta Confidence

`EXP3-PURE-CROSS-BERNSTEIN-DELTA-CONFIDENCE` now compiles in
`BanditRLProof.Exp3PureBernstein`. The endpoint
`sampledPurePredictableMinusObserved_sum_tail_bernstein_delta` bounds the
generated event where cumulative pure-Hedge predictable loss minus observed
cross-weighted loss exceeds
`2 * sqrt (horizon * budget / epsilon) + budget / epsilon` by
`ENNReal.ofReal delta`, for `epsilon = gamma / |arms|` and
`budget = max (log (1 / delta)) 0`.

The finite-law source reduces the p-sampled/q-weighted estimator to
`q(chosen) * loss(chosen) / p(chosen)` and proves its centered second moment is
at most `1 / epsilon`. A direct positive-tilt proof handles the required
`mean - estimator` sign, then existing conditional-law transport,
observed-feedback equality, adaptedness, fixed-tilt summation, and scalar
optimization complete the route. Contracts permit zero horizon and every
`delta > 0`, with no comparator, eta positivity, independence, stationarity,
countability, or supplied integrability. The predictable two-event consumer
now compiles below; it deliberately retains the existing pathwise
`horizon / epsilon` Hedge-square bound.

## EXP3 Predictable Bernstein High-Probability Regret

`EXP3-PREDICTABLE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinHighProbabilityRegret`. The endpoint
`sampledPredictable_bernsteinHighProbabilityRegret_tail_total_delta` bounds
the generated exploration-mixed predictable regret bad event by
`ENNReal.ofReal delta`, with the pure-cross and fixed-comparator Bernstein
confidence radii evaluated at `delta / 2`. The raw endpoint retains the two
separate `ENNReal.ofReal delta` failure terms.

The proof reuses the sampled Hedge inequality, exploration bias, and the
pathwise estimator-square bound from the range-Hoeffding assembly. Outside the
two Bernstein bad events, these deterministic inequalities and both strict
confidence complements contradict the target regret event; `measure_mono_ae`
and `measure_union_le` close the union. Contracts allow zero horizon and every
positive delta, with no independence, stationarity, countability, supplied
integrability, or separate square concentration. The deterministic
`horizon / (gamma / |arms|)` square contribution remains, so this is not a
general Freedman theorem or an ideal tuned EXP3/EXP3.P rate. Its generated
realized selected-loss consumer now compiles below.

## EXP3 Random-Square Bernstein High-Probability Regret

`EXP3-RANDOM-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RandomSquareHighProbabilityRegret`. The supporting endpoint
`sampledPredictableObservedMixedSquared_sum_tail_markov` uses the
finite-horizon expectation upper bound `E[sum mixedSquare] <= |arms|*T` and Mathlib
`Integrable.measure_le_integral` to prove failure probability at most
`deltaSquare` above `|arms|*T/deltaSquare`. Pointwise nonnegativity,
measurability, and integrability of that sum are compiled in the same module.

The primary endpoint
`sampledPredictable_randomSquareBernsteinHighProbabilityRegret_tail_total_delta`
adds the square event to the pure-cross and fixed-comparator Bernstein events,
allocates `delta/3` to all three, and removes reciprocal `gamma` from the Hedge
square budget. Contracts are the generated predictable EXP3 contracts plus
`T>0` and `delta>0`; no independence, stationarity, countability, supplied
integrability, or new law transport is assumed. This is a real improvement over
the deterministic square assembly, but Markov costs `1/delta` rather than
`log(1/delta)`, and both confidence radii still depend on the exploration floor.
The generated realized consumer now compiles below. The ideal
logarithmic-confidence `sqrt(K*T)` route remains open.

## EXP3 Random-Square Bernstein Realized High-Probability Regret

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret`. The
primary endpoint
`sampledPredictable_randomSquareBernsteinRealizedHighProbabilityRegret_tail_total_delta`
controls cumulative generated scalar loss minus one supported comparator's true
predictable cumulative loss. Its budget adds the random-square predictable
budget to the bounded realized-deviation confidence radius.

The proof uses the exact pathwise decomposition into exploration-mixed
predictable regret and realized-minus-predictable deviation. The raw theorem
exposes the three predictable failures plus the realized failure; the public
wrapper allocates `delta/4` to all four and proves total failure
`ENNReal.ofReal delta`. Contracts require positive horizon and failure
allocations but add no independence, stationarity, countability, supplied
integrability, or law transport. The generated realized consumer is closed
without restoring reciprocal `gamma` in the Hedge-square term. Markov still
costs `1/delta`, both Bernstein radii retain exploration-floor dependence, and
the realized radius remains Hoeffding/Azuma, so ideal Freedman/EXP3.P rates are
still open. The learning-rate-only tuning now compiles below.

## EXP3 Random-Square Bernstein Realized Tuning

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning`. It chooses
`eta = sqrt(log K * (delta/4) / (T*K))` and proves that entropy plus the
stability-amplified Markov-square term is at most
`3*sqrt(4*K*T*log K/delta)` when `gamma <= 1/2`.

The deterministic endpoint bounds the complete four-event budget by this
balanced term plus `gamma*T`, both Bernstein radii at `delta/4`, and the
realized-deviation radius at `delta/4`. The final generated-trajectory theorem
uses `measure_mono` to transfer the existing tail to that explicit threshold.
Contracts require `K>=2`, `T>0`, `0<gamma<=1/2`, and `delta>0`; no
`delta<=1`, cubic/quadratic dominance, independence, stationarity,
countability, supplied integrability, or law transport is added. This closes
eta tuning only. The explicit large-horizon gamma schedule now compiles in the
adjacent route; the caller-selected surface remains useful without dominance
or `delta<=1` assumptions.

## EXP3 Random-Square Bernstein Realized Explicit Tuning

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning`. It first proves
that the two `delta/4` exploration-floor Bernstein radii are each at most
`3*gamma*T` under `K*log(4/delta)<=gamma^3*T`, while the realized radius is at
most `gamma*T` under `2*v*log(4/delta)<=gamma^2*T`. Together with exploration,
the tuned threshold is at most
`3*sqrt(4*K*T*log K/delta)+8*gamma*T`.

The final theorem chooses
`gamma=min(1/2,max((K*log(4/delta)/T)^(1/3),
sqrt(2*v*log(4/delta)/T)))` and discharges both dominance conditions from the
transparent assumptions `8*K*log(4/delta)<=T` and
`8*v*log(4/delta)<=T`. Contracts otherwise match the generated predictable
loss route and require `0<delta<=1`, `K>=2`, and `T>0`; no caller-supplied
gamma, independence, stationarity, countability, supplied integrability, or
new law transport is added. This is an explicit large-horizon result, not a
sharp large-horizon theorem: the leading Markov term still contains
`1/sqrt(delta)` and the realized radius remains Hoeffding/Azuma. The adjacent
all-horizon route handles active clipping with an honest coarse fallback.

## EXP3 Random-Square Bernstein Realized All Horizon

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedAllHorizon`. Its threshold
branches internally on the two factor-eight contracts. In the valid explicit
regime it uses `3*sqrt(4*K*T*log K/delta)+8*gamma*T`; otherwise it invokes the
compiled a.e. bound that generated selected-loss regret is at most `T`, making
the strict `T+1` event have measure zero.

The public theorem covers every `T>0` and `0<delta<=1` without a caller-supplied
regime proof. Its probability/Standard-Borel/measurability and
supported-comparator contracts match the explicit route, with no independence,
stationarity, countability, supplied integrability, or new law transport. This
closes all-horizon coverage, not sharp active-clipping analysis: the fallback
is deliberately coarse, while the refined branch still has Markov
`1/sqrt(delta)` dependence and Hoeffding/Azuma realized deviation. General
Freedman and ideal EXP3.P remain open.

## EXP3 Realized Regret With Bernstein Predictable Confidence

`EXP3-REALIZED-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret`. The endpoint
`sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_total_delta`
bounds cumulative scalar loss stored in the generated trajectory minus one
supported comparator's true predictable cumulative loss by
`ENNReal.ofReal delta`. Its budget is the predictable Bernstein regret budget
plus the realized-deviation confidence radius, both evaluated at `delta / 3`;
the raw endpoint displays all three equal-delta failures.

The pathwise identity splits realized regret into exploration-mixed
predictable regret and realized-minus-predictable deviation. The first term
uses the compiled pure-cross and fixed-comparator Bernstein tails; the second
uses the existing `[0,1]` Hoeffding/Azuma confidence radius. Contracts require
positive horizon and delta, but no `delta <= 1`, independence, stationarity,
countability, supplied integrability, extra law transport, or separate square
concentration. The deterministic `horizon / epsilon` Hedge-square term and the
bounded-loss realized radius remain, so this is not a general Freedman theorem,
a fully Bernstein variance-process result, or an ideal tuned EXP3/EXP3.P rate.

## EXP3 Bernstein Tuning Corollary

`EXP3-BERNSTEIN-TUNED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinTuning`. The endpoint
`sampledPredictable_tunedBernsteinRealizedHighProbabilityRegret_tail` chooses
`eta = sqrt (log K * gamma / (T * K))` and bounds the generated selected-loss
regret event at threshold `11 * gamma * T` by `ENNReal.ofReal delta`.

The proof records the exact rate contracts rather than hiding them: at least
two arms, positive horizon, `0 < gamma <= 1/2`, `0 < delta <= 1`, cubic
dominance of both `K * log K` and `K * log (3/delta)` by `gamma^3 * T`, and
quadratic dominance of the realized interval-variance budget by
`gamma^2 * T`. Entropy and the stability-amplified Hedge square term cost
`3 gamma T`; exploration costs `gamma T`; the two Bernstein radii cost
`3 gamma T` each; realized deviation costs `gamma T`. This closes the
characterized `T^(2/3)`-type implication for the retained deterministic square
term. Its concrete cube-root/max consumer now compiles below; an ideal
`sqrt(K*T)` EXP3.P/Freedman theorem remains separate.

## EXP3 Explicit Bernstein Schedule

`EXP3-EXPLICIT-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinExplicitTuning`. It defines `gamma` as one half
clipped against the maximum of the arm-entropy cube root, confidence cube root,
and realized square root, then proves the generated selected-loss regret tail
at `11*gamma*T` with failure at most `ENNReal.ofReal delta`.

The caller supplies no cubic or quadratic dominance proofs. Instead, the
module derives all three from `8*K*log K<=T`,
`8*K*log(3/delta)<=T`, and
`8*intervalVarianceProxy(0,1)*log(3/delta)<=T`; these also show the clip is
inactive. Contracts retain `K>=2`, `T>0`, `0<delta<=1`, the existing
probability/measurability assumptions, and a supported comparator. This closes
the explicit large-horizon `T^(2/3)`-type schedule. Its active-clip branch is
consumed by the all-horizon wrapper below. An ideal `sqrt(K*T)`
variance-sensitive route remains open.

## EXP3 All-Horizon Bernstein Realized Regret

`EXP3-ALL-HORIZON-BERNSTEIN-REALIZED-REGRET` now compiles in
`BanditRLProof.Exp3BernsteinAllHorizon`. Generated realized scalar loss equals
the selected predictable loss almost surely and is therefore at most one;
the comparator predictable sum is pointwise nonnegative. Finite-sum order then
gives generated realized regret at most `T` almost surely, so the bad event at
the strict threshold `T+1` has measure zero.

`sampledPredictable_allHorizonBernsteinRealizedRegret_tail` branches on the
three factor-eight horizon inequalities. It uses the explicit
`11*gamma*T` Bernstein tail when they hold and the zero-probability `T+1`
fallback otherwise, under the same positive-horizon and `0<delta<=1`
contracts but without caller-supplied regime proofs. This closes the
active-clipping gap. The fallback is deliberately coarse; the ideal
`sqrt(K*T)` EXP3.P/Freedman route remains open.

## EXP3 Mixed-Square Exponential Confidence

`EXP3-MIXED-SQUARE-EXPONENTIAL-CONFIDENCE` now compiles in
`BanditRLProof.Exp3MixedSquareConfidence`. The endpoint
`sampledPredictableObservedMixedSquared_sum_tail_delta` bounds the observed
mixed estimator-square sum at
`K*T + sqrt(2*T*intervalVarianceProxy(0,K/gamma)*log(1/delta))` with failure
at most `ENNReal.ofReal delta`.

The proof identifies the exact finite-action conditional mean
`sum_a loss_t(a)^2`, bounds the raw score in `[0,K/gamma]`, transports the
action law through `condExpKernel`, builds a strongly-adapted centered
process, and transports the latent square sum to scalar feedback almost
everywhere. Contracts are `0<gamma<=1`, positive horizon and delta, a
probability prior, the existing Standard-Borel/measurability assumptions, and
predictable `[0,1]` losses. No comparator, positive eta, `delta<=1`,
independence, stationarity, or supplied integrability is needed.

This removes the Markov `1/delta` threshold, but the interval proxy remains
of order `(K/gamma)^2` per round. The adjacent predictable- and realized-regret
theorems and their learning-rate-tuned consumer now compile. A concrete gamma
schedule remains open, and this is not a Freedman or ideal EXP3.P result.

## EXP3 Mixed-Square Exponential Predictable Regret

`EXP3-MIXED-SQUARE-EXPONENTIAL-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialHighProbabilityRegret`. Its
total-delta endpoint allocates `delta/3` to the mixed-square, pure-cross, and
fixed-comparator events and bounds generated exploration-mixed predictable
regret against one supported comparator by `ENNReal.ofReal delta`.

The new budget replaces `K*T/deltaSquare` by
`K*T + sampledMixedSquaredConfidenceRadius(...,deltaSquare)` inside the
Hedge stability coefficient. It reuses the compiled pathwise Hedge inequality,
exploration bias, and both Bernstein confidence routes; only the square event
and corresponding deterministic budget changed. Contracts require
`eta>0`, `0<gamma<1`, positive horizon and delta, the existing probability
and measurability assumptions, predictable `[0,1]` losses, and a supported
comparator. No `delta<=1`, independence, stationarity, or supplied
integrability is added.

This is the first downstream regret theorem to remove the Markov
`1/delta` square term. Its interval radius still contributes
`K/gamma * sqrt(T*log(1/delta))` before multiplication by eta. The adjacent
realized-loss and learning-rate-tuned consumers now compile; a concrete gamma
schedule, Freedman, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Bernstein Confidence

`EXP3-MIXED-SQUARE-BERNSTEIN-CONFIDENCE` now compiles in
`BanditRLProof.Exp3MixedSquareBernstein`. For `epsilon=gamma/K`, its generated
observed-square endpoint uses the radius
`2*sqrt(T*(K/epsilon)*log_+(1/delta)) + log_+(1/delta)/epsilon` and has failure
at most `ENNReal.ofReal delta`, including at horizon zero.

The finite sampling law gives the exact uncentered second moment and the
centered bound `K/epsilon`. The proof keeps the sharper centered range cap
`1/epsilon`, transports a fixed-tilt MGF through the existing
`condExpKernel` action law, sums the strongly-adapted generated process,
applies the `K*T` mean budget, transfers to observed feedback a.e., and
optimizes the separate variance coefficient and tilt cap. Contracts are a
probability prior, Standard Borel nonempty Env/Action, measurable singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable `[0,1]`
losses, any natural horizon, and `delta>0`; no comparator, eta positivity,
positive horizon, `delta<=1`, independence, stationarity, countability,
supplied integrability, or new law transport is added.

This improves the old `1/epsilon^2` interval proxy, but it is a fixed-tilt
deterministic `K/epsilon` variance bound, not a random predictable
quadratic-variation, anytime, self-normalized, or general Freedman theorem.

## EXP3 Mixed-Square Predictable Variance

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVariance`. It defines the exact
finite-action centered second moment, proves its finite-law integral identity,
nonnegativity, measurability, and `K/epsilon` bound, then instantiates it at
each generated EXP3 round. After shifting by one, the resulting process is
`IsPredictable` for `sampledPredictableDeviationFiltration`; its first `T`
actual-time values sum to at most `T*(K/(gamma/K))`.

The proof factors time zero through `Env` and successor rounds through
`(Env, finite prefix)`, using the existing generated probability source and
predictable-loss regularity. Contracts are measurable Env/Action, measurable
action singletons, decidable nonempty arms, arbitrary eta, `0<gamma<=1`,
predictable `[0,1]` losses, and any natural horizon. It needs no prior,
Standard Borel instance, comparator, confidence parameter, or integrability
premise. The compiled finite-action integral equality is not yet an ambient
`condExpKernel` square identity in this row; the adjacent law-transport row now
closes that gap and the new predictable-variance tail row consumes it. The
remaining blockers are maximal/anytime control and preserving the random
variance event through the EXP3 regret assembly.

## EXP3 Mixed-Square Predictable Variance Conditional Square Law

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-COND-EXP` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVariance`. Its primary endpoint states
that, at every shifted process index `n+1`, the ambient `condExpKernel` square
integral of the centered mixed-square increment given the generated filtration
`F_n` equals the matching shifted predictable variance almost everywhere.

The generic layer freezes history inside `condExpKernel`, composes the
identified finite action pushforward with the centered score, and applies
`integral_map` twice before using the finite-action square identity. Generated
wrappers instantiate time zero given `Env`, successors given `(Env,prefix n)`,
and then normalize both cases to the shifted process. Contracts are a finite
prior, Standard Borel nonempty Env/Action, measurable action singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable `[0,1]`
losses, and any process index; no probability prior, comparator, horizon,
delta, independence, stationarity, or supplied integrability is required.
This is an exact conditional-square law, not yet a random-variance
exponential-supermartingale or Freedman tail.

## EXP3 Mixed-Square Bernstein Predictable Regret

`EXP3-MIXED-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinHighProbabilityRegret`. Its total-delta
endpoint places the new mixed-square Bernstein radius inside the Hedge
stability term and combines it with the existing pure-cross and comparator
Bernstein radii using three `delta/3` events.

The theorem covers every natural horizon and otherwise retains the generated
predictable-adversary contracts: probability prior, Standard Borel nonempty
Env/Action, measurable singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable `[0,1]` losses, a supported comparator, and positive
delta. It is root imported and has a full external total-delta canary. The
realized-regret assembly below now consumes this radius; parameter tuning,
general Freedman, and ideal EXP3.P remain separate.

## EXP3 Mixed-Square Bernstein Realized Regret

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedHighProbabilityRegret`. Its
total-delta endpoint controls generated scalar cumulative loss minus one
supported comparator's true predictable cumulative loss using four
`delta/4` events.

The Lean route proves the pathwise identity between realized regret,
exploration-mixed predictable regret, and cumulative realized deviation. It
then combines `sampledPredictable_bernsteinSquareHighProbabilityRegret_tail`
with `sampledPredictableRealizedDeviation_sum_tail_delta`, contains the target
event in their union, and normalizes the four underlying allocations. No new
filtration, conditional-law, or integrability transport is introduced.

Contracts require a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable measurable `[0,1]` losses, a supported comparator,
positive horizon, and positive delta. The theorem is root imported and has a
full external total-delta canary. The mixed-square term now uses the
deterministic `K/epsilon` second-moment radius in generated realized regret,
but it is not random quadratic-variation or general Freedman control; the
realized radius remains Hoeffding/Azuma. Eta tuning now compiles below; explicit
gamma scheduling and ideal EXP3.P remain open.

## EXP3 Mixed-Square Bernstein Realized Tuning

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedTuning`. It defines

`S = K*T + sampledMixedSquaredBernsteinConfidenceRadius(arms,gamma,T,delta/4)`

and `eta=sqrt(log(K)/S)`. The generated endpoint controls realized selected-loss
regret at `3*sqrt(log(K)*S)+gamma*T` plus the pure-cross Bernstein, comparator
Bernstein, and realized-deviation radii, with failure at most
`ENNReal.ofReal delta`.

The proof explicitly establishes `S>0`: unlike the old interval-square scale,
the new radius has a linear `log_+/epsilon` term, so positivity uses `K>=2`,
`T>0`, and `gamma>0` to show both epsilon and the variance coefficient are
positive. It then proves `eta>0`, `eta^2*S=log K`, identifies entropy with
`eta*S` and `sqrt(log K*S)`, uses `gamma<=1/2` for the factor-two stability
bound, compares the complete realized budget, and applies measure monotonicity.

Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable singletons, decidable arms with `K>=2`, predictable `[0,1]` losses,
a supported comparator, positive horizon and delta, and `0<gamma<=1/2`. No
`delta<=1`, dominance premise, independence, stationarity, countability,
supplied integrability, or new law transport is added. The theorem is root
imported and externally canaried. Eta is now closed against the exact
deterministic Bernstein-square scale; explicit gamma scheduling, the linear
`log_+/epsilon` correction, Hoeffding/Azuma replacement, random quadratic
variation, general Freedman, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized Regret

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-HIGH-PROBABILITY-REGRET` now compiles
in `BanditRLProof.Exp3MixedSquareExponentialRealizedHighProbabilityRegret`.
Its primary endpoint controls generated scalar cumulative loss minus one
supported comparator's predictable cumulative loss with total failure
probability `ENNReal.ofReal delta`.

The proof uses the exact pathwise identity between realized regret,
exploration-mixed predictable regret, and cumulative realized deviation. The
predictable theorem contributes the exponential square, pure-cross Bernstein,
and comparator Bernstein events; the existing realized-deviation tail is the
fourth event. The public wrapper allocates `delta/4` to all four events.

Contracts require a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable nonempty arms, `eta>0`,
`0<gamma<1`, predictable measurable `[0,1]` losses, a supported comparator,
positive horizon, and positive delta. No `delta<=1`, independence,
stationarity, countability, supplied integrability, or new law transport is
introduced. Markov square dependence is now absent from generated realized
regret, but the `K/gamma` interval radius and bounded-loss Hoeffding/Azuma
realized radius remain. Learning-rate tuning compiles below; a concrete gamma
schedule, variance-sensitive Freedman control, and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized Tuning

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedTuning`. It defines

`S = K*T + sampledMixedSquaredConfidenceRadius(arms,gamma,T,delta/4)`

and chooses `eta=sqrt(log K/S)`. For `K>=2`, `T>0`, and
`0<gamma<=1/2`, the module proves `S>0`, `eta>0`,
`eta^2*S=log K`, and bounds entropy plus the stability-amplified square scale
by `3*sqrt(log K*S)`.

The public tail controls generated realized selected-loss regret at this
balanced term plus `gamma*T`, the two Bernstein radii, and the realized
deviation radius, all at `delta/4`, with failure at most
`ENNReal.ofReal delta`. It needs no `delta<=1` or caller-supplied dominance
contract. The explicit large-horizon gamma consumer and its coarse all-horizon
wrapper now compile below; this caller-selected theorem remains useful under
weaker assumptions. Variance-sensitive Freedman control and ideal EXP3.P
remain separate.

## EXP3 Mixed-Square Exponential Realized Explicit Tuning

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedExplicitTuning`. It chooses
`gamma` as the minimum of `1/2` and the maximum of four scales:

- `sqrt(K*log K/T)` for the `K*T` part of the balanced square scale;
- `(K^2*(log K)^2*log(4/delta)/(2*T^3))^(1/6)` for the current
  `(K/(2*gamma))^2` mixed-square interval proxy;
- `(K*log(4/delta)/T)^(1/3)` for both Bernstein confidence radii;
- `sqrt(2*v*log(4/delta)/T)` for realized deviation, where
  `v=intervalVarianceProxy(0,1)`.

The module proves the exact proxy identity, reduces the balanced square-root
term to `2*gamma*T`, and obtains a generated realized-regret tail at
`14*gamma*T`. Four transparent horizon contracts make clipping inactive and
discharge the quadratic, sixth-power, cubic, and realized quadratic dominance
conditions. Contracts are a probability prior, Standard Borel nonempty
Env/Action, measurable singletons, decidable arms with `K>=2`, predictable
measurable `[0,1]` losses, a supported comparator, `T>0`, `0<delta<=1`, and
the four displayed large-horizon inequalities; no independence, stationarity,
countability, supplied integrability, caller gamma, or new law transport is
added. Large-horizon gamma scheduling is now closed for this route. The
sixth-root term honestly records the current Hoeffding-proxy limitation. Its
active-clipping complement is consumed by the all-horizon wrapper below;
variance-sensitive Freedman control and ideal EXP3.P remain open.

## EXP3 Mixed-Square Exponential Realized All Horizon

`EXP3-MIXED-SQUARE-EXPONENTIAL-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3MixedSquareExponentialRealizedAllHorizon`. It defines the
exact four-contract large-horizon proposition and branches the generated
realized-regret threshold between the explicit exponential-square threshold,
which is bounded upstream by `14*gamma*T`, and the strict `T+1` fallback.

The positive branch invokes the compiled explicit-schedule tail. The
complementary branch reuses `sampledPredictable_trivialRealizedRegret_tail`,
whose pathwise finite-horizon bound makes the strict fallback event have
probability zero. Contracts are a probability prior, Standard Borel nonempty
Env/Action, measurable action singletons, decidable arms with `K>=2`,
predictable measurable `[0,1]` losses, a supported comparator, `T>0`, and
`0<delta<=1`; no caller regime proof, independence, stationarity,
countability, supplied integrability, or new law transport is added. The leaf
is root imported, has a focused build, and has a full external theorem canary
in `Tests.Basic`.

Failure policy: every positive horizon is covered, but outside the four-contract
regime the threshold is deliberately the coarse `T+1` zero-probability
fallback. The refined branch still has the Bernstein confidence cube-root
`T^(2/3)` limitation and Hoeffding/Azuma realized deviation. This is not a
sharp active-clipping theorem, variance-sensitive mixed-square Freedman
control, or ideal EXP3.P.

## EXP3 Mixed-Square Bernstein Realized Explicit Tuning

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedExplicitTuning`; the preceding
eta-tuning row is consumed by this endpoint. The public theorem
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail` balances eta
against the exact fixed-tilt Bernstein mixed-square scale and uses the same
conservative four-scale clipped gamma already compiled for the exponential
square route. Under the arm factor-four, mixed factor-64, confidence
factor-eight, and realized factor-eight contracts, its generated realized
regret threshold is `14*gamma*T` with failure at most `ENNReal.ofReal delta`.

The proof identifies the variance coefficient as `K^2/gamma`, uses
`gamma<=1/2` to turn the sixth-power mixed contract into the power needed by
the square-root term, uses the arm and confidence contracts for the linear
`log_+/epsilon` term, and derives the balanced-root bound `2*gamma*T`. It then
transports positivity, stability, and all four dominance contracts through a
thin alias of the existing clipped schedule and invokes the characterized
tail. Contracts are a probability prior, Standard Borel nonempty Env/Action,
measurable action singletons, decidable arms with `K>=2`, predictable `[0,1]`
losses, a supported comparator, `T>0`, and `0<delta<=1`; no independence,
stationarity, countability, supplied integrability, caller gamma, or new law
transport is added. The module is root imported and externally instantiated
in `Tests.Basic`.

Failure policy: this is an honest reuse of the conservative sixth-root
schedule, not a newly optimized fifth-root or coupled gamma formula. The
current linear `log_+/epsilon` correction is already controlled inside the
compiled constant; eliminating or improving it, Hoeffding/Azuma realized
deviation, random predictable quadratic variation, general Freedman, and ideal
EXP3.P remain open. The active-clipping complement now compiles below through
an honest coarse `T+1` fallback.

## EXP3 Mixed-Square Bernstein Realized All Horizon

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` now compiles in
`BanditRLProof.Exp3MixedSquareBernsteinRealizedAllHorizon` and consumes the
preceding explicit-tuning row. It defines the exact conjunction of the arm
factor-four, mixed factor-64, confidence factor-eight, and realized
factor-eight contracts. Its threshold is the explicit variance-sensitive
threshold, upstream-bounded by `14*gamma*T`, in that regime and strict `T+1`
otherwise.

The positive branch invokes
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail`. The negative
branch instantiates `sampledPredictable_trivialRealizedRegret_tail` with the
same exact Bernstein-square eta and clipped gamma, so the fallback event has
probability zero. Regularity contracts are a probability prior, Standard
Borel nonempty Env/Action, measurable action singletons, decidable arms with
`K>=2`, predictable `[0,1]` losses, a supported comparator, `T>0`, and
`0<delta<=1`; no caller regime proof, independence, stationarity,
countability, supplied integrability, or new law transport is added. The
module is root imported and externally instantiated in `Tests.Basic`.

Failure policy: every positive horizon is covered, but outside the exact
four-contract regime the `T+1` threshold is deliberately coarse. The refined
branch retains the controlled linear `log_+/epsilon` term and
Hoeffding/Azuma realized deviation. This is not sharp active clipping, a
sharper fifth-root/coupled schedule, random predictable quadratic variation,
general Freedman, or ideal EXP3.P.

## EXP3 Mixed-Square Predictable-Variance Tail

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-TAIL` now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceTail`. The fixed-tilt theorem
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_fixedTilt`
proves
`P(sum X >= x and sum V <= v) <= exp(-t*x+t^2*v)` for
`0<=t<=gamma/K`. The optimized theorem
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta`
uses radius `2*sqrt(v*log_+(1/delta))+log_+(1/delta)/(gamma/K)` and failure
probability at most `ENNReal.ofReal delta`.

The proof establishes the support bound `|X|<=1/epsilon`, retains the exact
finite-law centered second moment in the one-step MGF, subtracts that random
predictable budget, transports the compensated law through the generated
zero/successor conditional kernels, and iterates the shifted strongly adapted
process with the existing fixed-MGF sum theorem. Contracts are a probability
prior, Standard Borel nonempty Env/Action, measurable action singletons,
decidable nonempty arms, arbitrary eta, `0<gamma<=1`, predictable measurable
`[0,1]` losses, any natural horizon, and positive `v,delta` for the optimized
wrapper. The module is root imported and its delta endpoint has an external
canary in `Tests.Basic`.

Failure policy: this is a fixed-horizon joint-event predictable-variance
Bernstein/Freedman theorem. It is not maximal/Ville, peeling/stitching,
anytime/self-normalized, an unconditional tail without controlling `sum V`,
or a complete ideal EXP3.P regret theorem. Its random-variance event is now
consumed by the generated predictable-regret route below.

## EXP3 Mixed-Square Predictable-Variance High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-HIGH-PROBABILITY-REGRET` now
compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceHighProbabilityRegret`.
The observed-square bridge transports the centered joint tail to the Hedge
square sum using `sampledObservedMixedSquaredSum_eq_predictable_ae`, the exact
deviation identity, and the `K*T` predictable-mean bound. The joint regret
endpoint combines that event with the existing pure-cross and comparator
Bernstein events. The primary total-delta theorem proves
`P(regret >= budget(v,delta)) <= ofReal(delta) + P(sum V > v)`, with square
radius `2*sqrt(v*log_+(3/delta))+log_+(3/delta)/(gamma/K)`.

The proof uses the sampled Hedge inequality, exploration bias, strict
complements of the three confidence events, `measure_mono_ae`, and union
bounds. It then splits the unconditional regret event into the compiled joint
event on `sum V<=v` and the single variance-overflow event. Contracts are a
probability prior; Standard Borel nonempty Env/Action; measurable action
singletons; decidable nonempty arms; `eta>0`; `0<gamma<1`; predictable
measurable `[0,1]` losses; a supported comparator; any natural horizon; and
positive `v,delta`. No `delta<=1`, independence, stationarity, countability,
supplied integrability, deterministic variance-envelope premise, or new
conditional-law transport is required. The module is root imported and the
primary residual theorem has an external canary in `Tests.Basic`.

Failure policy: random predictable variance now reaches generated predictable
regret without replacement by the deterministic envelope and is consumed by
the realized selected-loss route below. A closed sharper regret rate still
requires control of `P(sum V>v)`, for example through
algorithm-specific structure, peeling/stitching, or a maximal/self-normalized
argument. This is not anytime control, general Freedman, or ideal EXP3.P.

## EXP3 Mixed-Square Predictable-Variance Realized High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-REALIZED-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedHighProbabilityRegret`.
Its joint total-delta endpoint proves
`P(realized regret >= budget(v,delta) and sum V <= v) <= ofReal(delta)`, and
the primary residual endpoint proves
`P(realized regret >= budget(v,delta)) <= ofReal(delta) + P(sum V > v)`.
The budget adds `sampledPredictableRealizedDeviationConfidenceRadius` to the
predictable random-variance budget and allocates `delta/4` to random-square,
pure-cross, comparator, and realized-deviation failures.

The proof rewrites realized selected-loss regret pathwise as predictable
exploration-mixed regret plus cumulative realized deviation, unions the
predictable joint event with the compiled realized-deviation event, then
splits the unconditional event into the variance-good branch and the strict
overflow `varianceBudget < sum V`. Contracts are a probability prior;
Standard Borel nonempty Env/Action; measurable action singletons; decidable
nonempty arms; `eta>0`; `0<gamma<1`; predictable measurable `[0,1]` losses;
a supported comparator; positive horizon; and positive variance budget and
confidence allocations. No `delta<=1`, independence, stationarity,
countability, supplied integrability, deterministic variance-envelope
premise, or new conditional-law transport is required. Retrieval uses the
predictable-variance regret row, realized-deviation confidence, the comparable
Bernstein realized assembly, Mathlib measure/finite-sum/order/sub-Gaussian/MGF
cards, the Auer EXP3 card, and inspiration-only potential/tail weapons. The
module is root imported, focused-built, and externally canaried at the primary
total-delta residual theorem in `Tests.Basic`.

Failure policy: realized selected-loss transport is closed while preserving
the overflow probability and this row is consumed by the Markov route below.
No maximal/anytime or self-normalized theorem, general Freedman theorem, or
ideal EXP3.P theorem is claimed.

## EXP3 Predictable-Variance Realized Markov High-Probability Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceRealizedMarkovHighProbabilityRegret`.
Its Mathlib-backed overflow endpoint states
`mu {sum V > v} <= lintegral (ofReal (sum V)) mu / ofReal v` for any measure
and `v>0`. The raw realized consumer substitutes an explicit contract
`lintegral (ofReal (sum V)) mu <= ofReal varianceMeanBudget` into the prior
residual theorem. The primary endpoint chooses
`v=varianceMeanBudget/(delta/5)`, allocates `delta/5` to random-square,
pure-cross, comparator, realized-deviation, and overflow failures, and proves
`P(realized regret >= budget(varianceMeanBudget,delta)) <= ofReal delta`.

Local APIs/imports are the prior realized residual route,
`Mathlib.MeasureTheory.Integral.Lebesgue.Markov`,
`meas_ge_le_lintegral_div`, cumulative-variance measurability/nonnegativity,
`ENNReal.measurable_ofReal`, `measure_mono`, `ENNReal.div_le_div`,
`ENNReal.ofReal_div_of_pos`, `ENNReal.div_div_cancel`, and
`ENNReal.ofReal_add`. The proof contains the strict real overflow event in
Mathlib's weak ENNReal threshold event, applies Markov, inserts the supplied
lintegral budget, then normalizes five equal allocations.

The generic Markov leaf needs only an arbitrary measure, measurable
Env/Action with measurable action singletons, decidable nonempty arms,
`0<gamma<=1`, predictable measurable `[0,1]` losses, and `v>0`; it does not
need a finite measure. The primary regret endpoint additionally requires a
probability prior, Standard Borel nonempty Env/Action, `eta>0`, `0<gamma<1`,
a supported comparator, positive horizon, positive variance mean budget and
delta, and the displayed generated-trajectory lintegral contract. No
`delta<=1`, independence, stationarity, countability, separate integrability
witness, deterministic envelope, or new law transport is required. Retrieval
uses `MLIB-MEASURE-INTEGRAL` with Markov, finite-sum/order cards, the Auer EXP3
card, and inspiration-only tail/potential weapons. The module is root imported,
focused/root built, and externally canaried at the primary endpoint.

Failure policy: the probability residual is closed under a precise expectation
contract, and the loss-energy route below now discharges it when a pathwise
armwise loss-square budget is supplied. Markov still forces `v` to scale as
`varianceMeanBudget/delta`; sharper scenario-specific energy estimates or a
stronger exponential/self-normalized overflow theorem are still required for
general Freedman, anytime control, or ideal EXP3.P.

## EXP3 Predictable-Variance Loss-Energy Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-LOSS-ENERGY-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceLossEnergyRealizedMarkovHighProbabilityRegret`.
Its finite-law endpoint proves that the centered mixed-square estimator
variance is at most `(1/epsilon) * sum_a loss(a)^2`. Generated transport and
finite summation yield
`sum V <= (1/(gamma/K)) * sampledPredictableLossSquaredSum`. Consequently, a
pathwise armwise loss-square budget `L2` gives the exact lintegral contract
`lintegral(ofReal(sum V)) <= ofReal((1/(gamma/K))*L2)` and the prior Markov
consumer yields a realized selected-loss tail with total failure `delta`.

Local APIs/imports are the prior realized Markov module,
`sampledPredictableLossSquaredSum`, the exact mixed-square first/second-moment
identities, `FiniteActionDistribution.sum_eq_one`, generated probability and
loss-regularity sources, finite-sum/order/ring arithmetic, `lintegral_mono`,
`ENNReal.ofReal_le_ofReal`, and probability-measure integration of constants.
The proof expands the centered variance, applies `loss^4<=loss^2` and the
probability floor termwise, subtracts the nonnegative squared mean, transports
the result to every generated time, factors the horizon sum, integrates the
pathwise energy bound, and invokes the five-event Markov theorem.

The generic finite-law theorem needs a positive probability floor and losses
in `[0,1]`. The generated primary endpoint requires a probability prior,
Standard Borel nonempty Env/Action, measurable action singletons, decidable
nonempty arms, `eta>0`, `0<gamma<1`, predictable measurable `[0,1]` losses, a
supported comparator, positive horizon, positive `L2` and `delta`, and the
pathwise cumulative loss-square contract. No `delta<=1`, independence,
stationarity, countability, separate integrability witness, new law transport,
or deterministic `K*T` envelope premise is required. Retrieval uses the prior
Markov and predictable-variance rows, mixed-square Bernstein confidence,
finite-sum/order/measure cards, the Auer EXP3 card, and inspiration-only
tail/potential weapons. The module is root imported, focused/root built, and
externally canaried at the primary theorem.

Failure policy: the downstream small-loss route now derives `L2<=L1` and
replaces the Hedge `K*T` mean upper bound by `L1`. Markov still costs
`(L2/epsilon)/delta`; sharper exponential/self-normalized overflow,
maximal/anytime control, general Freedman, and ideal EXP3.P remain open.

## EXP3 Predictable-Variance Small-Loss Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SMALL-LOSS-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret`.
It defines the pathwise armwise loss mass
`L1=sum_t sum_a predictableLoss_t(a)` and proves `sum_t sum_a loss_t(a)^2<=L1`
from the existing `[0,1]` regularity. Hence `sum V<=(1/(gamma/K))*L1`, and the
same inequality supplies the generated variance `lintegral` budget.

The new observed-square bridge uses `L1` as an upper bound on the exact
predictable mixed-square mean `L2`, replacing the previous `K*T` upper bound.
Its predictable regret budget is
`log(K)/eta + eta/(1-gamma)*(L1+radius(v,deltaSquare)) + gamma*T` plus the
pure-cross and comparator Bernstein radii. The realized wrapper adds the
realized-deviation radius. The primary theorem sets
`v=((1/(gamma/K))*L1)/(delta/5)`, allocates `delta/5` to mixed-square,
pure-cross, comparator, realized-deviation, and Markov overflow, and proves the
generated realized selected-loss tail is at most `ofReal(delta)`.

Local APIs/imports are the loss-energy module, generated predictable loss
coordinates and unit-interval contracts, finite sums, observed/predictable
mixed-square a.e. equality, centered predictable-variance tail, sampled Hedge,
exploration bias, pure-cross/comparator Bernstein tails, realized-deviation
confidence, variance lintegral and Mathlib Markov, measure unions, and ENNReal
division/ofReal algebra. The proof first derives `l^2<=l`, sums over arms/time,
rebuilds the three-event predictable assembly with `L1`, adds realized
deviation as a fourth event, then splits the unconditional event into the
variance-good branch and fifth Markov overflow event.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon, `L1`, and `delta`; and a universal pathwise armwise loss-mass
bound. No `delta<=1`, independence, stationarity, countability, separate
integrability, new law transport, deterministic `K*T`, supplied `L2`, or
supplied variance-lintegral premise is required. Retrieval uses the loss-energy
and predictable/realized variance rows, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `MLIB-MEASURE-INTEGRAL`, `SCN-ADVERSARIAL-FINITE`, the
Auer EXP3 card, and inspiration-only tail/potential weapons. The module is root
imported, focused/root built, and externally canaried at the primary theorem.

Failure policy: this is an armwise aggregate small-loss theorem, not a standard
first-order best-arm-loss guarantee. The generic pathwise `L1` premise is now
consumed by the sparse-loss route below. `eta` and `gamma` remain
caller-selected, and Markov gives `v=(L1/(gamma/K))/(delta/5)`. L1-aware
tuning, best-arm first-order conversion, exponential/self-normalized overflow,
anytime control, general Freedman, and ideal EXP3.P remain open.

## EXP3 Predictable-Variance Sparse-Loss Realized Markov Regret

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-HIGH-PROBABILITY-REGRET`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret`.
The Lean-facing support definition filters `arms` to coordinates with nonzero
`predictableLossAt`. `sampledPredictableLossMassAt_le_supportCard` removes the
zero coordinates and uses the existing `[0,1]` contract to bound one-round
armwise loss mass by the support cardinality.
`sampledPredictableLossMassSum_le_sparsity_mul_horizon` then turns a universal
per-round natural support cap `s` into `L1 <= s*T`. The sparse budget aliases
the small-loss budget at `lossMassBudget=(s:Real)*T`, and the primary theorem
proves the generated realized selected-loss bad event has probability at most
`ENNReal.ofReal delta`.

Local APIs/imports are the compiled small-loss module,
`sampledPredictableLossMassSum`, `predictableLossAt_mem_unitInterval`,
`Finset.filter`, `Finset.filter_subset`, `Finset.sum_subset`,
`Finset.sum_le_sum`, `Finset.mem_range`, `Nat.cast_le`, and finite-sum/order
algebra. The proof filters to nonzero support, bounds each retained coordinate
by one, sums the support cap over `Finset.range horizon`, proves positivity of
`s*T`, and invokes the small-loss total-delta theorem.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, positive natural sparsity, positive delta; and the pathwise
support-cardinality cap for every generated sample and `t<horizon`. No
`s<=K`, `delta<=1`, independence, stationarity, countability, supplied
integrability, new law transport, supplied `L1`/`L2`/lintegral premise, or
deterministic `K*T` premise is required.

Retrieval uses the compiled small-loss row, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`, the Auer EXP3 card, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the primary theorem.

Failure policy: this closes the former abstract `L1` input for uniformly
pathwise sparse nonzero supports, but the result still controls armwise
aggregate loss and assumes sparsity for every generated sample. Eta is selected
by the tuning route below; gamma remains caller-selected and Markov retains
`1/delta`. Best-arm first-order conversion, probabilistic sparsity,
exponential/self-normalized overflow, anytime control, general Freedman, and
ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovTuning`.
For `L=(s:Real)*T`, it defines the exact Markov threshold
`v=((1/(gamma/K))*L)/(delta/5)` and complete Hedge scale
`S=L+sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta/5)`.
The internal learning rate is `eta=sqrt(log K/S)`.

The module proves `v>0`, `S>0`, `eta>0`, and `eta^2*S=log K`. Under
`K>=2` and `0<gamma<=1/2`, it identifies the entropy term with
`sqrt(log K*S)` and bounds the stability-amplified term by twice entropy.
Thus the complete eta-dependent budget is at most `3*sqrt(log K*S)`. The
tuned threshold adds `gamma*T` and the pure-cross, comparator, and
realized-deviation radii at `delta/5`; the final theorem tightens the compiled
sparse-loss event and retains failure probability `ENNReal.ofReal delta`.

Local APIs/imports are the sparse-loss total-delta module, its exact budget,
`sampledMixedSquaredPredictableVarianceRadius`, `Real.log`, `Real.sqrt`,
`Real.log_pos`, `Real.sqrt_pos`, `Real.sq_sqrt`, finite-cardinality casts,
`field_simp`, `ring`, `linarith`, `nlinarith`, and `measure_mono`.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; supported comparator;
positive horizon, natural sparsity, and delta; and the universal pathwise
support-cardinality cap. Eta is internal. No eta premise, `s<=K`, `delta<=1`,
independence, stationarity, countability, supplied integrability, new law
transport, supplied `L1`/`L2`/lintegral premise, or deterministic `K*T`
premise is required.

Retrieval uses the sparse-loss route, existing exponential/Bernstein square
tuning templates, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`,
`MLIB-FINSET-SUMS`, `SCN-ADVERSARIAL-FINITE`, the Auer EXP3 card, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the final theorem.

Failure policy: eta tuning is closed against the exact Markov sparse-loss
scale and is consumed by the explicit-gamma route below. Sparsity remains
universal pathwise, the loss notion remains armwise aggregate, and Markov
retains `1/delta`. Probabilistic sparsity, best-arm conversion,
exponential/self-normalized overflow, general Freedman, anytime control, and
ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov Explicit Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning`.
Writing `B=log(5/delta)`, it proves the exact Markov budget
`v=5*K*s*T/(gamma*delta)` and uses the full scale
`S=s*T+sampledMixedSquaredPredictableVarianceRadius(K,gamma,v,delta/5)`.
The contracts
`s*log K<=gamma^2*T`,
`5*K*s*(log K)^2*B<=gamma^5*delta*T^3`, and
`K*B<=gamma^3*T` control the complete balanced scale by
`sqrt(log K*S)<=2*gamma*T`; the usual realized quadratic contract then bounds
the eta-tuned threshold by `14*gamma*T`.

The explicit gamma is the minimum of `1/2` and the maximum of the sparse arm
square root, Markov fifth root, confidence cube root, and realized square
root. New fifth-root lemmas based on `Real.rpow_inv_natCast_pow` recover the
fifth-power contract. Four horizon inequalities with constants `4`, `32`,
`8`, and `8` make clipping inactive and discharge every characterized
premise. The final theorem
`sampledPredictable_explicitSparseLossPredictableVarianceRealizedMarkovRegret_tail`
selects both eta and gamma internally and bounds the generated realized-regret
bad event by `ENNReal.ofReal delta`.

Local APIs/imports are the preceding sparse eta-tuned theorem, the existing
explicit exponential-square algebra template, `Real.rpow_inv_natCast_pow`,
`Real.sqrt_le_iff`, power monotonicity, max/min order lemmas, the generic
Bernstein-radius and realized-radius dominance lemmas, finite-cardinality
casts, field/ring normalization, arithmetic tactics, and `measure_mono`.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; the four explicit large-horizon
inequalities; and universal pathwise support sparsity. No caller eta/gamma,
`s<=K`, independence, stationarity, countability, supplied integrability, new
law transport, or supplied `L1`/`L2`/lintegral premise is required.

Retrieval uses the sparse eta-tuned route, exponential explicit-tuning and
Bernstein explicit-tuning templates, `MLIB-REAL-LOG-SQRT`,
`MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the final explicit theorem.

Failure policy: explicit large-horizon eta/gamma tuning is closed and consumed
by the all-horizon route below. The fifth-root term preserves polynomial
`1/delta` dependence inherited from Markov, while the theorem remains armwise
aggregate with universal pathwise sparsity. Best-arm first-order conversion,
probabilistic sparsity, exponential/self-normalized overflow, general
Freedman, anytime control, sharper constants, and ideal EXP3.P remain open.

## EXP3 Sparse-Loss Predictable-Variance Realized Markov All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAllHorizon`.
It packages the four explicit contracts into
`sparseLossPredictableVarianceLargeHorizonCondition` and defines a branch
threshold: the compiled explicit `14*gamma*T` threshold in that regime, and
the strict `(T:Real)+1` threshold otherwise.

The final theorem
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail`
branches on that condition. The positive branch invokes the explicit
sparse-loss theorem after projecting the four conjunction fields. The
negative branch applies `sampledPredictable_trivialRealizedRegret_tail` with
the same internally selected eta and clipped gamma. It therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof.

Local APIs/imports are the explicit sparse-loss tuning module,
`Exp3BernsteinAllHorizon`, the explicit and strict-fallback tail theorems,
the generated realized-to-selected almost-sure law behind the fallback,
classical `if`/`by_cases`, schedule positivity/stability, and existing
finite-sum/order/measure-zero APIs.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; and universal pathwise support
sparsity. Eta and gamma are internal. No large-horizon premise, caller
eta/gamma, `s<=K`, independence, stationarity, countability, supplied
integrability, new law transport, or supplied `L1`/`L2`/lintegral premise is
required.

Retrieval uses the explicit sparse-loss route, generic Bernstein and
exponential-square all-horizon templates, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the final all-horizon theorem.

Failure policy: all positive horizons are covered, but the complementary
branch deliberately uses the coarse zero-probability `T+1` threshold. The
refined branch retains Markov's polynomial `1/delta`, universal pathwise
sparsity, armwise aggregate loss, componentwise constant `14`, and bounded
realized deviation. A sharp active-clipping rate, best-arm first-order
conversion, probabilistic sparsity, stronger overflow, general Freedman,
anytime control, and ideal EXP3.P remain open.

## EXP3 Sparse-Loss Realized Markov A.E. Sparsity All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-AE-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAESparsityAllHorizon`.
Its Lean endpoint
`sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_ae_sparsity`
uses the same internal eta, clipped gamma, branch threshold, and exact
generated trajectory measure as the preceding all-horizon theorem, but only
assumes the support cap on one common almost-everywhere event under that
measure.

The supporting small-loss APIs now accept an a.e. `L1` budget. The
sample-local support lemma transports a.e. sparsity to `L1<=S*T`;
`lintegral_mono_ae` supplies the Markov variance mean bound, and the
observed-square event inclusion uses the same a.e. event. Thus no extra
failure allocation is introduced. In the four-contract branch the proof
combines the raw a.e.-sparse tail with the compiled raw-to-tuned and
tuned-to-explicit budget comparisons; otherwise it reuses the strict `T+1`
zero-probability fallback.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; and a.e. support sparsity under the exact
internally tuned generated measure. No universal pathwise cap, extra
sparsity-failure probability, caller regime proof, eta/gamma, `S<=K`,
independence, stationarity, countability, or supplied integrability is needed.

Retrieval uses the pathwise all-horizon, sparse base, and small-loss rows;
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused-built, and
externally canaried in `Tests.Basic`.

Failure policy: measure-zero exceptional sparsity paths cost no probability,
but positive-probability sparsity violations remain open. The fallback is
still coarse, and the refined branch retains Markov polynomial `1/delta`,
armwise aggregate loss, constant `14`, and bounded realized deviation.

## EXP3 Sparse-Loss Realized Markov Probabilistic Sparsity

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity`.
The Lean-facing `sampledPredictableSparsityFailure` event contains exactly the
generated trajectories with some `t<T` whose nonzero predictable-loss support
has cardinality greater than `S`.
`sampledPredictableLossMassSum_le_or_mem_sparsityFailure` proves pointwise that
`L1<=S*T` or the sample lies in that event. The small-loss observed-square,
predictable-joint, and realized-joint layers now expose matching explicit-bad-
set residual APIs.

The Markov mean cannot use `S*T` on exceptional paths. The new global lemma
uses `support.card<=arms.card` to prove `L1<=K*T` for every trajectory and then
derives
`sampledPredictableGlobalVarianceMeanBudget=(1/(gamma/K))*(K*T)`.
The regret budget therefore keeps `S*T` in the observed-square and Hedge terms
but uses the global variance mean divided by `delta/5` for overflow.
`sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail`
bounds the bad-regret event by `ofReal(delta)+mu(sparsityFailure)`, and the
`_tail_of_sparsityFailure_le` consumer turns a supplied
`mu(sparsityFailure)<=ofReal(epsilon)` into `ofReal(delta)+ofReal(epsilon)`.

Local APIs/imports are the sparse base and small-loss modules; the three
explicit-bad-set residual consumers; `Filter.Eventually.of_forall`;
`Finset.filter_subset`, `Finset.card_le_card`; `lintegral_mono_ae`;
`measure_mono`, `measure_union_le`; ENNReal division/addition; and finite-sum
and order algebra. The proof route splits each sample into sparse-or-bad,
uses `S*T` only on the variance-good realized residual event, independently
closes Markov overflow with the global `K*T` lintegral, unions the fifth
ordinary event, and normalizes the five `delta/5` terms before adding the
sparsity-failure measure.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon and delta; a natural sparsity level; and, for the practical
consumer, the exact generated-measure sparsity-failure bound. No universal or
a.e. sparsity cap, `S>0`, `S<=K`, `epsilon>=0`, `delta<=1`, independence,
stationarity, countability, supplied integrability, or event-measurability
premise is required.

Retrieval uses the a.e.-sparsity, sparse-base, and small-loss rows;
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the `delta+epsilon` consumer in `Tests.Basic`.

Failure policy: positive-probability sparsity violations are now represented
honestly, but the threshold pays the global `K*T` Markov envelope instead of
the sparse `S*T` envelope. Eta/gamma remain caller-selected; Markov remains
polynomial in `1/delta`; and the result is armwise aggregate. Do not claim the
tuned all-horizon `14*gamma*T` threshold, best-arm first-order conversion,
exponential/self-normalized overflow, general Freedman, anytime control, or
ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise Variance

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity`.
The Lean-facing
`sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure`
proves pointwise that
`sum V <= (1/(gamma/K))*(S*T)` or the generated sample belongs to the exact
sparsity-failure event. The budget
`sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget`
therefore uses `S*T` both for the observed-square mean and for the deterministic
variance threshold, with four `delta/4` confidence allocations and no Markov
overflow event.

The small-loss module now exposes observed-square, predictable-joint, and
realized-joint off-bad APIs. Their source events are explicit set differences
by `bad`, and their conclusions contain only the ordinary confidence
allocations. The final pathwise-variance theorem contains the full regret event
in the off-bad variance-good event union `sparsityFailure`, giving
`ofReal(delta)+mu(sparsityFailure)`. Its practical consumer gives
`ofReal(delta)+ofReal(epsilon)` under the exact same generated-measure failure
bound.

Local APIs/imports are the probabilistic-sparsity and small-loss modules;
`sampledPredictableLossMassSum_le_or_mem_sparsityFailure`;
`sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossMassSum`; the
three off-bad joint tails; `Set.diff`, intersection, and union;
`Filter.Eventually.of_forall`; `measure_mono`, `measure_union_le`;
`ENNReal.ofReal_add`; and finite-sum, cast, ring, and order algebra. The proof
route is pointwise sparse variance or bad, four-event off-bad confidence, one
final union with the failure event, and normalization of four quarters.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable nonempty arms; `eta>0`;
`0<gamma<1`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and the exact generated-measure
failure bound for the epsilon consumer. No event-measurability premise,
restricted measure, universal/a.e. sparsity cap, `S<=K`, epsilon positivity,
`delta<=1`, independence, stationarity, countability, supplied integrability,
Markov inequality, or new law transport is required.

Retrieval uses the probabilistic Markov row, small-loss off-bad declarations,
sparse-base row, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`, Auer EXP3, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the practical
`delta+epsilon` theorem in `Tests.Basic`.

Failure policy: the caller-selected eta/gamma surface no longer pays global
`K*T`, `K^2`, or polynomial Markov `1/delta` variance costs. Eta tuning now
compiles downstream, and the large-horizon explicit gamma route now consumes
that tuning. The small-horizon/all-horizon fallback still uses the older
five-event route. The theorem remains armwise aggregate and uses bounded
realized deviation; do not claim best-arm first-order conversion, general
Freedman, anytime control, sharp active clipping, or ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning`.
The complete scale is
`S*T + predictableVarianceRadius((1/(gamma/K))*S*T, delta/4)`, and
`pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate` sets
`eta=sqrt(log K/scale)`.

The module proves positivity of the scale and eta, the exact balance
`eta^2*scale=log K`, and under `gamma<=1/2` the Hedge entropy-plus-stability
bound `3*sqrt(log K*scale)`. The raw four-event budget is contained in
`pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold`, whose three
remaining confidence radii all use `delta/4`. The generated residual theorem
preserves `delta+mu(sparsityFailure)`, and the practical endpoint consumes the
failure bound under the exact internally eta-tuned measure to obtain
`delta+epsilon`.

Local APIs/imports are the pathwise-variance probabilistic-sparsity module;
the sparse pathwise variance budget and predictable-variance radius;
`Real.log`, `Real.sqrt`, square and positivity APIs; finite casts;
field/ring/nonlinear arithmetic; `measure_mono`; and ENNReal addition. The
proof route is positive four-event scale, sqrt balancing, gamma-half stability
control, raw-to-tuned budget inclusion, and exact-measure residual
consumption.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and the exact internally eta-tuned
generated-measure failure bound for epsilon. Eta is internal. No global
`K*T` envelope, Markov, caller eta, event measurability, restricted measure,
universal/a.e. cap, `S<=K`, epsilon positivity, `delta<=1`, independence,
stationarity, countability, supplied integrability, or new law transport is
required.

Retrieval uses the pathwise-variance base row, the previous eta-tuning algebra
template, `MLIB-REAL-LOG-SQRT`, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, adversarial finite/Auer EXP3, and
inspiration-only tail/potential weapons. Status is `leanCompiled`, root
imported, focused/root built, and externally canaried at the eta-tuned
`delta+epsilon` theorem.

Failure policy: eta has been migrated to the four-event sparse variance scale,
so this layer no longer pays global `K*T`, `K^2`, or Markov `1/delta`. Gamma
is now selected by the compiled explicit route below. The all-horizon fallback
is the next route leaf; armwise aggregate loss, bounded realized deviation,
best-arm conversion, general Freedman, anytime control, sharp clipping, and
ideal EXP3.P remain open.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Explicit Gamma

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning`.
The sparse good-path variance budget rewrites to `K*S*T/gamma`. The resulting
mixed exploration component is
`(K*S*(log K)^2*log(4/delta)/T^3)^(1/5)`, with neither the extra `K` nor the
polynomial `1/delta` from the global-envelope Markov route.

The module proves the log-weighted predictable-variance radius is at most
`3*gamma^2*T^2`, the balanced root is at most `2*gamma*T`, and the eta-tuned
threshold is at most `14*gamma*T`. It then defines gamma as the clipped
maximum of the sparse arm square root, the new pathwise mixed fifth root, the
Bernstein cube root, and the realized-deviation square root. Four transparent
large-horizon contracts prove clipping inactive and supply every characterized
contract. The final generated endpoints give `delta+mu(sparsityFailure)` and
`delta+epsilon` under the exact internally eta/gamma-tuned measure.

Local APIs/imports are the pathwise eta-tuned theorem and sparse variance
budget; `sampledMixedSquaredPredictableVarianceRadius`;
`log_one_div_fourth_eq_log_four_div`; the Bernstein and realized radius
dominance lemmas; sparse arm and random-square confidence/realized exploration
scales; the existing general fifth/cube/square root algebra helpers;
`Real.log`/`sqrt`/`rpow`; finite casts; field/ring/nonlinear arithmetic;
`measure_mono`; and ENNReal addition. The old Markov explicit module is used
only for reusable root/power utilities, not as probability evidence.

The proof route is budget normalization, fifth-power and cubic radius control,
balanced-root and `14*gamma*T` comparison, clipped four-component schedule,
large-horizon contract extraction, event containment under one generated
measure, and exact failure-event consumption.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; the four inequalities
`4*S*log K<=T`,
`32*K*S*(log K)^2*log(4/delta)<=T^3`,
`8*K*log(4/delta)<=T`, and
`8*intervalVarianceProxy(0,1)*log(4/delta)<=T`; and the exact internally
tuned failure bound for epsilon. Eta and gamma are internal. No global `K*T`
envelope, Markov overflow, `K^2` mixed numerator, polynomial `1/delta`,
event measurability, restricted measure, universal/a.e. cap, `S<=K`, epsilon
positivity, independence, stationarity, countability, supplied integrability,
or new law transport is required.

Retrieval uses the pathwise eta-tuning row; reusable algebra from the old
explicit row; `MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
adversarial finite/Auer EXP3, and inspiration-only tail/potential weapons.
Status is `leanCompiled`, root imported, focused/root and `Tests.Basic` built,
and externally canaried at the fully explicit `delta+epsilon` theorem.

Failure policy: the large-horizon explicit-gamma branch is closed on the
four-event pathwise scale and is consumed by the all-horizon theorem below.
The result remains armwise aggregate and uses bounded realized deviation; do
not claim sharp active clipping, best-arm first-order conversion, general
Freedman, anytime control, or ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Pathwise-Variance All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityAllHorizon`.
It names the exact four-contract regime used by the pathwise explicit
schedule and defines an all-horizon threshold: the refined explicit threshold
(already bounded by `14*gamma*T`) in that regime, and strict `T+1`
otherwise.

The generated off-bad theorem gives `delta` after removing the exact
`sampledPredictableSparsityFailure` set. The residual theorem then gives
`delta+mu(sampledPredictableSparsityFailure)` for every positive horizon.
The practical theorem consumes the exact same-measure failure bound and gives
`delta+epsilon`. Both branches use the same internally selected clipped gamma,
pathwise balanced eta, and generated trajectory measure.

Local APIs/imports are the raw, eta-tuned, gamma-characterized, and explicit
off-bad pathwise theorems; the pathwise explicit-tuning theorem;
`Exp3BernsteinAllHorizon`; clipped-rate positivity and stability;
`sampledPredictable_trivialRealizedRegret_tail`; classical `if`/`by_cases`;
ENNReal addition order; and the generated regret and sparsity-failure events.
The proof route invokes the refined off-bad theorem in the true branch and
rewrites the threshold to `T+1` in the false branch, where
`regretBad \ sparsityBad ⊆ regretBad` feeds the strict tail under the identical
measure. The residual endpoint then adds the common bad set once.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and natural sparsity; `0<delta<=1`; and the exact internally tuned
failure-event bound for epsilon. Eta, gamma, and regime selection are
internal. No caller horizon inequality, global `K*T` Markov envelope, `K^2`
mixed numerator, polynomial `1/delta`, event measurability, restricted
measure, universal/a.e. sparsity cap, `S<=K`, epsilon positivity,
independence, stationarity, countability, supplied integrability, or new law
transport is required.

Retrieval uses the pathwise explicit-gamma row, the generic Bernstein
all-horizon fallback, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`MLIB-ORDER-ALGEBRA`, adversarial finite/Auer EXP3, and inspiration-only
tail/potential weapons. Status is `leanCompiled`, root imported,
focused/root and `Tests.Basic` built, and externally canaried at the practical
all-horizon theorem. This fixed-comparator surface is consumed by the finite
best-supported-arm single-charge theorem below.

Failure policy: all positive horizons are covered without reintroducing the
old Markov scale, but the complementary threshold is deliberately coarse
`T+1`. The refined branch remains armwise aggregate and uses bounded realized
deviation. Sharp active clipping, general Freedman, anytime control, and ideal
EXP3.P remain separate theorem routes.

## EXP3 Probabilistic-Sparsity Pathwise-Variance Best Arm All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-PATHWISE-VARIANCE-PROBABILISTIC-SPARSITY-BEST-ARM-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityBestArmAllHorizon`.
It defines the hindsight best supported-arm cumulative predictable loss as
the `Finset.inf'` over the nonempty supported-arm set and proves that the
corresponding regret event is exactly the existential finite union of the
fixed-comparator events.

The confidence schedule remains armwise `delta/K`, but the common
sparsity-failure event is no longer union-bounded once per arm. New off-bad
theorems are compiled at the raw pathwise-variance, eta-tuned,
gamma-characterized, fully explicit, and all-horizon fixed-comparator layers.
The best-arm off-bad theorem unions only
`comparatorRegretBad \ sampledPredictableSparsityFailure`, yielding
`ofReal(delta)`. The strengthened residual then adds the common bad set once:
`ofReal(delta) + mu(sampledPredictableSparsityFailure)`. Its practical
consumer assumes the exact same generated measure satisfies
`mu(sampledPredictableSparsityFailure) <= ofReal(epsilon)` and concludes
`ofReal(delta) + ofReal(epsilon)` for every positive horizon. The previous
`K*mu(bad)` and `epsilon/K` theorems remain as compatibility APIs.

Local APIs/imports are the full fixed-comparator off-bad transport chain;
`Finset.inf'_le_iff` and `Finset.inf'_le`; `Set.diff` and finite-iUnion
membership; `measure_biUnion_finset_le`, `measure_mono`, and
`measure_union_le`; finite-sum comparison and constant-sum APIs; ENNReal
`ofReal` division and multiplication cancellation; finite casts; and order
algebra. The proof route rewrites the best-loss event as existence of a
supported comparator, proves `0<delta/K<=1`, distributes removal of the common
bad set through the finite comparator union, invokes the same internal
eta/gamma/generated measure for every arm, normalizes
`K*ofReal(delta/K)=ofReal(delta)`, and finally covers the full event by its
off-bad part union the common bad set.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; positive horizon and sparsity;
`0<delta<=1`; and the unscaled same-measure failure bound for the practical
endpoint. Eta, gamma, the best-arm infimum, and regime selection are internal.
No caller comparator, caller horizon inequalities, epsilon/K calibration,
global `K*T` Markov envelope, `K^2` mixed numerator, polynomial `1/delta`,
event measurability, restricted measure, universal/a.e. sparsity cap, `S<=K`,
epsilon positivity, independence, stationarity, countability, supplied
integrability, or new law transport is required.

Retrieval uses the fixed-comparator pathwise all-horizon row,
`MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
adversarial finite/Auer EXP3, and inspiration-only tail/potential weapons.
Status is `leanCompiled`, root imported, focused/root and `Tests.Basic` built,
and externally canaried at the single-charge practical best-arm theorem.

Failure policy: this closes the finite hindsight best-supported-arm gap, not a
stochastic-mean or first-order best-arm theorem. Single charging of the common
sparsity-failure event is now closed, but `delta/K` still introduces the
expected logarithmic arm-count cost and the complementary threshold remains
coarse `T+1`. Sharp active clipping, general Freedman, anytime control, and
ideal EXP3.P remain separate theorem routes.

## EXP3 Probabilistic-Sparsity Realized Markov Eta Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityTuning`.
It defines the honest global Markov threshold
`v=((1/(gamma/K))*(K*T))/(delta/5)`, the complete Hedge scale
`S*T+sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta/5)`,
and the internal learning rate `eta=sqrt(log K/scale)`.

The module proves positivity of `v`, the scale, and eta; the exact identity
`eta^2*scale=log K`; and, under `gamma<=1/2`, the bound
`entropy+stability<=3*sqrt(log K*scale)`. Unfolding the raw and tuned budgets
then gives
`sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold`.
The residual theorem has failure
`ofReal(delta)+mu(sparsityFailure)` under the exact internally eta-tuned
generated measure. Its practical consumer assumes the same measure gives
`mu(sparsityFailure)<=ofReal(epsilon)` and concludes
`ofReal(delta)+ofReal(epsilon)`.

Local APIs/imports are the probabilistic-sparsity residual module;
`sampledPredictableGlobalVarianceMeanBudget`;
`sampledMixedSquaredPredictableVarianceRadius`; the raw generated tail;
`Real.log`/`Real.sqrt` positivity and square identities; finite-cardinality
casts; field/ring normalization; nonlinear and linear arithmetic;
`measure_mono`; and ENNReal addition order. The proof route balances eta
against the complete global-variance scale, proves raw-budget containment
under the identical generated measure, and consumes the exact failure-event
bound without changing its measure.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
`0<gamma<=1/2`; predictable measurable `[0,1]` losses; a supported comparator;
positive horizon, sparsity, and delta; and, for the epsilon theorem, the exact
internally tuned generated-measure sparsity-failure bound. Eta is internal.
No caller eta, universal/a.e. sparsity cap, `S<=K`, `epsilon>=0`, `delta<=1`,
independence, stationarity, countability, supplied integrability,
event-measurability premise, or new law transport is required.

Retrieval uses the probabilistic-sparsity residual and pathwise eta-tuning
rows; `MLIB-REAL-LOG-SQRT`, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `SCN-ADVERSARIAL-FINITE`,
Auer EXP3, and inspiration-only tail/potential weapons. Status is
`leanCompiled`, root imported, focused/root built, and externally canaried at
the eta-tuned `delta+epsilon` theorem in `Tests.Basic`.

Failure policy: eta tuning is closed against the global `K*T` Markov envelope
and is consumed by the explicit-gamma route below. Markov remains polynomial
in `1/delta`; all-horizon fallback, sharper decomposed or exponential
overflow, best-arm first-order conversion, general Freedman, anytime control,
and ideal EXP3.P remain open.

## EXP3 Probabilistic-Sparsity Realized Markov Explicit Tuning

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-EXPLICIT-TUNING`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityExplicitTuning`.
The global Markov budget is proved equal to
`5*K^2*T/(gamma*delta)`. Consequently the schedule uses the new fifth-root
component
`(5*K^2*log(K)^2*log(5/delta)/(delta*T^3))^(1/5)` together with the sparse
arm square root, Bernstein cube root, and realized-deviation square root.
Gamma is their clipped maximum and eta remains the exact
probabilistic-sparsity balanced learning rate.

Four explicit horizon inequalities make clipping inactive and provide
`0<gamma<=1/2` plus the quadratic, fifth-power, cubic, and realized quadratic
dominance contracts. The module proves the mixed-square radius bound, reduces
the complete tuned threshold to `14*gamma*T`, and obtains both
`delta+mu(sparsityFailure)` and `delta+epsilon` generated tails. The epsilon
premise is stated under the exact internally eta/gamma-tuned measure used by
the conclusion.

Local APIs/imports are the probabilistic-sparsity eta-tuning module; the
pathwise explicit-tuning power/root utilities; global variance mean and
mixed-square radius; Bernstein and realized radius dominance lemmas;
`Real.log`, `Real.sqrt`, and `Real.rpow`; finite casts; field/ring/nonlinear
arithmetic; `measure_mono`; and ENNReal addition order. The proof route is:
normalize the global budget, control the log-weighted radius, derive the
`14*gamma*T` gamma-characterized theorem, prove the clipped schedule
contracts, and instantiate the same-measure residual theorem.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; four transparent large-horizon
inequalities; and the exact generated-measure failure bound for the epsilon
endpoint. Eta and gamma are internal. No universal/a.e. support cap, `S<=K`,
epsilon positivity, independence, stationarity, countability, supplied
integrability, event-measurability premise, or new law transport is required.

Retrieval uses the probabilistic eta-tuning and pathwise explicit-gamma rows;
`MLIB-REAL-LOG-SQRT`, `MLIB-EXP-LOG-INEQUALITIES`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the fully explicit `delta+epsilon` theorem.

Failure policy: explicit eta/gamma tuning is closed in the stated
large-horizon regime and is consumed by the all-horizon wrapper below. The
global envelope costs `K^2` in the fifth-root numerator and polynomial
`1/delta`; the theorem remains armwise aggregate. Do not claim pathwise
sparse variance, sharp active clipping, best-arm first-order conversion,
exponential/self-normalized overflow, general Freedman, anytime control, or
ideal EXP3.P.

## EXP3 Probabilistic-Sparsity Realized Markov All Horizon

`EXP3-MIXED-SQUARE-PREDICTABLE-VARIANCE-SPARSE-LOSS-REALIZED-MARKOV-PROBABILISTIC-SPARSITY-ALL-HORIZON`
now compiles in
`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityAllHorizon`.
The named regime packages the same four explicit horizon inequalities. The
new threshold selects the refined `14*gamma*T` branch when they hold and the
strict `T+1` zero-probability branch otherwise, using exactly the same
internally clipped gamma, balanced eta, and generated trajectory measure.

The residual theorem proves
`mu(regret >= threshold) <= ofReal(delta) + mu(sparsityFailure)` for every
positive horizon. The practical endpoint consumes
`mu(sparsityFailure)<=ofReal(epsilon)` under that identical measure and
returns `ofReal(delta)+ofReal(epsilon)`. No caller-supplied regime proof is
required.

Local APIs/imports are the probabilistic explicit-tuning module;
`Exp3BernsteinAllHorizon`; clipped-rate positivity and stability;
`sampledPredictable_trivialRealizedRegret_tail`; classical `if`/`by_cases`;
ENNReal addition order; and generated regret/failure events. The proof route
splits on the named condition, invokes the explicit residual theorem in the
positive branch, and rewrites to `T+1` before applying the strict trivial tail
in the negative branch.

Regularity contracts are a probability prior; Standard Borel nonempty
Env/Action; measurable action singletons; decidable arms with `K>=2`;
predictable measurable `[0,1]` losses; a supported comparator; positive
horizon and sparsity; `0<delta<=1`; and the exact internally tuned
generated-measure failure bound for the epsilon theorem. Eta, gamma, and
regime selection are internal. No universal/a.e. support cap, caller horizon
inequalities, `S<=K`, epsilon positivity, independence, stationarity,
countability, supplied integrability, event-measurability premise, or new law
transport is required.

Retrieval uses the probabilistic explicit-gamma and pathwise all-horizon rows,
the generic Bernstein all-horizon fallback, `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
`SCN-ADVERSARIAL-FINITE`, Auer EXP3, and inspiration-only tail/potential
weapons. Status is `leanCompiled`, root imported, focused/root built, and
externally canaried at the all-horizon `delta+epsilon` theorem.

Failure policy: every positive horizon is covered, but the complementary
branch is deliberately coarse `T+1`. The refined branch still pays `K^2`,
polynomial `1/delta`, armwise aggregate loss, and bounded realized deviation.
Do not claim sharp active clipping, pathwise sparse variance, best-arm
first-order conversion, stronger overflow, general Freedman, anytime control,
or ideal EXP3.P.

## EXP3 Bernstein-Square Finite Best Arm

`EXP3-MIXED-SQUARE-BERNSTEIN-REALIZED-BEST-ARM-ALL-HORIZON` now compiles.
The shared `Exp3BestArm` module isolates the `Finset.inf'` cumulative-loss
definition and proves that the best-arm regret event is the finite union of
fixed-comparator events. The new theorem applies the compiled all-horizon
Bernstein-square tail at `delta/K` for each supported arm under one common
eta/gamma/generated measure. `measure_biUnion_finset_le` and the ENNReal
identity `K*ofReal(delta/K)=ofReal(delta)` yield a total failure bound
`ofReal(delta)`.

The endpoint needs a probability prior, Standard Borel nonempty spaces,
measurable action singletons, decidable arms with `K>=2`, predictable
`[0,1]` losses, positive horizon, and `0<delta<=1`. It needs no comparator,
caller regime proof, sparsity assumption, event-measurability premise,
integrability premise, or new conditional-law transport. The module is root
imported and externally instantiated in `Tests.Basic`.

This closes finite hindsight best-supported-arm conversion for the fixed-tilt
Bernstein route. It does not remove the `delta/K` logarithmic arm-count cost,
the coarse `T+1` fallback, or bounded-loss Hoeffding/Azuma realized deviation.
Random predictable quadratic variation, general Freedman, anytime control,
stochastic-mean/first-order regret, sharp clipping, and ideal EXP3.P remain
open.

## Expected Gate-Open History-Adaptive Corruption All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES`
is `leanCompiled` in
`TsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw`. Its Lean-facing
corruption scalar is
`sum_(t<T+1) sum_(a!=best) integral p_t(a) *
(abs shift_t(a) + abs shift_t(best))`, evaluated under the generated
trajectory law. Unlike the previous envelope budget, a closed measurable gate
contributes zero; an open-gate arm is weighted by its conditional selection
probability and contributes zero when that probability is zero.

The local APIs expose the realized shift selected from pre-action finite pair
history, its measurability and envelope domination, the exact clipping-based
actual/reference gap deviation, automatic `p * deviation` integrability,
budget nonnegativity, and expected-budget domination by the deterministic
envelope budget. A generic reference-gap self-bounding theorem now accepts a
sample-dependent deviation and retains the action probability inside the
integral. The finite-arm IID wrapper reuses the existing IID-prefix
factorization and uncorrupted expected-gap law, then feeds the resulting
self-bound into the compiled logarithmic and refined consumers. The final
theorem selects the refined branch only when a suboptimal arm exists and the
expected-corruption compact window holds, then uses the logarithmic branch
otherwise; a thin wrapper instantiates arbitrary measurable history-arm-gated
boosts.

Regularity contracts remain probability arm laws, a.e. reward support in
`[0,1]`, exact means, an all-time measurable predictable source, finite
horizon, positive non-best gaps, and gaps at most one. These gap contracts are
vacuous for `K=1`; the public all-regimes theorem no longer requires a
nonempty suboptimal set, while the refined child theorem retains that internal
premise. The `Fin 1` envelope simplifies to `1 + log(T+1)`. No caller integrability,
independence, deterministic gate-open count, free corruption scalar, or scalar
window proof is added. Retrieval evidence is the compiled reference-gap,
IID-prefix, logarithmic, and refined-window routes; Mathlib finite sums,
Bochner integrals, kernels, independence, `Preorder.measurable_frestrictLe`,
`Integrable.of_bound`, and `integral_mono_ae`; and both Tsallis-INF paper cards.
The paper cards remain evidence, not local proofs. Failure policy: predictable
expected gate-open corruption is closed. Current-action/nonpredictable gates,
raw or latent reward-law corruption, paper-sharp constants, and complete
Tsallis-INF remain open. Horizon-local source contracts compile downstream.

## Horizon-Local Expected-Corruption All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-HORIZON-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES`
is `leanCompiled` in
`TsallisFiniteArmIIDHorizonHistoryAdaptiveExpectedCorruptedRewardLaw`. Its
source carries the initial shift/envelope and exactly `Fin horizon` successor
shift, joint history-arm measurability, envelope, nonnegativity, and absolute
bound witnesses. Thus round zero and successor rounds `n+1` for `n<horizon`
are covered, with no post-horizon regularity contract.

The proof constructs an all-time source by preserving every used shift and
envelope and setting both to zero when `horizon<=n`. On-horizon and
off-horizon simp lemmas expose this transport. The named loss, expected budget,
and all-regime bound are definitions over that extension, so the final theorem
uses exactly the parent generated-policy
`sum_(t<T+1) sum_(a!=best) E[p_t(a)(|shift_t(a)|+|shift_t(best)|)]`
quantity and its existing refined/log selector; it does not replace the budget
by the deterministic envelope.

Required caller contracts are probability arm laws, a.e. `[0,1]` raw rewards,
exact means, the finite source witnesses, positive non-best gaps, and gaps at
most one. `horizon=0` has only initial data, and `K=1` remains supported. No
new law transport, integrability, nonempty-suboptimal, free corruption, or
scalar-window premise is introduced. Retrieval evidence is the compiled
all-time expected-corruption leaf, `Fin`, finite sums/integrals, probability
kernels/independence, and the two Tsallis-INF paper cards. Failure policy:
horizon-local predictable corruption is closed; current-action/nonpredictable
or raw/latent-law corruption, paper-sharp constants, and complete Tsallis-INF
remain open.

## Square-Root Schedule Self-Bounding Optimization

`TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-OPTIMIZATION` is `leanCompiled` across
`BanditRLProof.TsallisScheduledSelfBoundingOptimization` and
`BanditRLProof.TsallisSqrtScheduleSelfBoundingOptimization`. The route now
splits finite times by the exact active quadratic threshold, derives a
prefix/suffix form from one cutoff certificate, and consumes the refined
generated stability/penalty bound. It deliberately does not use the coarse
terminal-potential interpolation base, whose square-root-schedule term would
remain of order `sqrt(T)`.

For `A=5*(1+lambda)` and
`R=sum_(a!=best) 1/(lambda*gap(a))`, the compiled endpoint replaces the two
time sums by an active term
`2*A*sqrt(K-1)*sqrt(cutoff)-cutoff*(K-1)/R` and a tail term
`(A^2/4)*R*log((T+1)/cutoff)`, in addition to the harmonic base and
`lambda*C`. The proof uses `AntitoneOn.sum_le_integral_Ico`, `integral_inv`,
finite-sum algebra, and local square-root schedule identities.

Regularity requires positive suboptimal gaps, a nonempty suboptimal arm set,
`lambda in (0,1]`, `0<cutoff<=T+1`, the explicit cutoff threshold, and the
terminal self-bound. Retrieval evidence includes the compiled constrained
quadratic and refined penalty leaves, Mathlib finite sums and log/sqrt APIs,
and Masoudian--Seldin (2021) as route evidence only. Failure policy: the
finite-time split and cutoff/log theorem are closed; constructing a useful
natural cutoff and optimizing it jointly with `lambda` and corruption remain
open, so the final paper endpoint is not yet established.

### Discrete cutoff and `lambda = 1` endpoint

`TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-FLOOR-TUNING` is now `leanCompiled` in
`BanditRLProof.TsallisSqrtScheduleSelfBoundingTuning`. Mathlib's natural-floor
APIs prove the factor-two sandwich needed to replace the continuous threshold
by a positive finite-time cutoff. The fixed-`lambda` generated theorem removes
the caller cutoff, and the `lambda=1` corollary identifies
`q=25*S^2/(K-1)` and proves the explicit
`C+100*S+25*S*log(2*(T+1)*(K-1)/(25*S^2))` bound in the branch
`1<=q<=T+1`.

Regularity and failure policy remain theorem-facing: generated trajectory
measurability/probability, positive suboptimal gaps, a nonempty suboptimal set,
the terminal self-bound, and the large-horizon threshold branch are explicit.
The ordinary corruption theorem is closed for `lambda=1`; the refined
square-root-in-`C` theorem is not. Its exact remaining scalar obligation is
the paper's `W_-1` optimizer, or an equivalent convex-root existence and bound
over the stated corruption range. No Lambert W definition or theorem is
available in the pinned Mathlib source tree.

### Scalar beta root existence

`TSALLIS-SELF-BOUNDING-BETA-ROOT` is now `leanCompiled` in
`BanditRLProof.TsallisSelfBoundingBetaRoot`. It defines
`g(beta)=C*S/scale*beta-log(beta)-1` and uses Mathlib's
`intermediate_value_Icc` to prove a root exists in `[1,scale/S^2]` under the
paper's explicit corruption window. The Lean statement retains positive
`scale` and `S`, `1<=scale/S^2`, `C*S<=scale`, and
`S*(log(scale/S^2)+1)<=C`; continuity follows from
`Real.continuousOn_log` because every beta in the interval is positive.

The follow-up `TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-TUNING` leaf is now
`leanCompiled` in `TsallisSqrtScheduleSelfBoundingRefinedScalar` and
`TsallisSqrtScheduleSelfBoundingRefinedTuning`. Auditing the compiled floor
theorem's amplitude `5*(1+lambda)` changes the locally valid equation to
`C*S/scale*beta-log(beta)-2=0`, with beta in
`[2,scale/(25*S^2)]`. An elementary inequality
`(sqrt(w)-1)^2 <= w-log(w)-1` replaces Lambert W and gives the quantitative
weight bound needed for `alpha=sqrt(25*S^2*beta/scale)` and
`lambda=alpha/(2-alpha)`. The exact threshold becomes `2*(T+1)/beta`.

The generated endpoint now compiles with bound
`1+log(T+1)+10*sqrt(C*S)*(2+sqrt(log(scale/(C*S))+1))` under the explicit
scalar window, generated-law regularity, positive-gap, and terminal self-bound
contracts. A concrete history-adaptive model consumer and its compact-window
wrapper now compile downstream. The paper's ideal `-1` equation and sharper
constants, complementary corruption regimes, stronger corruption models, and
the complete Tsallis-INF theorem remain open.

## EXP3 Sparse Double Pathwise Variance

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsity`
now compiles. The Lean-facing endpoint replaces the fixed realized-deviation
proxy by the exact selected-loss predictable variance. On the
sparsity-good event, the mixed-square variance budget is
`(1/(gamma/K))*(S*T)` and the realized selected-loss variance budget is
`S*T`. The corrected small-loss assembler also uses `S*T`, rather than
`K*T`, as the predictable mixed-square mean budget. Its raw Hedge scale is
therefore `S*T + sampledMixedSquaredPredictableVarianceRadius
((K/gamma)*S*T) (delta/4)`, plus the exact realized radius.

The supporting route is also compiled. `selectedLossCenteredSecondMoment`
has a finite-action MGF compensation and an armwise loss-mass upper bound.
The generic conditional wrapper explicitly requires joint
`(history,action)` loss measurability and a global `[0,1]` bound, because
`BoundedMeasurableLossWithProbabilityFloor` only provides fixed supported-arm
measurability. Generated zero/successor action laws instantiate the wrapper;
the deterministic-feedback AE identity transports selected loss to realized
loss. The shifted variance process is predictable, and the fixed-MGF
martingale assembler yields radius
`2*sqrt(V*log_+(1/delta))+log_+(1/delta)`.

The final theorem intersects the mixed and realized variance-good events.
Both satisfy a pointwise budget-or-`sampledPredictableSparsityFailure`
alternative. The predictable three-event branch is restricted by the bad-set
complement, the realized-deviation tail remains global, and the outer joint
regret event is restricted by that same complement. The residual theorem then
adds the common set exactly once, and the practical consumer returns
`ofReal(delta)+ofReal(epsilon)` from the exact same-measure failure premise.
The modules are root imported, focused/root built, and externally canaried.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityTuning`
now closes eta tuning. It reuses the compiled sparse scale and learning rate
`eta=sqrt(log K / scale)`, bounds entropy plus stability by
`3*sqrt(log K*scale)` under `K>=2` and `0<gamma<=1/2`, and retains
`sampledRealizedPredictableVarianceRadius (S*T) (delta/4)` unchanged. Its
off-bad, residual, and practical `delta+epsilon` endpoints all use the same
internally tuned generated measure.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityExplicitTuning`
now closes large-horizon gamma scheduling. It augments the old sparse
pathwise raw schedule by
`sqrt(S*log(4/delta)/T)` and clips the maximum at `1/2`. The four named
contracts are
`4*S*log K<=T`,
`32*K*S*log(K)^2*log(4/delta)<=T^3`,
`8*K*log(4/delta)<=T`, and
`4*S*log(4/delta)<=T`. They imply the quadratic, fifth-power, cubic, and
selected-loss quadratic dominance conditions. In particular,
`sampledRealizedPredictableVarianceRadius(S*T,delta/4)<=3*gamma*T`,
so the full tuned threshold is at most `16*gamma*T`.

The module exposes gamma-characterized and fully clipped off-bad, residual,
and practical `delta+epsilon` endpoints under one identical internally
eta/gamma-tuned generated measure. It is root imported, focused-built, and
externally instantiated at all three surfaces in `Tests.Basic`.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityAllHorizon`
now closes the all-horizon fixed-comparator presentation. Its named condition
packages those same four contracts. The threshold is the exact explicit
branch, hence at most `16*gamma*T`, when the condition holds and strict
`T+1` otherwise. Both branches retain the same internal eta, clipped gamma,
and generated trajectory measure.

The off-bad theorem proves `mu(regretBad\sparsityFailure)<=ofReal(delta)`;
the residual adds the common bad event once; and the practical endpoint uses
the exact same-measure premise to return `ofReal(delta)+ofReal(epsilon)`.
The module is root imported, focused-built, and externally instantiated at
all three surfaces in `Tests.Basic`.

`BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now closes finite hindsight best-supported-arm transport. Its threshold calls
the exact fixed-comparator all-horizon threshold at `delta/K`. The shared
`Exp3BestArm` order lemma rewrites best-arm regret as a finite comparator
union; each off-bad tail uses the same eta, gamma, and generated measure;
finite-union and ENNReal cancellation produce total confidence `delta`.

The common sparsity-failure set is removed before the union, then added once.
Consequently the residual is `ofReal(delta)+mu(bad)` and the practical theorem
needs only `mu(bad)<=ofReal(epsilon)`, not epsilon/K. The module is root
imported, focused/root and `Tests.Basic` built, and externally instantiated at
off-bad and practical surfaces.

Failure policy: eta, explicit gamma, every-positive-horizon coverage, finite
hindsight best-arm transport, and single common-bad charging are closed for
the exact double-variance route. The `delta/K` schedule retains log-K cost and
the fallback remains deliberately coarse strict `T+1`. This is not
stochastic-mean or first-order regret, sharp clipping, general Freedman,
anytime/self-normalized control, or ideal EXP3.P.

## Predictable-Compensator Fixed-Tilt Tail

`BanditRLProof.ConcentrationFixedMGF` now compiles
`measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`. Its event
retains a random cumulative compensator:
`threshold<=sum Y` together with `sum V<=varianceBudget` has probability at
most `ofReal(exp(-tilt*threshold+varianceCoeff*varianceBudget))` whenever the
compensated increments have unit-tilt zero-budget initial and successor
conditional-MGF witnesses.

The local route is the existing fixed-tilt MGF sum theorem followed by one
real-measure/ENNReal conversion and a monotone event inclusion. Required
regularity is Standard Borel, finite zero-or-probability measure, strong
adaptedness, source MGF integrability, and nonnegative coefficients. No
independence or deterministic variance cap is introduced.

The existing realized predictable-variance EXP3 fixed-tilt endpoint was
refactored to consume this leaf at coefficient `tilt^2`, and `Tests.Basic`
contains a direct external canary. Remaining concentration gaps are one-step
MGF construction in new models, mixture/maximal tilts, and
maximal/anytime/self-normalized control; this theorem alone is not general
Freedman.

## Quadratic Fixed-MGF Delta Tail

`BanditRLProof.ConcentrationQuadraticFixedMGF` now proves
`measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`.
For positive `c`, `V`, `cap`, and `delta`, a fixed-tail family
`P(radius<=D, W<=V)<=exp(-tilt*radius+c*tilt^2*V)` for every
`tilt in [0,cap]` yields probability at most `ofReal(delta)` at radius
`2*sqrt(c*V*log_+(1/delta))+log_+(1/delta)/cap`.

The proof uses the migrated exact quadratic tilt optimizer and a separate
`exp(-log_+)` calibration valid without `delta<=1`. The realized selected-loss
and mixed-square predictable-variance EXP3 delta theorems now call this API,
so the abstraction has two compiled consumers. A direct external canary is in
`Tests.Basic`.

Regularity at this layer is deliberately minimal: measurable ambient space,
positive scalar contracts, and the fixed-tail family. Probability,
filtration, adaptedness, conditional MGF, bounded increments, and law
transport remain obligations of each producer. Quadratic fixed-horizon
optimization is closed; one-step MGF production, maximal/anytime mixtures,
self-normalized optional stopping, and a general Freedman theorem remain open.

## Finite-Prefix Quadratic Maximal Tail

`BanditRLProof.ConcentrationQuadraticMaximal` now proves
`measure_biUnion_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail`.
For a nonempty finite `times`, every event is assigned confidence
`delta/times.card`; the compiled quadratic optimizer supplies its bound, the
Mathlib-backed finite outer-measure union sums them, and ENNReal cardinality
cancellation returns `ofReal(delta)`.

`BanditRLProof.Exp3RealizedPredictableVarianceMaximal` instantiates the route
for every `t<horizon`, hence prefix lengths `1` through `horizon` inclusive,
using the existing
realized selected-loss fixed-tilt producer and one common predictable-variance
budget. Both generic and generated-trajectory theorem surfaces have external
`Tests.Basic` canaries.

The generic contracts are measurable ambient space, decidable nonempty finite
index set, positive scale/budget/cap/delta, and fixed-tail families. The EXP3
consumer adds the probability prior, Standard Borel spaces, finite action-law
regularity, legal exploration, and predictable `[0,1]` losses. No event
measurability, independence, stationarity, `delta<=1`, or new law assumption
is added. The result has an equal-share log-cardinality cost and must not be
reported as Ville/Doob, mixture, optional-stopping, horizon-free anytime,
self-normalized, or general Freedman concentration.

## Practical selected-policy finite-sum concentration update

The `COND-EXPECT-REWARD` route now has a compiled arbitrary-ambient probability
consumer from the policy-selected reward-coordinate law to a fixed-horizon
centered-reward sum tail:
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_tail_ennreal_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
It closes the analytic assembly from generated-history adaptedness and the
existing practical one-step conditional MGF to Mathlib's finite-sum
Azuma-Hoeffding API. Contracts remain explicit: probability measure, Standard
Borel sample space, countable measurable actions with measurable singletons,
timewise measurable rewards, measurable context/state/mean, raw/mean ranges,
centered kernel laws, selected-history variance ceilings, and the trim-a.e.
selected reward map law at every time.

Remaining gaps are model-side production of that selected conditional reward
law and variance domination, plus arm-wise empirical-mean/confidence and final
bandit consumers. This result covers centered rewards `1..n-1`; it does not
close confidence inversion, anytime concentration, or regret.

## Two-sided delta-confidence update

The generic concentration layer now includes the absolute-deviation ENNReal
tail, the `sqrt(2 V log(2/delta))` radius and algebraic calibration, and the
delta-valued fixed-horizon theorem for strongly adapted conditional
sub-Gaussian processes. The practical selected-policy endpoint consumes the
compiled conditional reward-law producer and returns the matching absolute
centered-sum event bound by `ENNReal.ofReal delta`.

Regularity is not hidden: finite/probability measure instances, Standard Borel
sample space, StronglyAdapted increments and conditional MGFs at the generic
layer; plus countable measurable actions, selected reward map laws,
raw/selected-mean ranges, centered kernel law, selected-history ceilings,
positive total ceiling variance, and `0 < delta <= 1` at the practical layer.
The union is an outer-measure bound, so event measurability is not added.
Arm-wise empirical means, random pull-count indexing, anytime/self-normalized
concentration, and final bandit/RL theorems remain open.

## Fixed-sample average delta-confidence update

Closed locally: deterministic positive-denominator sum-to-average event
transport, the generic strongly-adapted conditional sub-Gaussian average
theorem, and its full practical selected-policy reward-law instantiation. The
practical event averages exactly the successor rewards `1..m` by using
`range (m+1)` with a zero initial slot and divisor `m`; generic and practical
external canaries compile.

Regularity remains explicit: `m>0`, positive total proxy variance, and
`0<delta<=1`, in addition to the prior probability/Standard-Borel,
adaptedness/conditional-MGF, selected conditional reward law, measurable
surfaces, raw/mean ranges, centered kernel law, and selected-history variance
contracts. No event measurability or independence is introduced. Still open:
arm-restricted empirical means, random pull-count transport, confidence
sequences, anytime/self-normalized/Freedman bounds, and regret consumers.

## Product arm-stream fixed-sample arm confidence

Closed locally: the independent two-sided finite-sum and exact `range k`
average delta theorem, plus the stationary product arm-stream specialization
for a single arm's empirical mean. The concrete theorem derives aggregate
proxy positivity from `k>0` and `sigma2!=0`; generic and model-level external
canaries compile.

Contracts are finite measure and `iIndepFun` at the generic layer; Markov arm
kernel, stationary double-`infinitePi` arm-stream law, centered per-coordinate
`HasSubgaussianMGF`, `k>0`, nonzero proxy, and `0<delta<=1` at the UCB layer.
No filtration, conditional expectation, Standard Borel, event measurability,
or caller-supplied total variance is added. Still open on this branch are
non-product/selected-policy arm-law transport and anytime/self-normalized
confidence. Adaptive pull counts are not open in the canonical UCB route:
they are handled separately by the existing peeling/index-tail theorem.

## Selected-policy fixed-arm masked concentration

Closed locally: `ProbabilityTheory.HasCondSubgaussianMGF.indicator` preserves a
conditional sub-Gaussian witness under an event measurable in the conditioning
sigma-algebra. The practical consumer proves the generated action at `i+1` is
measurable at `F_i`, constructs a strongly adapted fixed-arm masked centered
reward process, and proves
`ConditionalExpectationReward.armMaskedCenteredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

The result is for one fixed arm and one fixed horizon. It retains the full
selected reward-law, raw/mean range, centered-kernel, selected-history variance,
positive total proxy, and `0<delta<=1` contracts. Its proxy is the deterministic
full `varianceCeiling i`. Missing `F_i` predictability or selected-law transport
must remain an explicit blocker. The adjacent predictable-variance leaf now
provides a separate masked-proxy route rather than silently strengthening this
older theorem.

## Conditional sub-Gaussian predictable-variance tail

Closed locally: at a fixed tilt,
`ProbabilityTheory.HasCondSubgaussianMGF.indicator_compensated_hasCondMGFUpperBoundAt`
subtracts the quadratic proxy only on a conditioning-measurable mask. The
generic finite-sum theorem retains the random cumulative masked proxy in the
joint bad event, and
`Concentration.condSubGaussian_indicator_sum_abs_tail_predictableVariance_delta`
uses the quadratic fixed-MGF optimizer plus a two-sided union to obtain an
`ENNReal.ofReal delta` bound.

Contracts are a probability/Standard Borel ambient space, filtration,
conditioning-measurable masks, StronglyAdapted masked increments and proxy
process, successor conditional sub-Gaussian witnesses, fixed horizon, positive
deterministic variance budget, and positive delta. This is not maximal,
anytime, self-normalized, or general Freedman concentration; it neither proves
the proxy-budget event nor performs peeling over arbitrary variance budgets.
Exact Nat-count peeling now compiles in the downstream generic and
selected-policy rows.

## Selected-policy successor-arm empirical mean

Closed locally: `successorArmPullCount`, `successorArmRewardSum`, and
`successorArmEmpiricalMean` align coordinates `1..n-1` with the zero-initialized
masked process. The finite-sum identity rewrites that process as selected
reward sum minus realized count times a stationary arm mean, and
`Concentration.measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail`
performs positive random-denominator transport. The practical endpoint
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
is externally canaried.

The older endpoint retains stationarity of the fixed arm mean across all
context histories, `DecidableEq Action`, positive full-proxy, and
`0<delta<=1`; its radius is the full horizon proxy divided by realized count.

The count-adaptive exact-fiber endpoint now also compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
Under a constant selected-history ceiling `sigma2`, the masked proxy identity is
exactly `sigma2 * successorArmPullCount`. On the fiber where that count equals
`k>0`, the empirical-mean confidence radius therefore charges `k*sigma2`, not
the full horizon proxy. Its additional contracts are positive coerced `sigma2`
and positive `delta`; it does not require `delta<=1` or positive full-horizon
variance.

The finite random-count endpoint now also compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
The generic declarations
`Concentration.measure_positive_randomCount_event_le_sum_exactCount` and
`Concentration.measure_positive_randomCount_event_le_of_exactCount_uniform`
cover a positive count event by exact fibers without measurability assumptions.
Here `successorArmPullCount_le_horizon` supplies ceiling `n`, every fiber receives
confidence `delta/n`, and the final radius is evaluated at the realized count.
The total failure is `ENNReal.ofReal delta`.

Additional contracts are `n>0`; the previous uniform `sigma2`, stationary arm
mean, selected law, and `delta>0` contracts remain. This one-arm/one-horizon
theorem is now consumed by the simultaneous endpoint below.

The finite-arm/time endpoint now compiles:
`ConditionalExpectationReward.successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
Its event is indexed by `arms.product (Finset.range T)` and evaluates each pair
at positive horizon `i+1`. `successorArmEmpiricalMeanFiniteArmTimeConfidenceShare`
allocates `delta / |arms × range T|`; each event then uses the existing internal
count peeling. `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`
normalizes the outer family, so the complete union has mass at most
`ENNReal.ofReal delta`.

The additional contracts are an explicit nonempty arm `Finset`, `T>0`, and a
stationary mean for every candidate arm; the practical selected-law,
uniform-`sigma2`, positive-`sigma2`, and positive-`delta` assumptions remain.

The random-width UCB consumer now compiles in
`BanditRLProof.Algorithms.UCBConditionalRewardLaw`. The source structure
`UCB.SelectedPolicySuccessorInitializedScoreMaxSource` records a finite set of
post-initialization times, best/chosen arm membership, positive realized counts,
and pointwise maximality of `UCB.selectedPolicySuccessorIndexAt`. Outside the
simultaneous event,
`meanGap_le_two_radius_of_not_badEvent` applies the existing deterministic UCB
algebra at the sample-dependent radius. Consequently
`measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
bounds any charged large-gap selection by `ENNReal.ofReal delta`.

The adapter intentionally does not use `UCB.finiteHorizonConfidenceBadEvent`:
that older API has a sample-independent radius, whereas this theorem uses the
realized pull count. Its additional compatibility contract is `Action : Type`,
matching the current universe-0 UCB score algebra. Failure policy moves to
the generated-policy leaf below, which now closes source construction,
initialization, and expected pull-count transport. Closed-form threshold
selection, regret assembly, and maximal/anytime/self-normalized or general
Freedman control remain open.

## Generated selected-policy UCB count closure

Card `LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-RANDOM-WIDTH-PULLCOUNT` is now
`leanCompiled`. Its Lean surface constructs the finite-history policy,
generated action trace, pair-history reconstruction invariant, one-pass
initialization, positive-count schedule, and concrete initialized score-max
source. Exceeding a threshold `B` yields a selected post-initialization time
whose prior chosen-arm count is at least `B`; the previous random-width
large-gap theorem then supplies the tail.

The remaining radius algebra is explicit rather than abstract: with `L_T`
equal to `selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta`, the two
contracts are `32*sigma2*L_T < gap^2*B` and `4*L_T < gap*B`. They compile to
the high-probability count bound and, using a measurable bounded Nat
integration lemma, the ENNReal expectation bound `B + T*ofReal(delta)`.
Focused, root, and `Tests.Basic` builds pass. Retrieval evidence is local
compiled Mathlib-backed code through the prior large-gap, finite arm/time,
Finset pull-count, measure, integral, log, and sqrt APIs; theorem cards and
weapon-only entries are not proof evidence.

The closed-form integer threshold now compiles in the next leaf. The remaining
gap is regret assembly and concrete-model selected-law production, not policy
construction, threshold inversion, or expected-count transport.

## Explicit threshold and practical expected count closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-EXPECTED-PULLCOUNT`
is `leanCompiled`. The threshold is `Nat.ceil (max quadratic linear) + 1`, with
quadratic term `32*sigma2*L_T/gap^2` and linear term `4*L_T/gap`. `Nat.le_ceil`
and positive denominator transport establish both strict inequalities, so the
random-width radius inversion is fully internal.

A concrete-source large-gap producer now names the practical selected-law
instantiation that was previously hidden inside the threshold-parametric count
theorem. The final public theorem combines that producer with measurable Nat
count integration and yields the explicit-threshold ENNReal expected count
under the complete practical law surface. It requires a positive chosen-arm
gap but no external large-gap event, integer threshold, radius condition, or
numeric inequality.

Focused module, root, and `Tests.Basic` builds pass, and the declaration is
externally canaried. Retrieval evidence is local compiled code plus Mathlib
`Nat.ceil`, order/division, measure, and lower-integral APIs; theorem-card and
weapon-only text is not proof evidence. The finite-arm pseudo-regret consumer
now compiles in the next leaf.

## Practical selected-policy UCB pseudo-regret closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`
is `leanCompiled`. Its successor-action adapter maps generated coordinates
`1..T` onto pseudo-regret coordinates `0..T-1`, proves the corresponding
pull-count equality, and aligns the model's Real mean gap with its rational
`FiniteBanditModel.gap`.

The generic ENNReal assembly theorem uses the existing scalar pseudo-regret
pull-count identity, finite `lintegral` summation, constant multiplication, and
model gap nonnegativity. Only positive-gap arms require count bounds; zero-gap
terms disappear. The practical specialization supplies every such bound from
the explicit-threshold selected-law theorem and produces the finite sum of gap
times threshold plus gap times `T*ofReal(delta)`.

The full selected reward law, measurability, range, centered-kernel,
stationary-model-mean, positive uniform variance, probability/Standard-Borel,
positive horizon, and positive delta contracts remain explicit. Focused,
root, and `Tests.Basic` builds pass. Compiled local declarations and Mathlib
Finset/measure/lower-integral APIs are retrieval evidence; theorem cards and
weapon-only routes are not proofs. The closed gap is finite-arm ENNReal
pseudo-regret assembly including zero-gap arms. The textbook RHS simplification
now compiles downstream.

## Practical UCB textbook gap-sum closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET` is
`leanCompiled`. The one-arm route proves
`gap * threshold <= 32*sigma2*L_T/gap + 4*L_T + 2*gap`: it reuses the canonical
`Nat.ceil_lt_add_one` pattern, bounds the nonnegative `max` by the sum of its
branches, and normalizes positive-gap divisions. The ENNReal wrapper then
transports this Real inequality without an infinity side condition.

The finite consumer filters `Finset.univ` to positive model gaps. Zero-gap
arms are discharged from `FiniteBanditModel.gap_nonneg`; the original
`gap*T*ofReal(delta)` failure contribution is unchanged. The end-to-end
selected-law theorem composes this bound with the already compiled practical
pseudo-regret endpoint and exposes the textbook filtered finite sum directly.

Focused module, root, and `Tests.Basic` builds pass. Local compiled declarations
plus Mathlib ceil, order, field, Finset filter, and ENNReal cast APIs are the
retrieval evidence; theorem cards and weapon-only routes are not proofs. The
closed gap includes threshold removal, reciprocal-gap simplification, and
zero-gap filtering. Its UCB canonical-law specialization and reward-only
trajectory theorem now compile downstream.

## Canonical reward-only trajMeasure closure

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-CANONICAL-REWARD-TRAJMEASURE-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The module defines the generated-UCB reward-history step
kernel family, proves every member is Markov, exposes the corresponding
`Kernel.trajMeasure` and probability instance, packages the canonical
finite-pair selected-reward source, and exports the exact trim-a.e.
`historyFiltrationSucc` `condExpKernel.map` law.

The final canonical theorem consumes that law internally and applies the
already compiled practical textbook finite-sum endpoint. Its proof route is
the canonical trim selected-law theorem, comap-to-history-filtration source
transport, source projection, and practical pseudo-regret composition.
Required contracts are a probability initial reward law; measurable context,
state and mean; Markov reward kernel; centered reward-kernel law; stationary
model means; positive selected-history variance; `K,T>0`; `delta>0`; mean
range; and pointwise raw range.

Focused module, root, and `Tests.Basic` canaries are the local evidence, with
Mathlib kernel/trajectory/measure APIs as upstream evidence. The generated-UCB
canonical law premise is closed. The stronger centered-kernel endpoint below
also closes the obsolete pointwise `hraw` and mean-range surface.

## Centered-kernel no-range canonical closure

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. Audit of the old concentration chain showed that
`CenteredRewardKernelLaw` already contains the exact selected-law centered
integrability, zero integral, and sub-Gaussian MGF facts. The range source was
therefore redundant rather than a genuine support obligation.

The replacement route transfers the target-law MGF through the canonical
trim-a.e. selected reward-map identity, constructs the successor conditional
MGF under `historyFiltrationSucc`, masks by the predictable arm event, and
uses the random predictable proxy `sigma2 * successorArmPullCount`. Exact
positive-count confidence, finite count peeling, finite arms-times union,
generated-UCB large-gap control, explicit expected counts, pseudo-regret
assembly, and textbook threshold simplification all compile in one module.

The final canonical theorem requires only probability initial law, measurable
context and mean, `CenteredRewardKernelLaw`, stationary model means, positive
selected-history variance ceiling, positive `K,T`, and positive `delta`. It
has no raw or mean range, no support restriction, and no caller law premise.
Focused, root, and `Tests.Basic` builds pass; compiled declarations plus the
Mathlib conditional-MGF, predictable-variance, finite-union, and integration
APIs are direct evidence. This canonical ENNReal UCB textbook pseudo-regret
route is closed, and its Real/Bochner presentation is closed downstream.
Common bounded context-independent centered-kernel constructors also compile
downstream; no context-dependent, anytime/Freedman, or unrelated final theorem
is claimed.

## Canonical Real expectation closure

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The audit found no missing probabilistic leaf: the only gap
between the canonical ENNReal endpoint and a textbook Real expectation was
finite-horizon integrability plus finite ENNReal normalization.

`integrable_real_pullCount_of_measurable_action` now supplies the generic
bounded-measurable pull-count adapter under `IsFiniteMeasure`.
`integrable_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction`
combines it with the existing finite-arm pseudo-regret decomposition. The final
canonical theorem proves pointwise nonnegativity, applies
`ofReal_integral_eq_lintegral_ofReal`, consumes the prior centered-kernel
lintegral theorem, proves the positive-gap finite sum is finite, and converts
every sum/addition/product/`ofReal` term to the explicit Real expression.

The final API has no external integrability hypothesis and no `.toReal` RHS.
Its probability, measurability, centered-kernel, stationary-mean, variance,
horizon, and confidence contracts are unchanged. Focused and `Tests.Basic`
builds pass. The exact compiled declarations plus Mathlib Bochner integral and
ENNReal conversion APIs are direct evidence. This Real presentation gap is
closed and consumed by the bounded finite-arm route below.

## Bounded finite-arm law closure

Card
`LOCAL-LEAF-UCB-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The prior abstract final theorem required callers to provide
`CenteredRewardKernelLaw`, a measurable mean, a selected-history variance
ceiling, and a compatible canonical trajectory setup. For stationary bounded
finite-arm laws those obligations are now constructed internally.

The generic direct-subGaussian constructor derives centered integrability and
zero integral from the MGF witness plus the exact raw mean. The bounded
constructor derives the MGF through
`boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`. A separate strict-
positivity leaf closes the nondegenerate interval proxy obligation. The UCB
consumer then specializes to `Unit` context, constant model means and variance,
the context-independent arm-law kernel, and the default-arm initial law.

The final external contracts are per-arm probability measures, common
`lo < hi`, a.e. measurable reward casts, common a.s. interval support, exact
integrals equal to `model.mean`, a default arm, positive horizon, and positive
delta. No abstract centered law, selected law, trajectory law, variance bound,
or integrability witness remains. Focused and `Tests.Basic` builds pass, and
the card plus retrieval indexes record the older ETC constructor as discovery
evidence rather than a UCB dependency. This common-interval stationary finite-
arm UCB Real expected-regret route is closed and consumed by the armwise route.

## Armwise bounded finite-arm law closure

Card
`LOCAL-LEAF-UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The remaining unequal-range gap was not probabilistic: each
arm already had a bounded centered MGF, but UCB needed one positive deterministic
proxy. The new supporting leaves define that proxy as the finite supremum of
the armwise interval proxies, prove every arm is dominated by it, and prove it
strictly positive from `model.hK` and pointwise nondegenerate intervals.

`contextIndependentArmwiseBoundedCenteredRewardKernelLaw` packages the per-arm
bounded MGF witnesses without collapsing the ranges. The final theorem selects
the finite maximum internally and reuses the canonical Real theorem. Its only
external contracts are per-arm probability laws, per-arm measurable bounded
support with `lo arm < hi arm`, exact model means, a default arm, positive
horizon, and positive delta. No common range or caller variance ceiling remains.

Focused module and `Tests.Basic` builds pass. Exact declarations, `Finset.sup`,
`Finset.le_sup`, the Mathlib-backed bounded MGF wrapper, and the prior canonical
Real theorem are direct evidence. Armwise stationary bounded finite-arm UCB is
closed; context-dependent/nonstationary, anytime/Freedman, cross-toolchain, and
other algorithm routes remain separate.

## Direct sub-Gaussian finite-arm law closure

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The audit separates two obligations that bounded support had
previously discharged together: producing centered MGF witnesses and choosing
one deterministic positive UCB proxy. The new endpoint accepts the MGF
witnesses directly and computes the proxy as the finite supremum of their
armwise `NNReal` parameters.

The maximum-proxy leaves prove selected-arm domination with `Finset.le_sup` and
strict positivity from the existence of one positive proxy. The existing
context-independent direct constructor derives centered integrability and zero
integral from the MGF witness and exact mean. The final theorem then reuses the
canonical Real trajectory theorem with no support or range assumptions.

Focused, root, and `Tests.Basic` builds pass. Exact declarations,
`MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-FINSET-SUMS`, `Finset.sup`,
`Finset.le_sup`, and the canonical Real card are direct evidence. The stationary
finite-arm direct-subGaussian exact-max UCB route is closed. The positive-padded
theorem below closes all-zero-proxy/noiseless families. Context-dependent or
nonstationary rewards, anytime/Freedman, cross-toolchain import, and other
algorithms remain separate.

## Direct finite-arm all-zero proxy closure

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The tuning proxy is `max 1 finiteArmVarianceProxy`;
`le_max_right` preserves genuine-proxy domination and `le_max_left` supplies
strict positivity. This does not assert that an all-zero genuine maximum is
positive.

The resulting canonical Real endpoint removes the positive-member premise
while retaining exact means and original per-arm centered MGF witnesses. All
kernel, selected-law, trajectory, centering, and integrability obligations are
internal. The conservative padded bound is closed; sharper zero-width analysis
remains a separate optimization.

## Context-dependent bounded reward-kernel closure

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-BOUNDED-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The earlier canonical Real theorem already accepted an
arbitrary context-dependent centered reward kernel, but callers still had to
assemble `CenteredRewardKernelLaw` and its integrability/centering obligations.
The new algorithm-independent constructors close that gap for both direct
pointwise MGF witnesses and common bounded selected laws.

`centeredRewardKernelLaw_of_hasSubgaussianMGF` obtains centered integrability
from `HasSubgaussianMGF.integrable`, raw integrability by adding the mean, and
zero centered integral with `integral_sub`. The bounded constructor applies the
existing Mathlib-backed Hoeffding MGF wrapper at every context/action pair.
`RewardKernel.isProbabilityMeasure_apply` supplies the selected-law instances.

The UCB endpoint allows reward distributions to vary with context/action while
requiring exact stationary arm means and common nondegenerate support. It
constructs the interval proxy and every selected-law/trajectory/regularity
witness internally, then returns the explicit Real positive-gap textbook sum.
Context-dependent means are outside the stationary pseudo-regret contract;
context/action-dependent ranges, direct sub-Gaussian ceilings, nonstationary
regret, and anytime/Freedman routes remain open.

## Context-dependent direct sub-Gaussian reward-kernel closure

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The bounded route's generic direct-MGF constructor now feeds
a public canonical Real UCB theorem without passing an abstract
`CenteredRewardKernelLaw` through the theorem boundary.

The external probability contract is exact pointwise selected-law means equal
to `model.mean arm`, centered `HasSubgaussianMGF` witnesses with proxies
`varianceProxy ctx arm`, one positive global `sigma2`, and uniform domination
`varianceProxy ctx arm <= sigma2`. MGF regularity supplies centered
integrability; adding the mean supplies raw integrability; `integral_sub`
supplies zero centering. The canonical route constructs selected law and
trajectory law internally and returns the explicit Real textbook gap sum.

No bounded support, reward-range premise, context independence, caller
centered-law, selected-law transport, trajectory law, or integrability witness
remains. The caller ceiling is not an avoidable artifact: automatic maxima need
finite/compact/bounded context structure. The finite-context exact and padded
specializations below close finite automatic ceilings and all-zero proxy
families. Infinite compact/bounded contexts, context-dependent
means/nonstationary regret, and anytime/Freedman routes remain open.

## Finite-context automatic variance-ceiling closure

Card
`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-AUTOMATIC-CEILING-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. For `[Fintype Context]`, the algorithm-independent maximum
uses nested `Finset.univ.sup`; `Finset.le_sup` closes every context/action
domination obligation, and existence of one positive proxy closes the
canonical theorem's strict-positive `sigma2` contract.

The public specialization no longer accepts a caller ceiling. Its remaining
contracts are the finite measurable context, exact stationary selected-law
means, direct pointwise centered MGF witnesses, one positive proxy, and the
existing probability/horizon/delta assumptions. The positive-padded endpoint
below closes all-zero/noiseless proxies; infinite-context compactness or
boundedness machinery remains open.

## Finite-context all-zero proxy closure

Card
`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The new proxy is `max 1 finiteContextArmVarianceProxy`, so
`le_max_right` preserves domination and `le_max_left` supplies strict positive
Real coercion. This is conservative tuning, not a claim that a genuine zero
proxy is positive.

The resulting canonical Real UCB theorem has no proxy-positivity premise and
still derives centered law, selected-law transport, trajectory law, and
integrability internally. Finite-context all-zero handling is closed. Infinite
context and sharper zero-width/noiseless algorithm analysis remain distinct.
## Half-Tsallis Canonical Finite-Horizon Decomposition

`TSALLIS-HALF-CANONICAL-FINITE-HORIZON-DECOMPOSITION` is `leanCompiled` in
`BanditRLProof.TsallisFTRLFiniteHorizonSelection`.  The Lean-facing sequence
`Tsallis.halfTsallisCumulativeMinimizer` applies the fixed compact-simplex
minimizer choice to `FTRL.cumulativeLoss loss t`.  Its certificate theorem
discharges the full family of `t <= T` minimizer premises in
`Tsallis.cumulativeLinearLoss_sub_comparator_le_stability_add_powerSumPenalty`.
The resulting canonical theorem assumes only decidable equality, nonempty
finite arms, positive eta, an arbitrary deterministic Real loss sequence, and
a feasible comparator.

The successor wrappers prove both the raw cumulative-score equality and the
importance-weighted update equality.  The route uses the compiled existence
selector, `FTRL.cumulativeLoss_succ`, and the existing deterministic horizon
decomposition; no theorem card is treated as a local proof.  Focused/root and
`Tests.Basic` external calls compile.

Failure policy: this closes deterministic minimizer and horizon plumbing, not
the stochastic stability sum.  The one-step theorem averages over the sampled
action and its successor minimizer depends on that action, so it cannot be
summed pathwise.  `Classical.choose` is also not yet a measurable history
selector.  Conditional action-law/expectation transport, expected stability
assembly, self-bounding, tuning, and final Tsallis-INF regret remain open.

## Half-Tsallis Conditional Action Stability

`TSALLIS-HALF-CONDITIONAL-ACTION-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisFTRLConditionalStability`. Its generic Lean endpoint
identifies the regular conditional law of the sampled action with the finite
current half-Tsallis distribution, rewrites the conditional integral as the
finite sampling-law sum, applies the compiled current/update minimizer
stability theorem pointwise in history, and integrates the resulting
half-power envelope. A generated `Exp3.actionProcessMeasure` specialization
discharges the conditional-law identity; a canonical history-selector
consumer also discharges minimizer and finite-simplex certificates.

The regularity boundary remains explicit: a standard-Borel action space with
measurable singletons, a finite nonempty arm set, finite history measure,
positive eta, supported losses in
`[0,1]`, coordinate measurability of the selected current distribution,
measurability/integrability of the history-action stability score, and
integrability of the half-power bound. Focused/root builds and external
source/consumer canaries compile.

Failure policy: one-round conditional action-law transport is closed. This
module consumes selector and updated-score regularity as contracts; downstream
generated-regularity and canonical-selector modules now synthesize them and
close finite-horizon expected assembly. Environment-regret transport,
self-bounding, tuning, and final Tsallis-INF regret remain open.

## Generated pure half-Tsallis trajectory stability

`TSALLIS-HALF-GENERATED-TRAJECTORY-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisFTRLRecursiveTrajectory`. The public endpoint
`Tsallis.integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound`
constructs the recursive finite-pair-history importance-weighted score, pure
half-Tsallis policy kernels, canonical predictable trajectory, conditional
successor-action law, and almost-sure score recursion before applying the
finite-horizon actual-successor stability theorem. Callers no longer supply a
policy law, `condDistrib` identity, or score-recursion proof.

The remaining regularity boundary is deliberate: coordinate measurability of
the noncomputable canonical selector is packaged as
`HalfTsallisFiniteHistorySelectorMeasurability`, and each generated updated
stability score must be measurable. The downstream automatic-integrability
leaf now derives both product-law stability integrability and history-marginal
half-power integrability. Standard-Borel environment/action spaces, measurable
action singletons, finite nonempty arms, finite prior, positive eta, and a
predictable `[0,1]` loss vector are retained.

Failure policy: recursive trajectory construction, conditional action-law
identification, a.e. importance-weighted score recursion, and generated
finite-horizon stability assembly are closed under those explicit regularity
contracts. Downstream selector measurability and estimated-to-environment
transport now compile; self-bounding, comparator specialization, tuning, and
final Tsallis-INF regret remain open.

## Generated half-Tsallis automatic integrability

`TSALLIS-HALF-GENERATED-STABILITY-AUTOMATIC-INTEGRABILITY` is `leanCompiled`
in `BanditRLProof.TsallisFTRLGeneratedRegularity`. Its public endpoint
`Tsallis.integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_measurable`
has the same generated actual-successor horizon conclusion but no caller
`Integrable` families.

The stability proof uses the finite-action identity behind the
importance-weighted estimator: after multiplication by the sampling mass,
the denominator cancels and
`p(chosen) * |stability(chosen)| <= p(chosen) + next(chosen)(chosen)`.
Finite-simplex normalization then bounds the conditional absolute moment by
`1 + arms.card`; `Measure.integrable_compProd_iff` supplies product-law
integrability. The half-power budget is separately bounded by
`2 * |eta| * arms.card` using coordinate bounds and `Real.rpow_le_one`.

Regularity contracts are now the selector coordinate-measurability contract
and per-round measurability of the generated updated stability score, together
with the existing finite-arm, finite-prior, standard-Borel, eta-positive, and
predictable `[0,1]` loss assumptions. Failure policy: both integrability
families are closed without a uniform probability floor. The downstream
generated-measurability leaf derives the scalar score premise from explicit
selector-coordinate regularity. Do not infer canonical selector or updated-
minimizer measurability.

## Generated half-Tsallis stability measurability

`TSALLIS-HALF-GENERATED-STABILITY-MEASURABILITY` is `leanCompiled` in
`BanditRLProof.TsallisFTRLGeneratedMeasurability`. The public endpoint
`Tsallis.integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_of_selector`
has no caller `hscore` or `Integrable` families. It consumes one
`HalfTsallisGeneratedSelectorMeasurability` contract, whose finite-history
component builds the policy and whose updated component states supported
coordinate measurability on the environment/prefix/chosen-action space.

The proof unfolds both finite linear-loss sums. Each importance-weighted
coordinate is a measurable singleton-action `ite`; current probabilities,
predictable losses, and updated selector coordinates are measurable, so
`Finset.measurable_sum` closes the scalar stability score. The predictable-loss
coordinate follows from `PredictableLossVector.measurable_successor` by product
composition. The automatic-integrability theorem then closes the horizon.

Failure policy: generated scalar stability-score measurability, both
integrability families, conditional-law transport, and horizon assembly are
closed under the generated-selector contract. The downstream canonical
selector leaf now proves that the existing `Classical.choose` current and
updated minimizers satisfy this contract.

## Canonical half-Tsallis selector measurability

`TSALLIS-HALF-CANONICAL-SELECTOR-MEASURABILITY` is `leanCompiled` across
`BanditRLProof.TsallisFTRLMinimizerUniqueness`,
`BanditRLProof.TsallisFTRLMinimizerMeasurability`, and
`BanditRLProof.TsallisFTRLGeneratedMeasurability`. Strict concavity of the
finite square-root sum gives strict convexity of the half-Tsallis objective and
uniqueness on supported coordinates. Compact standard-simplex cluster points,
joint objective continuity, and Mathlib ultrafilter convergence then prove the
restricted canonical minimizer continuous in the finite score vector. Borel
composition turns supported score-coordinate measurability into canonical
selector-coordinate measurability.

The generated layer instantiates both finite-history and sampled-action
updated selector contracts and exposes
`integral_sum_sampledHalfTsallisSuccessorStability_le_integral_sum_halfPowerStabilityBound_canonical`,
which has no selector, `hscore`, or integrability argument. Regularity is a
nonempty finite arm set and decidable equality for selector continuity;
measurable singletons for importance-weighted updates; and standard-Borel
environment/action spaces, finite prior, eta positive, and predictable
`[0,1]` loss for the horizon endpoint.

Failure policy: canonical selector measurability is closed. Do not claim
ambient-function uniqueness outside `arms`, whose coordinates are deliberately
unconstrained. The downstream estimated-to-environment regret route now
compiles.

## Half-Tsallis Estimated-to-Environment Regret

`TSALLIS-ESTIMATED-ENVIRONMENT-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisFTRLEstimatedEnvironmentRegret`. The final theorem
`integral_sampledHalfTsallisPredictableEnvironmentRegret_le` bounds expected
predictable environment regret over `horizon + 1` actual rounds. It keeps time
zero separate, because the generated successor theorem covers rounds
`1, ..., horizon`, then combines the initial half-power stability budget, the
integrated successor half-power sum, and the finite-simplex comparator penalty.

Local imports/APIs are the canonical generated measurability and stability
route, deterministic FTRL decomposition, Exp3 predictable trajectory reward
laws, finite-action kernels, `condDistrib`, `Measure.integrable_compProd_iff`,
and finite Bochner sums. The proof identifies actual-time cumulative selectors,
transports observed estimators to predictable losses almost everywhere, proves
mixed and comparator-weighted conditional first moments, and integrates the
pathwise decomposition. Finite sampling mass cancels the
importance-weighted denominator, so no uniform exploration floor is assumed.

Regularity is standard-Borel environment/action spaces, measurable action
singletons, finite nonempty arms, eta positive, a `PredictableLossVector`, a
general finite-simplex comparator, and `IsProbabilityMeasure prior` for the
unscaled initial and penalty constants. Retrieval evidence is the compiled
canonical selector, generated stability, expected stability, deterministic
decomposition, local Exp3 law transports, and Mathlib compProd/condDistrib
integral APIs. Paper cards remain route evidence and the weapon card is
inspiration-only. Root/focused builds, `Tests.Basic`, placeholder scan, and an
independent public-import `#print axioms` audit pass.

Failure policy: estimated-comparator-to-environment transport, including the
otherwise omitted initial round, is closed under these contracts. Do not read
the successor theorem alone as full regret, add an EXP3-style probability
floor, or claim the paper's conjugate-potential/final Tsallis-INF theorem. The
downstream self-bounding consumer now compiles; its missing input is a refined
suboptimal-arm stability/penalty producer.

## Half-Tsallis Self-Bounding Conversion

`SELF-BOUNDING-CONVERSION` is `leanCompiled` in
`BanditRLProof.TsallisSelfBounding`. The module defines the point-mass optimal
comparator, proves its one-round linear regret equals probability-weighted gap
mass, transports a fixed predictable gap law to the generated trajectory, and
obtains the integrated `(Delta, C, T)` self-bounding condition for nonnegative
corruption. It also specializes the existing generated environment-regret
upper theorem to that comparator.

The reusable consumer
`regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption` proves the finite
completion-of-squares step from a refined suboptimal square-root upper bound.
Its contracts are nonnegative indexed probabilities, strictly positive indexed
gaps, a scalar self-bound, and the supplied refined upper bound. Finite sums,
`Real.sqrt`, ordered-field algebra, generated `compProd` integrals, and the
compiled estimated-environment route are the local APIs.

Failure policy: the current fixed-eta producer remains an all-arm
`powerSum (1/2)`. The compiled point-mass counterexample proves it cannot be
uniformly replaced by the required suboptimal-arm square-root sum. Independent
review also confirms that a paper-level result needs adaptive learning-rate
stability-plus-penalty; a reduced-variance-estimator proof is a distinct route
with distinct law transport. The next leaf is
`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY`, not final regret or tuning.

## Refined All-Arm to Suboptimal Stability

`TSALLIS-REFINED-ALLARM-TO-SUBOPTIMAL` is `leanCompiled` in
`BanditRLProof.TsallisRefinedSuboptimalStability`. For every finite-simplex law
and supported distinguished arm it proves
`sum_a sqrt(p_a)*(1-p_a) <= 2*sum_(a != best) sqrt(p_a)`. The best-arm term is
bounded by `1-p_best`, simplex normalization rewrites this as suboptimal mass,
and each suboptimal probability is bounded by its square root.

`regret_le_of_refinedHalfPowerSelfBounding` then product-indexes finite time and
suboptimal arms and composes any nonnegative-coefficient refined all-arm upper
with positive gaps and the `(Delta,C,T)` self-bound. The result is the explicit
`2*base + sum_(t,a != best) (2*coefficient_t)^2/gap_a + corruption` endpoint.
The abstract theorem only needs positive gaps on `arms.erase best`; a later
algorithm-facing wrapper should additionally expose `gap best = 0`.

Failure policy: `hupper` is not yet produced by the generated algorithm. Paper
Lemma 11 uses conjugate-potential Taylor/Hessian control, whereas the existing
local theorem bounds the fixed-eta term `<p_t-p_(t+1),hatLoss_t>` only after a
multiplier-shift upper has discarded chosen-action information. The compiled
shifted-IW moment leaf below recovers the required sampled-action cancellation,
but the compiled minimizer counterexample below proves that the deterministic
comparison and even its final sampled-action average are false for the current
symmetrized expression. The paper-faithful alternative is therefore
`TSALLIS-CONJUGATE-POTENTIAL-STABILITY`. Its expected route additionally needs
expected-simplex/Jensen transport and places each `eta_t^2/2` remainder in
`base`. `TSALLIS-TIME-VARYING-PENALTY` also requires scheduled minimizers,
measurability, kernel identities, and same-`eta_t` auxiliary updates, not only
a scalar telescope. Only after these producers compile should the combined
`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY` be marked complete.

## Refined Shifted IW Moment

`TSALLIS-REFINED-SHIFTED-IW-MOMENT` is `leanCompiled` in
`BanditRLProof.TsallisRefinedImportanceWeightedMoment`. Its Lean-facing
definitions subtract the sampled raw-loss baseline from every ordinary-IW
coordinate. Exact finite-sum expansions prove
`sum_prob_mul_shiftedHalfPowerImportanceWeightedMoment_le` and
`sum_prob_mul_shiftedPositiveCubicImportanceWeightedMoment_le_one`. Thus
`sum_prob_mul_stability_le_refinedHalfPower_add_square` packages any pointwise
shifted Taylor/Hessian bound into
`eta/2 * sum_a sqrt(p_a)*(1-p_a) + eta^2/2`; the current-FTRL wrapper exposes
the same endpoint with the sole additional hypothesis `hshiftedTaylor`.

Local imports/APIs are `BanditRLProof.TsallisFTRLGeneratedRegularity`,
`BanditRLProof.TsallisImportanceWeightedMoment`, ordinary importance-weighted
losses, finite-simplex probabilities, `Finset.erase` sum rearrangements,
`Real.sqrt`, `max`, and ordered-field cancellation. Contracts are finite
decidable arms, strictly positive supported probabilities, losses in `[0,1]`,
and nonnegative eta for the final consumer. No measure, kernel, minimizer,
integrability, or trajectory premise is hidden.

Retrieval evidence is the compiled local importance-weighted moment and refined
all-arm leaves, Mathlib finite-sum/order/sqrt APIs, and Tsallis-INF Lemma 11
Part 2 equations (19)--(21). Numerical testing was used only to reject the false
pointwise `1-p` replacement, not as proof evidence. Root/focused builds and a
`Fin 2` `Tests.Basic` canary compile. Failure policy: baseline expansion,
quadratic cancellation, cubic remainder, and sampled-action averaging are
closed. The downstream obstruction proves `hshiftedTaylor` is not uniformly
available for the current symmetrized term; preserve this consumer for the
different conjugate-potential producer. Do not report it as conjugate-potential
stability, a conditional-expectation theorem, or final Tsallis-INF regret.

## Refined Averaged Stability Obstruction

`TSALLIS-REFINED-AVERAGED-STABILITY-DIAGNOSTIC` is resolved by the
`leanCompiled` theorem
`exists_minimizer_counterexample_to_refinedAveragedStability` in
`BanditRLProof.TsallisRefinedAveragedStabilityObstruction`. Its public statement
exhibits `Fin 2` data with positive eta, strict current simplex probabilities,
`[0,1]` losses, a current half-Tsallis regularized minimizer, and an updated
half-Tsallis regularized minimizer for every sampled ordinary-IW increment, but
proves the strict reverse of the locally paper-scaled
`eta * sum sqrt(p)*(1-p) + 2*eta^2` refined averaged upper bound.

The proof route uses `eta=1/100`, `p=(49/625,576/625)`, rational-square updated
simplex points, exact KKT multipliers, and
`isRegularizedMinimizer_of_halfTsallisInteriorStationary`. `Fin.sum_univ_two`,
explicit `Real.sqrt`/negative-half-rpow certificates, `FinCases`, and
`NormNum` close all arithmetic. There is no measure, kernel, conditional
expectation, or trajectory premise. Root/focused/`Tests.Basic` builds and an
external theorem consumer compile.

Failure policy: do not retry `hshiftedTaylor` or the same averaged coefficient
for `<p-p_next,hatLoss>` under these contracts. This obstruction does not apply
to the conjugate-potential quantity in Tsallis-INF Lemmas 17--19; its distinct
deterministic producer now compiles. Final regret remains open.

## Half-Tsallis Conjugate-Potential Stability

`TSALLIS-CONJUGATE-POTENTIAL-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisConjugatePotentialStability`. The Lean-facing surface
defines `halfTsallisPotentialValue`, `halfTsallisPotentialStability`, the
explicit coordinate conjugate increment, and its finite-sum upper. The main
theorems are
`halfTsallisPotentialStability_importanceWeightedLoss_le_shiftedMoments_of_minimizers`,
`sum_prob_mul_halfTsallisPotentialStability_importanceWeightedLoss_le_refined_of_minimizers`,
and the canonical-selector wrapper
`sum_halfTsallisMinimizer_mul_potentialStability_le_refined`.

Proof route: translate `eta_paper = 2*eta_local`; rewrite each coordinate
increment exactly as
`eta*sqrt(p)*p*d^2/(1+eta*d*sqrt(p))`; use the conjugate domain to bound it by
`eta*sqrt(p)*p*d^2 + 2*eta^2*p^2*max(-d,0)^3`; apply the square-completion
Fenchel coordinate inequality; cancel score/common multiplier by current
interior stationarity; cancel the arbitrary baseline by simplex normalization;
choose the selected raw loss as baseline; and consume the compiled shifted
ordinary-IW quadratic/cubic moments.

The potential definition includes the paper-normalizing `+1/eta`. Independent
review caught that the unshifted local regularized-objective value differs from
the paper potential by this eta-dependent constant: it cancels for the fixed-eta
one-step theorem but not across a time-varying schedule. The low-level
`halfTsallisPotentialStability_le_conjugatePotentialUpper_of_feasible` theorem
is intentionally only a candidate-value bridge; the minimizer-level and
canonical theorems certify the updated point and therefore expose genuine
constrained-potential steps.

Regularity contracts are finite decidable arms, local `eta` in `(0,1/2]`, exact
current and sampled-update half-Tsallis simplex minimizers, and supported losses
in `[0,1]`. Current strict positivity is derived from minimizer interiority.
There is no measure, kernel, conditional expectation, integrability, or
trajectory premise. Retrieval evidence is the local stationarity/minimizer and
shifted-IW moment layers, Mathlib finite-sum/order/sqrt/field APIs, and
Tsallis-INF Lemmas 18--19/equations (13)--(15); theorem-card and weapon material
is not counted as a local proof. Root/focused/`Tests.Basic` builds and external
generic/canonical canaries compile; the public-import axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Failure policy: this theorem is the distinct conjugate-potential quantity and
must not be substituted back into the refuted `<p-p_next,hatLoss>` claim. Its
generated fixed-eta conditional-expectation transport and finite-horizon
potential telescope now compile downstream. `TSALLIS-TIME-VARYING-PENALTY`,
their refined assembly, an early-round fallback for local `eta > 1/2`, an exact
reusable Lemma 18 conjugate-value interface, and final Tsallis-INF regret remain
open.

## Tsallis Conjugate-Potential Finite-Horizon Decomposition

`TSALLIS-CONJUGATE-POTENTIAL-FINITE-HORIZON-DECOMPOSITION` is `leanCompiled` in
`BanditRLProof.TsallisConjugatePotentialFiniteHorizon`. Its deterministic theorem
telescopes the paper-normalized fixed-eta potential using exact score recursion.
Its generic probability theorem identifies each conditional action law with the
finite ordinary-IW sampling measure, integrates the compiled one-round bound,
and exchanges finite sums and Bochner integrals. The generated canonical
endpoint discharges selector measurability, policy and condDistrib identities,
a.e. score recursion, and both score and budget integrability.

The regularity boundary is explicit: finite nonempty decidable arms, a finite
prior, Standard Borel environment/action with measurable action singletons,
predictable supported `[0,1]` losses, and fixed local `eta` in `(0,1/2]`. No
uniform probability floor is introduced. Retrieval evidence is the compiled
conjugate-potential producer and generated half-Tsallis trajectory stack,
Mathlib finite-sum/measure/kernel APIs, and Tsallis-INF Lemmas 18--19. Root,
focused, and `Tests.Basic` builds plus external declaration canaries compile.

Failure policy: the fixed-eta successor-round route is closed. This leaf does
not handle time zero, early rounds with local `eta > 1/2`, learning-rate changes,
the negative best-arm penalty, refined assembly, or final Tsallis-INF regret.

## Tsallis Time-Varying Penalty

`TSALLIS-TIME-VARYING-PENALTY` is `leanCompiled` in
`BanditRLProof.TsallisTimeVaryingPenalty`. The generic theorem consumes exact
current minimizers at `eta_t` and same-`eta_t` next-score auxiliary minimizers,
then bounds the finite scheduled potential sum by the initial mass, explicit
reciprocal-rate increments, and the negative terminal comparator mass. For a
positive nonincreasing schedule, the zero-score minimizer maximizes mass and
the increments telescope to
`(mass(initial) - mass(comparator)) / eta_n`. The canonical theorem constructs
both minimizer families internally. A supported point-mass corollary proves
`mass(pointMass best) = 1` and exposes the negative best-arm term
`-1 / eta_n` explicitly.

Local APIs/imports are `Tsallis.halfTsallisPotentialValue`,
`FTRL.cumulativeLoss`, `FTRL.IsRegularizedMinimizer`,
`halfTsallisMinimizer_isRegularizedMinimizer`,
`Exp3Potential.sum_range_forward_difference`, `Finset` finite sums,
reciprocal order, and field/ring algebra. Regularity contracts are finite
nonempty decidable arms for the canonical endpoint, arbitrary real loss
vectors, a finite-simplex comparator, `eta_t > 0` through the terminal index,
and `eta_(t+1) <= eta_t` before it. There is no probability, measurability,
kernel, integrability, bounded-loss, or `eta <= 1/2` premise.

Retrieval evidence is the compiled conjugate-potential and minimizer layers,
Mathlib finite-sum/order APIs, and Tsallis-INF Lemmas 12 and 20. Root, focused,
and `Tests.Basic` builds plus an external canonical canary compile. Failure
policy: deterministic cross-rate penalty control is closed, but generated
scheduled-selector measurability/law transport, early large-step stability,
refined assembly, tuning, and final regret remain
separate.

## Half-Tsallis Expected Finite-Horizon Stability

`TSALLIS-HALF-EXPECTED-FINITE-HORIZON-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisFTRLExpectedStability`. The generic theorem places every
round on a common ambient finite measure, uses each condDistrib identity to
recover the realized history/action map law, transports product-law
integrability back to that realized composition, applies the compiled
one-round integral bound, and exchanges the finite time sum with the Bochner
integral. The canonical endpoint removes minimizer certificates. The final
successor endpoint assumes exact importance-weighted score recursion and
rewrites the sampled-action update as the actual next-round selector, proving
the integral bound for `sum_t (<p_t,hatLoss_t>-<p_(t+1),hatLoss_t>)`. The
ambient theorem only assumes a finite measure; under a probability measure,
this integral inequality is the usual expected stability bound.

The regularity boundary is explicit: a finite ambient measure; measurable
time-indexed histories/actions; a standard-Borel action space with measurable
singletons; finite nonempty arms; Markov policy laws identified a.e. with the
canonical half-Tsallis finite laws; eta positive; supported `[0,1]` losses;
measurable/integrable product-law stability scores; integrable history
half-power budgets; and exact score recursion. Focused/root builds and the
external final-successor canary compile.

Failure policy: expected finite-horizon stability assembly and sampled-action
successor alignment are closed under those contracts. Downstream modules now
construct the canonical measurable trajectory and consume this theorem in the
compiled estimated-to-environment regret route. Self-bounding, comparator
specialization, tuning, and final Tsallis-INF regret remain open.

## Tsallis Scheduled Recursive Trajectory

`TSALLIS-SCHEDULED-RECURSIVE-TRAJECTORY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledRecursiveTrajectory`. The initial action uses
`eta 0`; the policy after the visible prefix through `n` uses `eta (n+1)` and
the recursively accumulated observed importance-weighted score. The module
compiles a roundwise selector-measurability contract, its canonical inhabitant,
the scheduled finite-action policy and trajectory kernel, and both the
history-only and environment-retaining successor `condDistrib` laws.

Local APIs/imports are the compiled canonical half-Tsallis selector,
`Exp3.measurable_observedImportanceWeightedLoss`, finite-action measures and
kernels, Thompson's canonical measurable-environment trajectory, Mathlib
`compProd`, and `condDistrib`. Regularity is finite nonempty decidable arms,
measurable singleton actions, a deterministic real schedule, and for the law
wrappers Standard Borel environment/action plus a finite prior and measurable
history environment. Positivity and monotonicity of `eta` are deliberately not
needed at this law layer.

Retrieval evidence is the fixed-rate generated trajectory, canonical selector,
time-varying penalty, and local kernel/conditional-distribution declarations.
Focused/root and `Tests.Basic` builds plus external canaries compile; the axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Failure policy: scheduled selector regularity and successor action-law transport
are closed. Observed-IW cumulative-loss alignment and pathwise
stability-plus-penalty assembly now compile downstream, as does expected
refined stability over every successor round. The time-zero consumer, the early
`eta > 1/2` fallback, tuning, and final Tsallis-INF regret remain separate.

## Tsallis Scheduled Score/Penalty Alignment

`TSALLIS-SCHEDULED-SCORE-PENALTY-ALIGNMENT` is `leanCompiled` in
`BanditRLProof.TsallisScheduledScoreAlignment`. The inclusive generated history
score through `n` is proved equal to `FTRL.cumulativeLoss` of the actual
observed IW vectors through `n`. Consequently the canonical scheduled
minimizer at time `t` is definitionally transported to the actual generated
sampling probability. Named same-rate stability, potential-penalty, and
estimated-regret processes then satisfy an exact pathwise finite-sum
decomposition. Combining this identity with the deterministic scheduled
point-mass theorem yields generated best-arm estimated regret bounded by the
same-rate stability sum plus initial mass divided by `eta_n` minus `1/eta_n`.

Local APIs/imports are `TsallisScheduledRecursiveTrajectory`,
`TsallisTimeVaryingPenalty`, the fixed-rate alignment pattern,
`Exp3.previousPairHistory_frestrictLe`, `FTRL.cumulativeLoss_succ`, finite sums,
and ring/linear arithmetic. Contracts are finite nonempty decidable arms, an
arbitrary path sample, a supported best arm, positive `eta_t` through `n`, and
a nonincreasing schedule before `n`. No probability measure, measurability,
conditional law, integrability, reward bound, probability floor, or eta upper
bound is used.

Retrieval evidence is the compiled scheduled trajectory, deterministic
time-varying penalty, fixed-rate estimated-environment alignment, and
conjugate-potential producer. Failure policy: pathwise alignment and penalty
assembly are closed, and the expected successor stability sum now compiles.
The time-zero finite-action expectation and integrability consumer now compiles
downstream, as does its exact all-times finite-sum assembly with the successor
endpoint. The next blockers are a coarse fallback for local rates above `1/2`
and integration of the small-rate expected stability sum with the scheduled
penalty theorem.

## Tsallis Scheduled Successor Expected Stability

`TSALLIS-SCHEDULED-SUCCESSOR-EXPECTED-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledExpectedStability`. Its endpoint integrates the
exact pathwise same-rate potential-stability term at actual times `n+1` and
bounds the finite sum by the integral of
`eta (n+1) * sum_a sqrt(p_a) * (1-p_a) + 2 * eta (n+1)^2`.

The module packages the environment/prefix history map, successor action map,
lifted scheduled finite-action source and policy, scheduled current and
same-rate updated selectors, coordinate measurability, and automatic
product-law integrability. It instantiates the existing one-round conjugate
bound separately at each `eta (n+1)`, uses the generated successor
`condDistrib`, rewrites stored feedback to the predictable loss coordinate via
`Exp3.canonicalPredictableTrajectoryMeasure_reward_eq_successorLoss_ae`, and
exchanges the finite sum with the integral using
`ExpectationBochnerSums.integral_finset_sum`.

Regularity is a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` losses,
and `0 < eta (n+1) <= 1/2` for every included successor. No schedule
monotonicity, probability floor, independence, concentration premise, or
time-zero law is hidden. Retrieval evidence is the scheduled score/penalty and
trajectory leaves, fixed-rate conjugate finite-horizon route, Mathlib
kernel/integral/finite-sum APIs, and Tsallis-INF Lemmas 18--19. Focused/root and
`Tests.Basic` builds plus the external `Fin 2` endpoint canary compile. The
placeholder scan is empty, and the public-import axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Failure policy: expected successor stability is closed, and time zero plus the
combined all-times finite-sum consumer now compile downstream. Do not infer an
`eta_t > 1/2` fallback, integration of the full
stability-plus-penalty regret theorem, all-arm refinement, tuning, or final
Tsallis-INF regret.

## Tsallis Scheduled Initial Expected Stability

`TSALLIS-SCHEDULED-INITIAL-EXPECTED-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledInitialExpectedStability`. Its endpoint proves
integrability of the exact pathwise scheduled potential-stability term at time
zero and bounds its integral by the canonical initial refined budget
`eta 0 * sum_a sqrt(p_0(a)) * (1-p_0(a)) + 2 * (eta 0)^2`.

The proof defines the zero-score initial history/action potential score, reuses
the canonical initial finite-action source, transports the initial action law
with `canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment`,
and rewrites the stored reward with
`canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae`. It then
identifies the scheduled same-rate next minimizer and applies the generic
one-round conjugate-potential integral theorem.

Regularity is a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` initial
losses, and `0 < eta 0 <= 1/2`. No schedule monotonicity, successor-rate
premise, probability floor, independence, or concentration is used. Failure
policy: focused/root/`Tests.Basic` builds and the external `Fin 2` canary pass;
the source is placeholder-free and the public-import axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Time-zero expectation transport
is closed and the initial-plus-successor finite-sum consumer now compiles
downstream; early `eta_t > 1/2` fallback, full integrated assembly, tuning, and
final regret remain open.

## Tsallis Scheduled All-Times Expected Stability

`TSALLIS-SCHEDULED-ALL-TIMES-EXPECTED-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledAllTimesExpectedStability`. Its final statement
integrates the exact pathwise stability sum over `Finset.range (horizon + 1)`
and bounds it by the integral of the initial refined budget plus every
successor refined budget. This is the stability sum consumed by the scheduled
pathwise regret decomposition, not an auxiliary surrogate.

The proof first exposes the successor path-term/history-action equality as a
public a.e. API, transports product-law integrability back to each trajectory
term, and forms the successor finite sum. It then combines this with the
distinct time-zero integrability theorem using `Finset.sum_range_succ'`, proves
both budget sides integrable, applies `integral_add`, and adds the initial and
successor expectation inequalities.

Regularity is a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` losses,
and `0 < eta t <= 1/2` for every `t <= horizon`. No monotonicity, probability
floor, comparator, independence, or concentration premise is used. Retrieval
evidence is the initial/successor expected-stability leaves, scheduled
score/penalty alignment, `IntegrabilitySums.integrable_finset_sum`,
`MeasureTheory.Integrable.add`, `integral_add`, and the Mathlib measure/finite-
sum cards. Focused/root/`Tests.Basic` builds and the external `Fin 2` canary
pass; the source is placeholder-free and the public-import axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Failure policy: all-times small-rate expected stability is closed. The local
`eta_t > 1/2` fallback, expected stability-plus-penalty integration, all-arm
refinement, tuning, and final Tsallis-INF regret remain open.

## Tsallis Scheduled All-Rate Expected Stability

`TSALLIS-SCHEDULED-ALL-RATE-EXPECTED-STABILITY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledAllRateExpectedStability`. Its final statement
keeps the exact `Finset.range (horizon + 1)` pathwise stability sum and bounds
each actual time by the refined budget when `eta t <= 1/2`, or by the coarse
constant `1` otherwise. Thus the all-times expectation now requires only
`0 < eta t` for included times.

The proof route is layered. A deterministic minimizer comparison reduces the
potential step to a difference of finite linear losses; ordinary-IW
cancellation and nonnegativity then give the pointwise bound `<= 1`. The
finite-simplex average, product-law integrability, and identified
`condDistrib` transport are exposed as generic APIs. Initial and successor
generated-law wrappers select between those coarse APIs and the existing
refined endpoints, before `ExpectationBochnerSums.integral_finset_sum` closes
the exact all-times result.

Regularity is a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable supported
`[0,1]` losses, and positive included rates. No rate upper bound, schedule
monotonicity, probability floor, comparator, independence, or concentration
is assumed. Retrieval evidence includes Tsallis-INF Lemma 11's
`min {refined, 1}` ordinary-IW branch and early-round constant fallback, the
compiled scheduled refined endpoints, and local finite-action
kernel/integral/sum APIs. The paper card is retrieval evidence, not a local
proof; proof-weapon cards remain inspiration-only.

Failure policy: the early large-rate expected-stability gap is closed, and its
expected stability-plus-penalty consumer now compiles. The remaining route is
the all-arm-to-suboptimal conversion, tuning, and final Tsallis-INF regret.

## Tsallis Scheduled Expected Regret

`TSALLIS-SCHEDULED-EXPECTED-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisScheduledExpectedRegret`. Its endpoint bounds generated
predictable environment regret against `pointMass best` by the exact
all-rate scheduled stability-budget integral plus the explicit initial
potential term divided by `eta horizon` and terminal `-1 / eta horizon`.

The support layer proves scheduled probability measurability and simplex
membership, no-floor conditional IW first moments, stored-reward to
predictable-estimator a.e. transport, and finite-horizon integrability. The
final proof combines the observed/environment integral identity, pathwise
scheduled point-mass penalty, `integral_mono_ae`, and the compiled all-rate
expected-stability sum. Contracts are a probability prior, Standard Borel
environment/action, measurable action singletons, finite nonempty decidable
arms, predictable `[0,1]` losses, `best ∈ arms`, positive rates through the
inclusive horizon, and a nonincreasing schedule. No probability floor or eta
upper bound is used.

Retrieval evidence is the fixed-rate estimated/environment regret module, the
scheduled score/penalty and all-rate stability leaves, Mathlib conditional-law,
integral, and finite-sum cards, and Tsallis-INF Lemma 11. Failure policy: the
expected scheduled assembly is closed, and its small-rate suboptimal-arm
consumer and exact predictable fixed-gap producer now compile. Model-side
reward-law-to-gap transport, schedule tuning, and the full Tsallis-INF regret
theorem remain open.

## Tsallis Scheduled Refined Expected Penalty

`TSALLIS-SCHEDULED-REFINED-EXPECTED-PENALTY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledRefinedExpectedPenalty`. Its final Lean-facing
theorem bounds generated predictable environment regret by the all-rate
stability integral plus an initial refined suboptimal mass and the finite sum
of reciprocal-rate increments times expected refined suboptimal masses. The
coarse terminal term `M(p_0) / eta_horizon - 1 / eta_horizon` is absent.

The proof first establishes
`M(p)-1 <= 2 * sum_{a != best} (sqrt(p_a)-p_a/2)` on a finite simplex. It then
consumes the uncollapsed deterministic penalty theorem, cancels the constant
point-mass baseline using `sum_range_forward_difference`, proves the refined
mass integrable, transports each square root with concave Jensen, and combines
the result with the exact observed-to-environment regret identity and all-rate
stability integral.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, positive rates through the
inclusive horizon, and a nonincreasing schedule. There is no eta upper bound,
probability floor, gap law, independence, concentration premise, or tuned
schedule. Retrieval evidence is Tsallis-INF Lemma 12 part 2, the local
time-varying penalty and scheduled expected-regret leaves, Mathlib finite-sum,
integral, and square-root/Jensen APIs. Failure policy: do not return to the
coarse terminal penalty for stochastic tuning. The next leaf must combine the
refined stability and penalty coefficients; that assembly now compiles
downstream. Concrete schedule algebra and full Tsallis-INF regret remain open.

## Tsallis Scheduled Refined Stability-Penalty Assembly

`TSALLIS-SCHEDULED-REFINED-STABILITY-PENALTY-ASSEMBLY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledRefinedStabilityPenalty`. It defines
`c_0 = 2*eta_0 + 2/eta_0` and
`c_(t+1) = 2*eta_(t+1) + 2*(1/eta_(t+1)-1/eta_t)`, then proves generated
predictable environment regret is at most
`sum_t 2*eta_t^2 + sum_t c_t*sum_{a != best} sqrt(E[p_t(a)])`.

The final endpoint reuses the exact predictable fixed-gap law and automatic
self-bound to obtain
`2*sum_t 2*eta_t^2 + sum_(t,a != best) c_t^2/gap(a) + corruption` without a
caller-supplied self-bounding hypothesis. The proof drops only the
nonpositive `-E[p]/2` correction, reindexes time zero plus successors with
`Finset.sum_range_succ'`, and applies the compiled finite completion-of-squares
consumer over the time/arm product.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, positive nonincreasing rates
bounded by `1/2` through the horizon, exact fixed gaps, positive suboptimal
gaps, and nonnegative corruption. No probability floor, independence,
concentration premise, manual self-bound, or concrete schedule is assumed.
Retrieval evidence is the refined expected penalty, fixed-gap self-bound,
suboptimal Jensen, generic completion-of-squares, finite-sum, integral, and
square-root routes. Failure policy: coefficient assembly is closed, and its
concrete square-root schedule consumer now compiles downstream. Do not reopen
the coarse terminal penalty or claim the broader stochastic/full theorem.

## Tsallis Square-Root Schedule Fixed-Gap Bound

`TSALLIS-SQRT-SCHEDULE-FIXED-GAP` is `leanCompiled` in
`BanditRLProof.TsallisSqrtScheduleFixedGap`. It instantiates the generated
scheduled policy with `eta_t = 1/(2*sqrt(t+1))`, proves positivity,
monotonicity, `eta_t <= 1/2`, `4*eta_t^2 = 1/(t+1)`, and
`c_t^2 <= 25/(t+1)`, and closes the time/arm product sum. The final theorem is
`regret <= H_(T+1)*(1+25*sum_(a != best)1/gap(a))+corruption` under the exact
predictable fixed-gap law.

The route imports only the compiled refined stability-penalty endpoint and
uses Mathlib square-root order/square identities, reciprocal order, and finite
sum/product factorization. Regularity is unchanged from the exact-gap route:
probability prior, Standard Borel environment/action, measurable singletons,
finite nonempty decidable arms, supported predictable `[0,1]` losses, supported
best arm, positive suboptimal gaps, and nonnegative corruption. Schedule
contracts and the self-bound are no longer caller premises. Retrieval evidence
is the local refined assembly/fixed-gap route plus `MLIB-FINSET-SUMS` and
`MLIB-REAL-LOG-SQRT`. Failure policy: the finite harmonic theorem is closed and
its Mathlib-backed logarithmic corollary now compiles downstream. Broader
stochastic/corrupted-law transport remains open, so this is not yet the full
paper Tsallis-INF theorem.

## Tsallis Square-Root Schedule Logarithmic Fixed-Gap Bound

`TSALLIS-SQRT-SCHEDULE-LOG-FIXED-GAP` is `leanCompiled` in
`BanditRLProof.TsallisSqrtScheduleFixedGap`. The module now identifies its
Real-valued finite harmonic budget with the Real cast of Mathlib's rational
`harmonic (T+1)`, applies `harmonic_le_one_add_log`, proves the reciprocal-gap
factor nonnegative, and exposes
`regret <= (1+log(T+1))*(1+25*sum_(a!=best)1/gap(a))+corruption`.

The only new import is `Mathlib.NumberTheory.Harmonic.Bounds`; the proof uses
the rational cast APIs and the existing harmonic fixed-gap endpoint. No new
regularity premise is introduced. Root, focused, and `Tests.Basic` builds plus
the external `Fin 2` canary cover the public interface. Failure policy: the
explicit logarithmic exact predictable-gap theorem is closed. The remaining
theorem-level gap is transport from broader stochastic/corrupted reward laws
to self-bounding, not finite-sum or logarithm algebra.

## Tsallis Finite-Bandit Mean-Loss Specialization

`TSALLIS-FINITE-BANDIT-MEAN-LOSS` is `leanCompiled` in
`BanditRLProof.TsallisFiniteBanditMeanLoss`. Given a `FiniteBanditModel` whose
Real-cast means lie in `[0,1]`, `Exp3.finiteBanditMeanLoss` constructs the
stationary predictable loss `1 - mean`. Countability of `Fin K` discharges
product measurability, and the public gap lemma proves at every time and sample
that the loss difference against `model.bestArm` is exactly the Real cast of
`model.gap arm`.

The final endpoint fixes the arm set to `Finset.univ`, obtains nonemptiness from
`model.bestArm`, and invokes the compiled logarithmic square-root-schedule
theorem. Callers provide only bounded means, strictly positive non-best model
gaps, a probability prior on a Standard Borel environment, and nonnegative
corruption; no predictable-loss object, gap-law proof, or schedule proof is
exposed. Root, focused, and `Tests.Basic` builds plus an external `Fin 2`
canary cover the interface. Failure policy: the finite-model deterministic
mean-loss route is closed. Its feedback law is still Dirac at `1 - mean`;
random reward-kernel feedback and conditional-mean/self-bounding transport
remain open and must not be reported as the stochastic Tsallis-INF theorem.

## Tsallis Scheduled Suboptimal Expected Bound

`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY` is `leanCompiled` in
`BanditRLProof.TsallisScheduledSuboptimalExpectedBound`. The module defines
the expected scheduled action probability, proves that these expectations
again form a finite simplex, and applies Mathlib's concave Jensen theorem for
`Real.sqrt` to obtain `E[sqrt (p_t(a))] <= sqrt (E[p_t(a)])`.

Under `0 < eta t <= 1/2`, the piecewise all-rate budget is definitionally the
refined budget. The existing all-arm elimination lemma removes the best-arm
coordinate pathwise, finite-sum/integral exchange closes the inclusive
`Finset.range (horizon + 1)` expression, and the compiled scheduled
expected-regret theorem supplies the initial-minus-terminal potential penalty.
The principal endpoint is therefore an environment-regret upper bound by
`sum_t (2 * eta_t * sum_{a != best} sqrt (E[p_t(a)]) + 2 * eta_t^2)` plus
that penalty. A second endpoint passes this expression and an explicit
positive-gap self-bounding inequality to the compiled completion-of-squares
consumer.

Regularity contracts are a probability prior, Standard Borel environment and
action spaces, measurable action singletons, finite nonempty decidable arms,
predictable supported `[0,1]` losses, `best` in the arm set, a positive
nonincreasing schedule with `eta t <= 1/2` through the inclusive horizon, and,
for the final self-bounding theorem, positive gaps on `arms.erase best` plus an
explicit expected-probability self-bound with corruption. No probability
floor, independence, concentration premise, or tuned schedule is used.

Retrieval evidence is the compiled scheduled expected-regret, all-rate
stability, refined all-arm-to-suboptimal, and self-bounding leaves; Mathlib's
concave integral, finite-sum, measure-integral, and square-root APIs; and
Tsallis-INF Lemma 11. The paper card is evidence only and weapon cards are
inspiration-only. Failure policy: simplex/Jensen transport, suboptimal-arm
elimination, scheduled penalty assembly, and abstract self-bounding completion
are closed. Do not claim an automatic fixed-gap law wrapper, schedule tuning,
or the full Tsallis-INF theorem. The exact predictable fixed-gap wrapper now
compiles downstream; this does not derive that law from a stochastic reward
kernel.

## Tsallis Scheduled Fixed-Gap Self-Bounding

`TSALLIS-SCHEDULED-FIXED-GAP-SELF-BOUNDING` is `leanCompiled` in
`BanditRLProof.TsallisScheduledFixedGapSelfBounding`. The pathwise theorem
rewrites scheduled predictable environment regret against `pointMass best` as
the inclusive time sum of `p_t(a) * gap(a)` over `arms.erase best`. It reuses
the finite-simplex point-mass gap identity and derives `gap(best) = 0` from the
exact predictable loss-difference law at each sample and time.

A measure-generic theorem proves integrability of every finite coordinate,
exchanges both finite sums with the integral, and identifies the result with
`sum_t sum_{a != best} gap(a) * E[p_t(a)]`. Consequently every nonnegative
corruption allowance supplies the explicit self-bounding premise automatically.
The final endpoint invokes the previous completion-of-squares theorem and
returns the scheduled squared-rate-over-gap regret bound without a
caller-supplied self-bound.

Regularity contracts are a probability prior, Standard Borel environment and
action spaces, measurable action singletons, finite nonempty decidable arms,
predictable supported `[0,1]` losses, a supported best arm, exact samplewise
`loss_t(a) - loss_t(best) = gap(a)` on the arm set, strictly positive gaps on
`arms.erase best`, nonnegative corruption, and positive nonincreasing rates
with `eta t <= 1/2` through the inclusive horizon. No probability floor,
independence, concentration premise, manually supplied self-bound, or tuned
schedule is used.

Retrieval evidence is the scheduled suboptimal expected-bound leaf, the
generic self-bounding conversion, the scheduled expected-regret layer,
Mathlib finite-sum and measure-integral APIs, and the stochastic self-bounding
route in Tsallis-INF. The paper card is evidence only and weapon cards are
inspiration-only. Failure policy: exact predictable gap identification,
expected gap-mass transport, nonnegative-corruption self-bounding, and final
completion-of-squares assembly are closed. Do not claim the exact gap law has
been derived from reward-kernel means, that rates are tuned, or that the full
Tsallis-INF theorem is complete.

## Tsallis Scheduled Expected-Gap Self-Bounding

`TSALLIS-SCHEDULED-EXPECTED-GAP-SELF-BOUNDING` is `leanCompiled` in
`BanditRLProof.TsallisScheduledExpectedGapSelfBounding`. Its Lean-facing
contract `HasScheduledExpectedGapLaw` is coordinatewise: for every included
time and suboptimal arm,
`E[p_t(a) * (loss_t(a) - loss_t(best))] = gap(a) * E[p_t(a)]`.
Unlike the earlier producer, it does not require the loss difference to equal
the gap at every sample.

The proof establishes measurability and integrability of each weighted loss
difference using the simplex bound and `[0,1]` predictable losses, rewrites
point-mass regret as a finite sum over `arms.erase best`, exchanges the time
and arm sums with the integral, and derives the usual corruption self-bound.
Generic self-bound consumers were extracted at the refined coefficient and
square-root schedule layers. The final compiled endpoint is
`regret <= (1+log(T+1))*(1+25*sum_(a!=best)1/gap(a))+corruption`.

Regularity is a probability trajectory law, measurable action singletons,
finite nonempty decidable arms, predictable `[0,1]` losses, supported best arm,
positive suboptimal gaps, nonnegative corruption, and the coordinatewise
expected-gap law. The generated final wrapper additionally uses Standard
Borel environment/action spaces and a probability prior. No probability
floor, samplewise fixed-gap identity, concentration theorem, or caller
schedule proof is required.

Retrieval evidence is the compiled fixed-gap, scheduled expected-regret,
refined stability, and square-root/log leaves; `MLIB-MEASURE-INTEGRAL`,
`MLIB-FINSET-SUMS`, `MLIB-CONDITIONAL-EXPECTATION`; and the Tsallis-INF paper
card. Cards remain evidence only and weapons remain inspiration-only. The
public `Fin 2` canary, focused/root/`Tests.Basic` builds, placeholder scan, and
axiom audit pass; the latter reports only `propext`, `Classical.choice`, and
`Quot.sound`. Failure policy: expected-gap-to-log-regret transport is closed.
Deriving `HasScheduledExpectedGapLaw` from an actual stochastic reward/loss
construction via conditional expectation or independence remains open.

## Tsallis Scheduled Conditional-Mean Expected Gap

`TSALLIS-SCHEDULED-CONDITIONAL-MEAN-EXPECTED-GAP` is `leanCompiled` in
`BanditRLProof.TsallisScheduledConditionalMeanGap`. The module defines
`sampledScheduledHalfTsallisPastSigma`: it is `bot` at time zero and the comap
of the generated action/reward prefix through `n` before time `n+1`. It proves
that every scheduled probability coordinate `p_t(a)` is strongly measurable
on this sigma-algebra.

The Lean-facing contract `HasScheduledConditionalMeanGapLaw` requires
`condExp past_t (loss_t(a)-loss_t(best)) = gap(a)` almost everywhere for each
included time and suboptimal arm. The producer
`hasScheduledExpectedGapLaw_of_conditionalMeanGapLaw` applies Mathlib's
`condExp_mul_of_stronglyMeasurable_left` and `integral_condExp` to obtain
`HasScheduledExpectedGapLaw`, so all existing self-bounding and logarithmic
consumers apply without a samplewise fixed-gap premise.

Regularity is a probability trajectory measure, measurable singleton actions,
finite nonempty decidable arms, predictable `[0,1]` losses, and the stated
conditional mean law through the inclusive horizon. No Standard Borel,
independence, reward-kernel, floor, concentration, or schedule premise is added
by this producer. Retrieval evidence is `MLIB-CONDITIONAL-EXPECTATION`,
`MLIB-MEASURE-INTEGRAL`, the local expected-gap leaf and local independence
wrappers, plus the Tsallis-INF paper card; cards are evidence only and weapons
are inspiration-only. The public-import axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Failure policy: past-measurability and
conditional-mean to first-moment transport are closed. The independence
producer now compiles downstream; producing its hypotheses from a concrete
stochastic reward/loss kernel remains open, so this is not the full
stochastic/corrupted Tsallis-INF theorem.

## Tsallis Scheduled Independent-Mean Gap Regret

`TSALLIS-SCHEDULED-INDEPENDENT-MEAN-GAP-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisScheduledIndependentMeanGap`. Its contract
`HasScheduledIndependentMeanGapLaw` states, for each included time and
suboptimal arm, that the predictable loss difference is independent of the
pre-action trace sigma-algebra and has global integral equal to the arm gap.

Mathlib's `condExp_indep_eq` turns that contract into
`HasScheduledConditionalMeanGapLaw`; the compiled conditional-mean producer
then yields `HasScheduledExpectedGapLaw`. The final generated-trajectory
theorem reaches
`regret <= (1+log(T+1))*(1+25*sum_(a!=best)1/gap(a))+corruption` under the
square-root schedule. Thus independence-to-conditional-mean, expected
self-bounding, schedule algebra, and logarithmic closure are one compiled
theorem route rather than disconnected cards.

The generic producers require a probability trajectory measure, finite
decidable arms, predictable `[0,1]` losses, coordinatewise independence and
exact global means; the expected-gap step also uses measurable singleton
actions. The final endpoint additionally uses Standard Borel environment and
action spaces, a probability prior, positive suboptimal gaps, and nonnegative
corruption. No samplewise fixed-gap law, probability floor, concentration
premise, or caller schedule proof is needed.

Retrieval evidence is the local conditional-mean and expected-gap leaves,
`MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-CONDITIONAL-EXPECTATION`,
`MLIB-MEASURE-INTEGRAL`, the compiled ETC `condExp_indep_eq` pattern, and the
Tsallis-INF paper card. Cards are evidence only and weapons are
inspiration-only. The public-import axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Failure policy: the abstract independence route is closed.
The remaining law transport is to prove its independence and mean premises
for one concrete stochastic reward/loss kernel on the generated trajectory;
full stochastic/corrupted Tsallis-INF is not yet claimed.
+
## Tsallis Scheduled IID Mean-Gap Route

`TSALLIS-SCHEDULED-IID-MEAN-GAP-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisScheduledIIDMeanGap`.  The Lean-facing model is an IID
loss-state stream with a jointly measurable `[0,1]` loss evaluator.
`KernelTrajectoryPrefix.partialTraj_zero_congr` and
`trajMeasure_map_frestrictLe_congr` show that finite Ionescu-Tulcea marginals
only use the corresponding finite step-kernel prefix.  The explicit
`sampledScheduledHalfTsallisIIDPrefixKernel` therefore proves
`HasScheduledIIDPrefixKernelFactorization` for the canonical trajectory.
Infinite-product coordinate independence, `Measure.fst_compProd`,
`Measure.infinitePi_map_eval`, and the past-kernel independence transport then
produce `HasScheduledIndependentMeanGapLaw` and the explicit logarithmic regret
endpoint.  The final theorem has no caller-supplied trajectory or `hfactor`.

Regularity is now exactly Standard Borel loss states/actions, measurable
singleton actions, a probability coordinate law, jointly measurable `[0,1]`
losses, positive mean gaps, and nonnegative corruption.
Retrieval evidence is the local IID-coordinate and scheduled independent-mean
leaves plus `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL`,
`MLIB-MEASURE-INTEGRAL`, and the Tsallis-INF paper card.  Cards remain evidence
only and weapons inspiration-only. Failure policy: canonical prefix
factorization, IID independence/global means, and the concrete IID log endpoint
are closed. The finite-arm stochastic reward-vector/model-gap consumer now
compiles; an actual corruption contract is separate.

## Tsallis Finite-Arm IID Reward-Law Route

`TSALLIS-FINITE-ARM-IID-REWARD-LAW-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDRewardLaw`. It closes the model-facing gap
left by the abstract IID loss-state theorem. A family
`armLaw : Fin K -> Measure Rat` is assembled into `Measure.pi armLaw`.
Pointwise clipping gives a globally `[0,1]` selected loss, while the explicit
a.e. reward-support contract proves clipping does not alter arm means.
`MeasureTheory.integral_comp_eval` then transports the coordinate integrals,
and the abstract `iidLossStateMeanGap` is exactly the Real cast of
`FiniteBanditModel.gap`.

The final theorem exposes the scheduled half-Tsallis logarithmic bound directly
in model gaps. Required contracts are probability arm laws, rewards a.e. in
`[0,1]`, exact arm-law means, positive non-best gaps, and nonnegative
corruption. The concrete process is IID across rounds and uses an independent
within-round product reward vector. Retrieval evidence is the local IID route,
Mathlib Pi-integral and measure/integrability cards, and the Tsallis-INF paper
cards. Failure policy: this stochastic IID model route is closed. Its
stationary-oblivious corrupted-process consumer now compiles; adaptive
corruption remains outside this theorem.

## Tsallis Stationary Corrupted IID Reward-Law Route

`TSALLIS-FINITE-ARM-IID-STATIONARY-CORRUPTED-REWARD-LAW-REGRET` is
`leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDCorruptedRewardLaw`. A fixed
`rewardShift : Fin K -> Real` is added to every fresh IID reward coordinate and
projected to `[0,1]`. Mathlib's `Set.abs_projIcc_sub_projIcc` bounds each
coordinate change by `abs (rewardShift arm)`, so the actual mean loss gap is
within `abs (shift arm) + abs (shift bestArm)` of `model.gap`.

The actual IID mean-gap law is constructed through the existing finite-prefix
factorization and independence route. A new perturbed-expected-gap consumer
then derives the baseline self-bound with the explicit inclusive-horizon
budget
`(T+1) * sum_(a != best) (abs (shift a) + abs (shift best))`.
The final logarithmic theorem has no free corruption parameter, and the budget
is zero for zero shift.

Regularity is one probability law per arm, raw rewards a.e. in `[0,1]`, exact
baseline means, positive non-best baseline gaps, a fixed real shift per arm,
and finite horizon. Arms are independent within a round and rounds remain IID.
Retrieval evidence is the finite-arm IID and expected-gap self-bounding leaves,
Mathlib measure/integral/independence cards, the unit-interval contraction, and
the two Tsallis-INF paper cards. Failure policy: stationary oblivious
corruption is closed. Its deterministic time-indexed predictable consumer now
compiles; history-adaptive corruption remains outside this theorem.

## Tsallis Time-Varying Expected-Gap Route

`TSALLIS-SCHEDULED-TIME-VARYING-EXPECTED-GAP` is `leanCompiled` in
`BanditRLProof.TsallisScheduledTimeVaryingExpectedGap`. It generalizes the
first-moment, conditional-mean, and independence contracts from
`gap : Action -> Real` to `gap : Nat -> Action -> Real`. Mathlib conditional
expectation pull-out turns the per-time conditional law into the weighted gap
identity, and finite Bochner-sum exchange identifies integrated generated
regret with the full time-by-arm gap mass.

The new baseline consumer assumes
`abs (actualGap t a - baseGap a) <= deviation t a` and subtracts exactly
`sum_(t<=T) sum_(a!=best) deviation t a` in the self-bound. Its regularity is a
probability trajectory measure, finite nonempty decidable arms, measurable
action singletons, predictable `[0,1]` losses, and the stated deterministic
time-indexed conditional or independent mean law. Retrieval evidence is the
compiled conditional/expected-gap route, `MLIB-CONDITIONAL-EXPECTATION`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-INDEPENDENCE`, and the corrupted
Tsallis-INF paper card. Failure policy: deterministic per-time gap transport
is closed; a random history-dependent gap requires a stronger past-measurable
law.

## Tsallis IID Time-Varying Mean-Gap Producer

`TSALLIS-SCHEDULED-IID-TIME-VARYING-MEAN-GAP` is `leanCompiled` in
`BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap`. The evaluator
`value t state action` reads one fresh coordinate from a common IID state law.
Equal finite state prefixes generate equal visible trajectory prefixes, so a
measurable finite-prefix extension builds the canonical factorization kernel.
Product coordinate independence, `Measure.compProd_map`,
`Measure.fst_compProd`, and `Measure.infinitePi_map_eval` then produce the
time-varying independent and expected-gap laws.

Regularity is Standard Borel state/action spaces, measurable action
singletons, a probability coordinate law, and per-time jointly measurable
`[0,1]` evaluators. Retrieval is the stationary IID producer, the time-varying
expected-gap leaf, and Mathlib independence/kernel/integral cards. Failure
policy: common-law IID coordinates with deterministic time-indexed evaluation
are closed. Nonidentical coordinate laws now compile in the next leaf;
realized-history-dependent evaluation still needs a separate producer.

## Tsallis Independent Nonidentical Mean-Gap Producer

`TSALLIS-SCHEDULED-INDEPENDENT-NONIDENTICAL-MEAN-GAP` is `leanCompiled` in
`BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap`. For
`law : Nat -> Measure LossState`, with every `law t` a probability measure,
`Measure.infinitePi law` and the existing finite-prefix factorization imply
the scheduled time-varying independent mean-gap law with
`gap(t,a)=∫s, value t s a - value t s best ∂law t`.

The proof reuses `iIndepFun_rewardTrace_infinitePi`, separates coordinate `t`
from the finite past via `iIndepFun.indepFun_finset`, transports independence
through the trajectory `compProd`/`comap`, and computes the exact marginal
using `Measure.fst_compProd` and `Measure.infinitePi_map_eval`. Regularity is
Standard Borel state/action spaces, measurable action singletons, one
probability law per coordinate, jointly measurable per-time `[0,1]`
evaluators, a Markov trajectory kernel, and finite-prefix factorization. The
old common-law theorem remains a constant-law wrapper and keeps its original
mean-gap definition for downstream `simp` compatibility. Retrieval is the
common-law producer, the time-varying expected-gap leaf, and Mathlib
independence/kernel/integral cards; theorem cards remain evidence only.
Failure policy: independent nonidentical latent coordinates are closed.
The concrete finite-arm stationary-mean reward-law theorem now compiles
downstream; history-dependent laws, current-action corruption, and
conditional reward kernels need distinct transports.

## Tsallis Time-Varying Corrupted IID Reward-Law Route

`TSALLIS-FINITE-ARM-IID-TIME-VARYING-CORRUPTED-REWARD-LAW-REGRET` is
`leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDTimeVaryingCorruptedRewardLaw`. For a fixed
schedule `rewardShift : Nat -> Fin K -> Real`, the theorem clips shifted fresh
IID rewards to `[0,1]`, derives each round's actual mean-gap deviation, and
returns the baseline logarithmic reciprocal-gap bound plus
`sum_(t<=T) sum_(a!=best) (abs (shift t a) + abs (shift t best))`.
There is no free corruption parameter. Zero schedules have zero budget and
constant schedules recover the stationary budget exactly.

Regularity is probability arm laws, raw rewards a.e. in `[0,1]`, exact
baseline means, positive non-best baseline gaps, a deterministic full
time-by-arm shift schedule, and finite horizon. Arms remain independent within
each base round and base reward vectors remain IID across rounds. Retrieval is
the stationary corruption theorem, both time-varying supporting leaves,
Mathlib product/integral/independence and projection-contraction APIs, and both
Tsallis-INF paper cards; cards remain evidence only. Failure policy:
deterministic time-indexed oblivious/predictable corruption is closed.
The measurable pre-action-history shift generalization now compiles below;
current-action, latent-law, and expectation-only-budget semantics remain
outside the broader paper theorem.

## History-Adaptive Corrupted IID Reward-Law Route

Three new leaves are `leanCompiled`:

- `TSALLIS-SCHEDULED-REFERENCE-GAP-SELF-BOUNDING` compares actual and
  reference predictable loss gaps on the same actual trajectory measure and
  derives the fixed-baseline self-bound from a pointwise deviation envelope.
- `TSALLIS-SCHEDULED-IID-HISTORY-ADAPTIVE-PREFIX` proves canonical finite IID
  state-prefix factorization when successor losses inspect the supplied
  pre-action finite pair history but only the current IID state coordinate.
- `TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-CORRUPTED-REWARD-LAW-REGRET`
  constructs the measurable clipped loss and proves baseline model-gap log
  regret plus
  `sum_(t<=T) sum_(a!=best) (envelope(t,a)+envelope(t,best))`.

Local APIs/imports are the scheduled expected-gap and IID mean-gap layers,
`PredictableLossVector`, finite-prefix extension and trajectory congruence,
`integral_mono_ae`, product-coordinate independence, `continuous_projIcc`,
projection contraction, and the sqrt-schedule harmonic/log endpoint. The
proof route establishes actual trajectory factorization, proves the
uncorrupted reference model-gap law on that same measure, transports the
pointwise clipped gap deviation through expected probabilities, and invokes
the existing self-bound completion.

Regularity is one probability law per arm, raw rewards a.e. in `[0,1]`, exact
baseline means, positive non-best gaps, measurable pre-action-history shifts,
a deterministic nonnegative time/arm envelope, finite horizon, independent
arms within each base round, and IID base rounds. Retrieval uses the local
stationary/time-varying corruption chain, Mathlib measure/integral/kernel/
independence/projection APIs, and both Tsallis-INF paper cards; cards are
evidence only and weapons inspiration-only. Status includes focused/root/test
canaries and a zero-source budget canary. Failure policy: current-action
corruption, latent reward-law changes, or budgets available only in
expectation require a stronger filtration-aware conditional-law theorem.

`TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-REFINED-CORRUPTED-REWARD-LAW-REGRET`
is now `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDHistoryAdaptiveRefinedCorruptedRewardLaw`.
Its first public statement exposes the preceding construction as the exact
terminal self-bound required by refined tuning. Its final statement fixes
`C` to `finiteArmIIDHistoryAdaptiveRewardCorruptionBudget`, keeps
`S=sum_(a!=best) 1/gap(a)`, and proves the generated local endpoint
`1+log(T+1)+10*sqrt(C*S)*(2+sqrt(log(scale/(C*S))+1))`. Thus neither the
corruption scalar nor trajectory-law identification is caller supplied.

The model-facing `_of_window` theorem now replaces positive budget and the four
low-level scalar inequalities by gaps in `(0,1]` plus
`finiteArmIIDHistoryAdaptiveRefinedCorruptionWindow`. This named predicate has
three natural clauses: horizon dominates `25*S^2`, corruption mass is at most
the horizon scale, and the logarithmic lower corruption threshold holds.
Finite-sum order proves `armCount<=S`; the generic window theorem then derives
budget positivity and all low-level contracts. Local APIs/imports, proof route,
and retrieval evidence are the history-adaptive corruption leaf, refined
tuning leaf, IID-prefix/reference-gap transport, Mathlib measure/kernel/
independence APIs, and both Tsallis paper cards. Status includes focused/root/
test and declaration canaries. Failure policy: compact-window transport and
this model-level composition are closed. The uniform non-best-arm epsilon-boost
family and its stationary arm-dependent generalization now have compiled exact
budgets, compact-window producers, named regimes, and all-regimes endpoints.
Their complements automatically reuse the logarithmic theorem, closing
zero/small corruption for both families. History-varying or random adaptive
envelopes, current-action or latent-law corruption, expectation-only budgets,
and the complete paper theorem remain open.

## Uniform Suboptimal-Arm Boost Refined Consumer

`TSALLIS-FINITE-ARM-IID-UNIFORM-SUBOPTIMAL-BOOST-REFINED-REGRET` compiles in
`TsallisFiniteArmIIDUniformSuboptimalBoostRefinedRegret`. Lean-facing APIs are
`uniformSuboptimalRewardBoostSource`, its exact corruption-budget theorem, its
compact-window theorem, and the final explicit refined regret theorem. The
proof uses finite-arm measurability, collapses the erased-arm/time envelope
sums to `(T+1)*k*epsilon`, derives `C*S<=k*(T+1)` from `epsilon*S<=1`, and then
reuses the existing model `_of_window` theorem. The named regime and total
bound then split internally: the true branch uses that refined theorem and the
false branch uses the logarithmic theorem plus the exact-budget rewrite.
Contracts for the all-regimes endpoint are nonnegative `epsilon`, probability
arm laws with a.e. `[0,1]` rewards and exact means, a nonempty suboptimal set,
gaps in `(0,1]`, and finite horizon; no window proof remains caller supplied.
Retrieval evidence is the two parent local leaves,
Mathlib finite-sum/measure/kernel/independence and `measurable_of_countable`
APIs, and both Tsallis-INF paper cards. Status is `leanCompiled`, root imported,
and externally canaried. This closes all regimes for the uniform deterministic
boost family; arm-dependent stationary and deterministic time-varying families
compile downstream, while genuinely random history-adaptive envelopes and
stronger corruption models remain open.

## Arm-Dependent Suboptimal-Arm Boost All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-ARM-DEPENDENT-SUBOPTIMAL-BOOST-ALL-REGIMES` compiles in
`TsallisFiniteArmIIDArmDependentSuboptimalBoostRegret`. Its Lean-facing APIs are
`armDependentSuboptimalRewardBoostSource`, the exact source-budget theorem,
`finiteArmIIDArmDependentSuboptimalBoostRefinedRegime`, its compact-window
transport theorem, `finiteArmIIDArmDependentSuboptimalBoostAllRegimeBound`, and
the final generated reward-law regret theorem. For nonnegative
`boost : Fin K -> Real`, the source leaves the best arm unchanged and shifts
each other arm by its own value. Erased finite sums and a constant time sum give
the exact budget `(T+1) * sum_(a != best) boost(a)`. The named regime transports
that exact budget to the existing compact window; the final proof splits on
the regime and invokes either the refined `_of_window` theorem or the
logarithmic `+C` theorem.

Regularity contracts are probability arm laws, a.e. unit reward support, exact
means, a nonempty suboptimal set, gaps in `(0,1]`, pointwise nonnegative boost,
and a finite horizon. Countability supplies arm measurability, and no caller
window proof is required. Retrieval evidence is the compiled history-adaptive
logarithmic/refined leaves, the uniform consumer's finite-sum pattern, Mathlib
finite-sum/order/measure/kernel/independence APIs, and both Tsallis-INF paper
cards. Status is `leanCompiled`, root imported, declaration-indexed, and
externally canaried. Failure policy: stationary nonuniform boosts are closed;
deterministic time-varying schedules compile in the next leaf, while random
history-adaptive envelopes, current-action or latent-law corruption,
expectation-only budgets, paper-sharp constants, and the complete Tsallis-INF
theorem remain open.

## Time-Varying Suboptimal-Arm Boost All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-TIME-VARYING-SUBOPTIMAL-BOOST-ALL-REGIMES` compiles in
`TsallisFiniteArmIIDTimeVaryingSuboptimalBoostRegret`. Its Lean-facing APIs are
`timeVaryingSuboptimalRewardBoostSource`,
`finiteArmIIDTimeVaryingSuboptimalBoostBudget`, the exact source-budget theorem,
`finiteArmIIDTimeVaryingSuboptimalBoostRefinedRegime`, its compact-window
transport theorem, `finiteArmIIDTimeVaryingSuboptimalBoostAllRegimeBound`, and
the final generated reward-law regret theorem. A pointwise nonnegative
`boost : Nat -> Fin K -> Real` is encoded with `boost 0` in the initial source
and `boost (n+1)` after a length-`n` pre-action history; the best-arm shift is
forced to zero. Erased finite-arm sums give the exact corruption mass
`sum_(t<T+1) sum_(a!=best) boost(t,a)` with no uniform time or arm relaxation.
The named regime rewrites this exact budget into the compact window, and the
final theorem internally selects the refined `_of_window` or logarithmic `+C`
parent theorem.

Regularity contracts are probability arm laws, a.e. unit reward support, exact
means, a nonempty suboptimal set, gaps in `(0,1]`, a pointwise nonnegative
deterministic schedule, and finite horizon. Countability of `Fin K` supplies
successor measurability; no new trajectory-law, independence, integrability,
or caller window contract is introduced. Retrieval evidence is the compiled
history-adaptive refined/logarithmic route, the stationary arm-dependent
consumer, Mathlib finite-sum/order/measure/kernel/independence APIs, and both
Tsallis-INF paper cards. Status is `leanCompiled`, focused-built, root imported,
declaration-indexed, and externally canaried. Failure policy: deterministic
time-and-arm nonuniform schedules are closed, and one action-history-dependent
source compiles downstream. Reward-coordinate or arbitrary measurable history
gates, current-action or latent-law corruption, expectation-only budgets,
paper-sharp constants, and the complete Tsallis-INF theorem remain open.

## Previous-Action-Gated Adaptive Boost All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-PREVIOUS-ACTION-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES`
compiles in `TsallisFiniteArmIIDPreviousActionGatedSuboptimalBoostRegret`.
Its Lean-facing APIs are `previousActionGatedSuboptimalRewardBoostSource`, the
exact source-budget theorem, the refined-window transport theorem, and the
final all-regimes reward-law regret theorem. At successor time `n+1`, the
source evaluates action coordinate `n` of
`History.FinitePairHistory (Fin K) Real n`; it activates `boost (n+1) arm`
exactly when that previous sampled action equals `triggerArm`, while the best
arm remains unshifted. The initial round uses `boost 0` on non-best arms.

The successor measurability proof uses `measurable_pi_apply`, product
projections, `measurableSet_eq_fun`, `Measurable.ite`, and countable-arm
measurability. The deterministic envelope is still the complete time-and-arm
schedule, so its exact budget is
`sum_(t<T+1) sum_(a!=best) boost(t,a)`. The existing time-varying named regime
therefore supplies the compact window, and the final theorem selects the
refined or logarithmic parent internally. Regularity contracts are a fixed
trigger arm, pointwise nonnegative deterministic schedule, probability arm
laws, a.e. unit reward support, exact means, nonempty suboptimal arms, gaps in
`(0,1]`, and finite horizon. Retrieval evidence is the time-varying all-regimes
consumer, the history-adaptive refined/logarithmic route, Mathlib finite-product
measurability and finite-sum/measure/kernel/independence APIs, and both
Tsallis-INF paper cards. Status is `leanCompiled`, focused-built, root imported,
declaration-indexed, and externally canaried. Failure policy: this closes a
genuine action-history-dependent source, and the arbitrary measurable
finite-history-and-arm gate generalization compiles below. It does not close
current-action/latent-law corruption, expectation-only budgets, paper
constants, or complete Tsallis-INF regret.

## Measurable History-Arm-Gated Adaptive Boost All-Regimes Consumer

`TSALLIS-FINITE-ARM-IID-MEASURABLE-HISTORY-ARM-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES`
compiles in
`TsallisFiniteArmIIDMeasurableHistoryArmGatedSuboptimalBoostRegret`. Its
Lean-facing gates are an arbitrary `initialGate : Set (Fin K)` and an all-time
family `gate n : Set (History.FinitePairHistory (Fin K) Real n × Fin K)` with
`MeasurableSet (gate n)`. At time zero, the source applies `boost 0 arm`
exactly on `initialGate`; at successor time `n+1`, it applies
`boost (n+1) arm` exactly when `(history, arm)` belongs to `gate n`; the best
arm is always unshifted. This directly supports measurable action-coordinate,
past observed clipped-feedback/loss-coordinate, finite Boolean-combination,
and arm-dependent predictable events. It does not expose the current, raw, or
latent reward-vector coordinate.

The proof combines the supplied gate with the measurable best-arm event and
countable-arm scheduled boost through `Measurable.ite`. Its full deterministic
schedule is the envelope, giving the exact source budget
`sum_(t<T+1) sum_(a!=best) boost(t,a)`. The named time-varying refined regime
therefore supplies the compact window, and the final theorem internally
selects the existing refined `sqrt(C*S)` or logarithmic `+C` parent. Regularity
contracts are an arbitrary initial arm gate, all-time joint successor-gate
measurability, all-time pointwise nonnegative deterministic boost, probability
arm laws, a.e. unit reward support, exact means, nonempty suboptimal arms, gaps
in `(0,1]`, and finite horizon. Retrieval evidence is the
previous-action and time-varying consumers, the history-adaptive refined/log
parents, Mathlib measurable-set/ite/countable-measurability and finite-sum/
measure/kernel/independence APIs, and both Tsallis-INF paper cards. Status is
`leanCompiled` with focused/root/Tests builds and external declaration
canaries. Failure policy: the exact quantity is a worst-case deterministic
envelope budget, not a realized or expected gate-open budget. Horizon-local
only gate/boost evidence and the single-arm `K=1` endpoint are not covered.
Current-action or other nonpredictable gates, raw/latent-law corruption,
random/expectation-only envelopes, paper-sharp constants, and complete
Tsallis-INF remain open.

## Scheduled Self-Bounding Lambda Interpolation

`TSALLIS-SCHEDULED-SELF-BOUNDING-INTERPOLATION` is `leanCompiled` in
`BanditRLProof.TsallisScheduledSelfBoundingInterpolation`. Its generated
theorem combines the existing scheduled square-root expected-probability
upper bound with one terminal `(Delta,C,T)` self-bounding inequality. For
`lambda in [0,1]` the result is exactly `(1+lambda)*upper -
lambda*gapMass + lambda*C`; no self-bound at an earlier horizon is assumed.

The local route uses ordered multiplication and ring normalization after the
kernel, integral, finite-sum, and Jensen obligations already discharged by
`TsallisScheduledSuboptimalExpectedBound`. Retrieval evidence is the local
self-bounding and scheduled expected-probability leaves, Mathlib finite-sum
and ordered-real algebra, and Masoudian--Seldin (2021), equations
`self-bounding` and `upperfull`. The paper remains retrieval evidence, not a
local proof. Failure policy: the interpolation is closed; constrained joint
optimization over all expected action probabilities and `lambda`, the time
threshold split, and the improved square-root corruption endpoint remain
open.

## Constrained One-Round Tsallis Quadratic Optimization

`TSALLIS-CONSTRAINED-QUADRATIC-OPTIMIZATION` is `leanCompiled` in
`BanditRLProof.TsallisConstrainedQuadraticOptimization`. The module proves the
positive-coefficient completion-of-squares bound, both finite-sum branches of
the appendix optimization, the finite-simplex estimate
`sum_(a != best) sqrt(p_a) <= sqrt(K-1)`, and direct wrappers for the generated
scheduled expected action probabilities.

The active branch retains the exact threshold
`2*M <= b*sum_i (1/c_i)` and concludes
`sum_i (b*x_i-c_i*x_i^2) <= b*M-M^2/sum_i(1/c_i)`. Its Tsallis specialization
uses `M=sqrt(card (arms.erase best))`, `x_a=sqrt(p_a)`, and
`c_a=lambda*gap(a)`. Regularity explicitly requires `0<lambda`, positive
suboptimal gaps, and a nonempty suboptimal set for the active denominator;
this makes the paper appendix's implicit denominator conditions Lean-visible.

Retrieval evidence is the preceding interpolation/expected-probability
leaves, Mathlib finite-sum and ordered-field APIs,
`Real.sum_sqrt_mul_sqrt_le`, and Masoudian--Seldin (2021). The paper remains
route evidence only. Failure policy: one-round probability optimization is
closed, while the across-time threshold split, harmonic/logarithmic sum,
joint `lambda` optimization, and final square-root corruption endpoint remain
open.

## Finite-Arm Nonidentical Reward-Law Regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-REWARD-LAW-REGRET` is `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIndependentRewardLaw`, root imported, and
externally canaried with distinct same-mean laws. For
`armLaw : Nat -> Fin K -> Measure Rat`,
every round may use different arm distributions while retaining the fixed
`FiniteBanditModel.mean`. `Measure.pi` forms each round reward vector and
`Measure.infinitePi` makes the round vectors independent but not necessarily
identically distributed. Exact clipped product-law gaps, canonical prefix
factorization, nonidentical coordinate independence, and the fixed mean-gap
consumer yield the explicit logarithmic model-gap regret bound.

Regularity is per-time/per-arm probability, a.e. `[0,1]` reward support,
exact roundwise model means, positive non-best gaps, finite horizon, and
nonnegative additive corruption. Retrieval uses the compiled IID reward-law,
nonidentical mean-gap, Mathlib product/infinite-product measure, integral, and
independence routes; theorem cards are evidence only. Failure policy:
stationary means under independent nonidentical reward laws are closed.
Time-varying means, dependent arms, conditional/history-dependent laws,
current-action corruption, and the complete paper theorem remain open.

## 2026-07-23 Nonidentical Drifting-Mean Reward-Law Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REWARD-LAW-REGRET` is
`leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentDriftingMeanRewardLaw.lean`.
It accepts `armLaw : Nat -> Fin K -> Measure Rat` and an absolute
mean-deviation envelope from one fixed `FiniteBanditModel`. The proof computes
the actual product-law loss gap, bounds its difference from `model.gap` by
the selected and best arm deviations, transports the nonidentical independent
law to the time-varying expected-gap self-bound, and invokes the sqrt-schedule
log consumer for the fixed `model.bestArm` comparator. It is a static-
comparator result, not dynamic regret. The additive term is the explicit
inclusive-horizon double
finite sum; no caller-chosen corruption scalar remains. Root import, focused
build, and `Tests.Basic` pass, including a two-arm canary whose means genuinely
change across rounds. No placeholders were added. Conditional/history or
dependent laws, current-action changes, data-derived envelopes, and complete
Tsallis-INF remain open.

## 2026-07-26 Nonidentical Drifting-Mean Refined-Regret Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REFINED-REGRET` is
`leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentDriftingMeanRefinedRegret.lean`.
The parent drifting-law module now exposes the generated terminal
self-bounding inequality with the exact finite mean-deviation budget. The new
module specializes `RefinedLocalCorruptionWindow`, proves the arm-count versus
reciprocal-gap comparison from non-best gaps in `(0,1]`, extracts the scalar
optimizer contracts, and invokes the compiled refined local endpoint.

The result is the coefficient-aware local `sqrt(C*S)` bound with
`C = finiteArmIndependentMeanDeviationBudget` and fixed comparator
`model.bestArm`. It is conditional on the compact window, so it does not claim
all-regimes closure. Root import, focused build, and `Tests.Basic` pass; the
external two-arm canary instantiates the exact final theorem with the existing
genuinely drifting laws and a `1/4` envelope. No placeholders or new
probability-law assumptions were introduced. The all-regimes and actual-mean
dynamic-comparator wrappers now compile downstream.

## 2026-07-26 Nonidentical Drifting-Mean All-Regimes Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-ALL-REGIMES` is
`leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentDriftingMeanAllRegimes.lean`.
`finiteArmIndependentDriftingMeanAllRegimeBound` selects the compiled
coefficient-aware refined expression exactly when erased arms are nonempty and
the explicit mean-deviation budget satisfies the compact window. It selects
the unconditional logarithmic reciprocal-gap-plus-budget expression on both
complements.

The final generated theorem requires neither a caller window proof nor a
nonempty-suboptimal premise. Its `Fin 1` bound simplifies to
`1 + log(T+1)`, while the two-arm external canary instantiates the exact
all-regimes theorem for genuinely time-varying laws and a `1/4` mean envelope.
The probability/support/law construction is unchanged from the parent route,
and this theorem's comparator is fixed `model.bestArm`. It supplies the fixed
component of the compiled dynamic-regret theorem below.

## 2026-07-26 Nonidentical Drifting-Mean Dynamic-Regret Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-DYNAMIC-REGRET-ALL-REGIMES`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentDriftingMeanDynamicRegret.lean`.
The module defines moving-comparator predictable environment regret and proves
its exact decomposition into fixed-baseline regret plus the cumulative
actual-mean advantage of the moving arm. `finiteArmIndependentBestArmAt`
selects a finite actual-mean maximizer and proves its max property.

The final generated theorem identifies the integrated comparator advantage
through the existing independent nonidentical mean-gap law, bounds it using
`FiniteBanditModel.mean_le_bestArm_mean` and the two armwise deviation
envelopes, and adds it to the fixed all-regimes theorem. This is expected
predictable-environment dynamic regret, not realized sample-path regret. It has no caller
comparator, max, window, or nonempty-suboptimal premise. Focused/root and
`Tests.Basic` builds pass; canaries cover the max property, zero `Fin 1`
penalty/bound, one arm, and genuinely switching two arms, including a proof
that the round-1 maximizer differs from `model.bestArm` and the penalty is
strictly positive. The exact cumulative actual-mean path-variation
specialization now compiles downstream. Horizon-compressed or sharp standard
`V_T`/switch-count rates, conditional/history-dependent or dependent laws,
paper-optimal constants, and complete Tsallis-INF remain open.

## 2026-07-26 Cumulative Mean Path-Variation Dynamic-Regret Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-PATH-VARIATION-DYNAMIC-REGRET-ALL-REGIMES`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentPathVariationDynamicRegret.lean`.
It defines the armwise cumulative sum of consecutive actual-mean increments
and proves by induction that this sum bounds displacement from the round-zero
mean. A round-zero actual/model mean equality then supplies the arbitrary
all-time deviation contract required by the parent theorem.

The final generated expected predictable-environment dynamic-regret theorem
therefore has no caller `meanDeviation` family, comparator, max certificate,
window, or nonempty-suboptimal premise. Focused/root and `Tests.Basic` builds
pass; canaries cover zero variation, an exact one-step value `1/2`, `Fin 1`,
and a genuinely switching two-arm final instantiation. This result retains
the cumulative envelope separately at every included time. It is not a
horizon-compressed or minimax-sharp standard `V_T`, switch-count, realized
sample-path, conditional/history-dependent, dependent-arm, or complete
Tsallis-INF theorem.

## 2026-07-26 Mean Switch-Count Dynamic-Regret Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentMeanSwitchCountDynamicRegret.lean`.
The module derives population-mean membership in `[0,1]` from the probability
and a.e. reward-support contracts, defines the real prefix switch count, and
proves that count equals the coerced filtered cardinality of nonzero
consecutive mean changes. Each changed increment is at most one, so the
compiled cumulative path variation is bounded by this exact count.

Round-zero actual/model mean matching then supplies the parent all-time
deviation contract. The final expected predictable-environment dynamic-regret
theorem has no caller comparator, variation family, switch budget, max
certificate, window, or nonempty-suboptimal premise. Focused and
`Tests.Basic` builds pass; canaries cover mean range, zero and exact one-step
counts, explicit external use of the filtered-cardinality identity,
path-to-count domination, `Fin 1`, and an alternating two-arm final
instantiation. Independent semantic review found no P0/P1 issue and confirmed
the prefix/horizon indexing and generated-law specialization.

This closure is per arm and prefix-indexed. A single global environment
change-point budget, minimax switch-rate algorithm, compressed standard
`V_T`, observable/sample-derived count, realized sample path,
conditional/history-dependent or dependent reward law, and complete
Tsallis-INF theorem remain open.

## 2026-07-26 Global Mean Switch-Count Dynamic-Regret Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentGlobalMeanSwitchCountDynamicRegret.lean`.
The module defines one prefix count of the rounds `s < t` where some arm has
different population means at `s` and `s+1`, and identifies it with the real
coercion of the matching filtered cardinality. A pointwise existential
witness proves that every armwise switch count is bounded by the global
count.

The compiled armwise path and model-deviation adapters then provide the
parent theorem's all-time envelope uniformly across arms. The final expected
predictable-environment dynamic-regret theorem has no caller comparator,
variation family, armwise count, global switch budget, max certificate,
window, or nonempty-suboptimal premise. Focused and `Tests.Basic` builds
pass; canaries cover zero and exact one-step global counts, explicit external
use of the cardinality identity, a law where only arm one switches while arm
zero stays fixed, armwise/global and path/global domination, `Fin 1`, and an
alternating two-arm final instantiation. Independent semantic review found
no P0/P1 issue and confirmed the prefix indexing, existential aggregation,
inequality direction, and final parent-theorem specialization.

This is an exact global population-mean change-point count used as a repeated
prefix envelope. A minimax or horizon-compressed switch-rate/standard `V_T`
theorem, observable/sample-derived count, realized sample path,
conditional/history-dependent or dependent reward law, and complete
Tsallis-INF theorem remain open.

## 2026-07-26 Horizon-Compressed Global Switch-Count Closure

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-HORIZON-COMPRESSED-LOG-DYNAMIC-REGRET`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentGlobalMeanSwitchCountCompressedDynamicRegret.lean`.
The module proves terminal-count nonnegativity and monotonicity, then
compresses the fixed mean-deviation budget and moving-comparator penalty
separately to coefficient `2`. Adding them yields coefficient `4` in the
public logarithmic moving-comparator dynamic-regret bound.

Focused and `Tests.Basic` builds pass. External canaries instantiate count
monotonicity, both compressed budgets, their sum, the `Fin 1` simplification,
and the final theorem on a two-arm law whose actual best arm switches. The
statement requires no upper gap bound, caller budget, deviation family,
comparator, max certificate, refined window, or nonempty erased-arm premise.

The nonstationarity term now contains one terminal global count rather than
a time-indexed finite sum. It stops at `globalCount(T)` and therefore excludes
the post-horizon `T -> T+1` transition. It is nevertheless
`4*(K-1)*(T+1)*globalCount(T)`, so no minimax, sublinear, sharp
switch-rate, or sharp standard variation-budget claim is made. Those
stronger rates, observable/sample-derived counts, realized regret, and
conditional/dependent-law routes remain open.

## 2026-07-26 Single-Switch Comparator-Route Obstruction

`TSALLIS-FINITE-ARM-NONIDENTICAL-SINGLE-SWITCH-DYNAMIC-COMPARATOR-ADVANTAGE-OBSTRUCTION`
is `leanCompiled` in
`BanditRLProof/TsallisFiniteArmIndependentSingleSwitchComparatorObstruction.lean`.
Its fully concrete `Fin 2` Dirac law satisfies probability, a.e. `[0,1]`
support, exact initial model matching, and baseline gap contracts. Lean
identifies the unique actual best arm before and after the switch, proves
`globalCount(T)=1` for `T>0`, and calculates the inclusive-horizon
comparator advantage and repeated-prefix penalty exactly as `T/4` and
`2*T`.

For every natural `c`, the compiled square-horizon witness
`T=(4*c+1)^2` makes `T/4 > c*sqrt(T)` without increasing the switch count.
This isolates the remaining gap in the current proof route: an independent
upper bound on comparator advantage cannot supply a uniform square-root
switch rate. No generated-regret lower bound, minimax lower bound,
algorithm impossibility, or Tsallis-INF failure is claimed. Cancellation-
aware analysis or restarted/windowed/change-detection machinery remains
open. Independent read-only review found no P0-P3 issue and explicitly
checked the count indexing, best-arm uniqueness, exact constants, square-root
witness, regularity surface, external canaries, and claim boundary.

## 2026-07-26 Oracle-Restart Epoch Assembly

`TSALLIS-ORACLE-RESTART-EPOCH-DYNAMIC-REGRET-ASSEMBLY` is `leanCompiled` in
`BanditRLProof/TsallisOracleRestartDynamicRegret.lean`. The module defines the
inclusive epoch fibers, proves the exact moving-comparator finite-sum
decomposition, proves
`sum_epoch sqrt(|fiber epoch|) <= sqrt(|epochs|)*sqrt(horizon+1)`, and exposes
both the epoch-count and switch-count global endpoints.

Focused and `Tests.Basic` builds pass. The external canaries include a
concrete two-epoch/four-round cardinality instance, an unused empty-fiber
instance, and abstract consumers of the exact decomposition and both assembly
endpoints. Empty or unused registered epochs require no special premise.
Independent review found no correctness issue. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The generated restarted selector/kernel and its conditional action law now
compile separately. This assembly remains distinct because its regret
integrand uses the global scheduled probability. The restart-specific
probability integrand and schedule-aligned fiber decomposition now compile in
`TsallisOracleRestartPredictableRegret`; epoch-local law/expected-regret
transport now compiles in `TsallisOracleRestartExpectedRegret`.

## 2026-07-28 Generated Oracle-Restart Trajectory Action Law

`TSALLIS-ORACLE-RESTART-GENERATED-TRAJECTORY-ACTION-LAW` is `leanCompiled` in
`BanditRLProof/TsallisOracleRestartGeneratedTrajectory.lean`. It packages the
restart schedule contract, inclusive epoch-suffix reindexing and
measurability, boundary/continuation distributions, a measurable
finite-action `HistoryAlgorithm`, the canonical Markov trajectory kernel,
the actual-time probability surface, and the successor conditional-action
law given the complete global prefix.

Focused and root-imported `Tests.Basic` builds pass. External canaries check
both endpoints of a concrete suffix, never-restart and restart-every-round
distribution/probability reductions, and a full external consumer of the
`condDistrib` theorem. The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

This closes process generation and action-law identification only. It does
not establish fresh independent epoch laws, concentration, or final dynamic
regret. The restart-specific
predictable-regret integrand and direct schedule-fiber compatibility now
compile downstream, and fixed-comparator first-moment/epoch integral transport
now compiles after that. Independent review found no process-law correctness
issue; its metadata, regularity, and canary observations were resolved.

## 2026-07-28 Oracle-Restart Predictable Dynamic-Regret Assembly

`TSALLIS-ORACLE-RESTART-PREDICTABLE-DYNAMIC-REGRET-ASSEMBLY` is
`leanCompiled` in
`BanditRLProof/TsallisOracleRestartPredictableRegret.lean`. The module defines
restart-specific fixed- and moving-comparator predictable environment regret,
proves both never-restart reductions, and proves the fixed-plus-moving
identity under `best ∈ arms`.

Its finite epoch registry is the image of `schedule.start` over the inclusive
horizon, so coverage is proved internally. The moving regret is exactly the
sum over schedule fibers, without an independent epoch map or compatibility
premise. Pointwise `C*sqrt(fiber.card)` certificates yield both the
schedule-epoch and explicit switch-count square-root endpoints.

Focused and `Tests.Basic` builds pass. External canaries cover the concrete
never/every restart registries, both never-restart regret reductions,
fixed-plus-moving decomposition, exact fiber decomposition, and the final
switch-count endpoint. Independent review found no P0/P1 issue; the omitted
`best ∈ arms` contract and missing moving/fixed-plus canaries were added. The
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

This is deterministic pointwise regret assembly for the generated restart
probability surface. It does not prove fresh independent epoch laws,
the pathwise epoch estimated-regret certificate, a schedule-cardinality
theorem derived from a change law, concentration, or final dynamic regret.
Fixed-comparator law/expected-regret transport now compiles downstream;
schedule cardinality remains a separate leaf.

## 2026-07-28 Oracle-Restart Epoch Fixed-Comparator Regret Transport

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-FIXED-COMPARATOR-REGRET-TRANSPORT` is
`leanCompiled` in
`BanditRLProof/TsallisOracleRestartExpectedRegret.lean`. The generated action
law now retains environment plus global prefix, which is the conditioning
surface required by predictable losses. Boundary and continuation policies
both have strictly positive arm probabilities.

The module applies the generic mixed/weighted importance-sampling
first-moment API at time zero and every successor, proves measurability,
finite-simplex and bounded integrability, and sums the resulting identities
over each actual schedule fiber. Point masses rewrite to the existing
arm-valued epoch regret using `schedule.start t = epoch`. Expected epoch
certificates then feed the compiled finite Cauchy layer and produce both
schedule-epoch and switch-count expected moving-regret endpoints. The module
also defines the stored-reward restart estimator, proves its a.e. equality with
the predictable estimator at each time and epoch, identifies its point-mass
epoch integral with the same environment regret, and exposes schedule/switch
consumers that accept stored-reward certificates directly.

Focused and `Tests.Basic` builds pass. External canaries cover per-time first
moments, both point-mass epoch integral equalities, and the predictable and
observed final expected switch-count consumers. Independent review found no
correctness issue and confirmed that no fresh-run independence is used. The
axiom audit of the observed transport reports only `propext`,
`Classical.choice`, and `Quot.sound`.

This closes law and expected-regret transport. The downstream
`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-SCORE-ALIGNMENT` leaf now also compiles:
actual probabilities and stored-reward estimators equal scheduled local-time
surfaces on a shifted path; visited fibers are contiguous translated ranges
with exact cardinality; and actual observed point-mass epoch estimated regret
has the scheduled pathwise FTRL stability-plus-penalty bound.

Its local APIs are the restart and scheduled score surfaces,
`OracleRestartSchedule.start_*`, `Finset.max'`, `Finset.sum_image`, and
`Finset.card_image_of_injective`. Its only substantive contracts are finite
nonempty decidable arms, a valid deterministic schedule, visited epoch,
best-arm membership, and positive nonincreasing local eta. Focused/root/tests
and external canaries pass; independent review confirmed the pathwise route
and public-import axiom audit is baseline only.

The downstream
`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-EXPECTED-STABILITY-TRANSPORT` leaf now
also compiles. It uses the environment-plus-global-prefix conditional action
law of the single generated restart trajectory, proves coarse and refined
successor stability transport, covers global time zero, and exposes an
arbitrary-time finite-mass-scaled endpoint. With a probability prior it sums a
contiguous actual epoch prefix to a literal cardinality bound and integrates
the pathwise FTRL inequality, yielding an actual observed epoch expected
estimated-regret bound by cardinality plus deterministic penalty.

Focused and `Tests.Basic` builds and external canaries pass. Axiom audit is
baseline only. Independent review's refined-branch, time-zero, mass-scaling,
and deterministic-schedule concerns are reflected in the statements and
contracts. No fresh epoch law or shifted-trajectory pushforward equality was
introduced.

The remaining analytic gap is refined finite-sum control plus local-rate and
penalty tuning to derive `C*sqrt(fiber.card)`. The compiled coarse certificate
is linear in cardinality. A law-derived schedule-cardinality theorem and final
generated dynamic regret remain open.

## Restart-local refined stability tuning

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-REFINED-STABILITY-TUNING` is now compiled
in `BanditRLProof.TsallisOracleRestartRefinedStabilityTuning`. The concrete
schedule `eta_t = 1/(2*sqrt(t+1))` turns the refined successor bounds into an
actual shifted-prefix expectation of at most
`4*sqrt(K)*sqrt(localHorizon+1)`. A separate deterministic argument bounds the
terminal point-mass half-Tsallis penalty by the same quantity.

The visited-epoch consumer derives the local-horizon witness from epoch
membership and returns the assembly-shaped certificate
`integral observedEpochEstimatedRegret <=
(8*sqrt(K))*sqrt(epochRounds.card)`. It stays on the single global restart law
and requires no caller eta contracts. Focused/root/tests and the external
cardinality canary pass; public-import axiom audit is baseline only.

This closes the expected local `C*sqrt(fiber.card)` gap. It does not derive the
number of epochs from a reward-law switch count, instantiate a concrete
moving-comparator law, optimize constants, or prove complete Tsallis-INF.

## Generated oracle-restart dynamic regret

`TSALLIS-ORACLE-RESTART-GENERATED-DYNAMIC-REGRET` is now compiled in
`BanditRLProof.TsallisOracleRestartGeneratedDynamicRegret`. It feeds the
visited-epoch certificate into the existing observed-to-predictable
moving-comparator assembly and proves

`E[moving regret] <=
  (8*sqrt(K))*sqrt(scheduleEpochs.card)*sqrt(T+1)`.

With the explicit contract `scheduleEpochs.card <= switches + 1`, a second
theorem proves the corresponding
`(8*sqrt(K))*sqrt(switches+1)*sqrt(T+1)` endpoint. The same one global
generated restart law is retained throughout. Focused and external builds pass
and the public-import axiom audit is baseline only.

This closes the concrete generated dynamic-regret consumer, but not a
law-derived epoch-count theorem. Selecting restart times from a reward law and
proving the cardinality contract are the next distinct obligations; constants
and complete Tsallis-INF also remain open.

## Global-mean-switch oracle restart

`TSALLIS-ORACLE-RESTART-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET` is now
compiled in `BanditRLProof.TsallisOracleRestartGlobalMeanSwitchCount`. A
generic change predicate generates a valid restart schedule with exact epoch
registry `{0}` plus successors of the filtered change times. Specializing to
finite-arm population-mean changes proves
`epochs.card = globalMeanSwitchCount(T) + 1`.

The same module proves that every arm mean is constant within each resulting
epoch, so the mean-maximizing arm selected at the epoch start remains
mean-maximizing at every epoch round. Under a.e. `[0,1]` reward support, a
compiled loss-gap bridge proves that this raw-mean comparator is also optimal
for the clipped loss. Under the concrete independent roundwise reward-vector
product law, the generated expected moving-comparator regret is integrable and bounded by
`8*sqrt(K)*sqrt(globalMeanSwitchCount(T)+1)*sqrt(T+1)`.

No caller schedule, comparator, count, variation, or local-rate witness
remains. This is a population-mean oracle using the complete law sequence, not
an observed-reward detector. Detection delay/false alarms, high-probability
regret, sharper constants, dependent laws, and complete Tsallis-INF remain
open. Independent review's raw-mean/clipped-loss mismatch was resolved by
adding the unit-support contract and the compiled nonnegative loss-gap theorem.

## Canonical Conditional Reward Foundation

`COND-EXPECT-REWARD` now has a compiled theorem-facing endpoint in
`BanditRLProof.ConditionalRewardFoundation`. On the canonical reward-only
`historyStepKernelFamily` trajectory measure it exposes successor conditional
mean zero, successor conditional sub-Gaussian MGF witnesses at deterministic
historywise proxy ceilings, and the zero-initialized finite-sum
Azuma-Hoeffding upper tail. A reusable
`ProbabilityTheory.HasCondSubgaussianMGF.integrable` wrapper removes the last
caller ambient-integrability premise from this canonical mean-zero route.

This does not identify conditional laws for an arbitrary ambient process.
Such consumers must still supply an initial/successor `condDistrib` or
selected-law source. Uniform-time confidence, arm-wise empirical means,
observed change detection, and final UCB/ETC/RL routes remain open.

## OFUL Elliptical Potential

`OFUL.standardLogDeterminantAndEllipticalPotential` now closes the deterministic
elliptical-potential route as one theorem-facing endpoint. Under positive
regularization and a uniform squared-feature norm ceiling, it simultaneously
bounds the terminal Gram determinant and the clipped inverse-quadratic update
sum by the standard logarithmic dimension/radius budget.

This is deterministic finite-dimensional linear algebra. It does not provide
the vector self-normalized martingale tail, confidence ellipsoid, optimism
argument, or final OFUL regret theorem. Those are the remaining probabilistic
and algorithmic layers.

## OFUL Fixed-Direction Exponential Supermartingale

`BanditRLProof.OFULSelfNormalizedConfidence` now compiles the first
probabilistic edge of the OFUL route. Its theorem-facing endpoint proves a
zero-budget fixed-tilt MGF certificate for the finite sum of predictable
scalar projections times conditionally sub-Gaussian noise, with the exact
quadratic compensation. A bounded-projection wrapper derives the exponential
integrability required by the local composition API.

This closes only the deterministic-horizon fixed-direction precursor. The
scalar, finite-product, and diagonal-coordinate Gaussian
quadratic-exponential identities now also compile in
`BanditRLProof.OFULGaussianMixture`, ending in the determinant and
inverse-diagonal score-quadratic form under coordinatewise `0 <= q_i`.
`BanditRLProof.OFULGaussianSpectralMixture` now transports that identity
through Mathlib's orthonormal eigenbasis for every real PSD matrix `A` and
collects the result as
`sqrt(det(1+A))^-1 * exp(score^T (1+A)^-1 score / 2)`.

`BanditRLProof.OFULGaussianCovarianceMixture` now transports the normalized
identity through `multivariateGaussian 0 V_0^-1` for arbitrary
positive-definite `V_0`. Under `G.PosSemidef`, it collects the exact endpoint
as
`sqrt(det V_0 / det(V_0+G)) *
  exp(score^T (V_0+G)^-1 score / 2)`.
No caller integrability, measurability, or nonempty-coordinate premise is
exposed by this deterministic integral theorem.

`BanditRLProof.OFULGaussianMixtureMeasurability` now supplies the random
product-space surface. Measurable score and coordinatewise measurable Gram
entries imply joint measurability of
`ENNReal.ofReal (exp(<score omega,theta>-<theta,G omega theta>/2))`.
Mathlib's Tonelli theorem then rewrites the product lintegral as the iterated
lintegral for every `SFinite` parameter law, with a direct
`N(0,V_0^-1)` wrapper.

`BanditRLProof.OFULFiniteHorizonScoreGram` now defines the stochastic
finite-horizon score `S_n` and variance-weighted Gram `G_n`, proves
`G_n.PosSemidef`, and identifies the compensated fixed-direction sum with
`<S_n,theta>-<theta,G_n theta>/2`. It transports the MGF certificate to the
real expectation bound and then, by symmetric Tonelli, to a product-space
`lintegral <= 1` for every probability direction law and for
`N(0,V_0^-1)`.

`BanditRLProof.OFULGaussianEvaluatedMixture` now evaluates that Gaussian
direction integral samplewise. Fernique supplies integrability under
`G_n.PosSemidef`; with deterministic `V_0.PosDef`, the exact inner
`ENNReal` integral is the determinant-ratio inverse-Gram exponential. Tonelli
then converts the product bound into the outer sample `lintegral <= 1` for
that evaluated expression.

`BanditRLProof.OFULSelfNormalizedMarkov` now closes the deterministic-horizon
vector self-normalized tail. Mathlib Markov transport converts the evaluated
`ENNReal` moment into the generic variance-weighted probability theorem.
The common-`R` wrapper proves `G_n(R^2)=R^2 sum x_i x_i^T`, cancels that
scale from the determinant ratio, and rewrites the inverse quadratic form,
yielding the exact paper-facing radius
`2 * R^2 * log(sqrt(det V_n / det V_0) / delta)`.

`BanditRLProof.OFULConfidenceEllipsoid` now consumes that vector tail. It
defines the finite-horizon response statistic and ridge estimate, proves the
exact error decomposition
`thetaHat_n-thetaStar = V_n^-1 S_n - V_n^-1 V_0 thetaStar`, identifies the
inverse-score matrix norm with the self-normalized quadratic form, and
transports confidence-radius failure into the compiled tail. Its terminal
theorem bounds the confidence-ellipsoid bad event by `ENNReal.ofReal delta`
for `0 < delta <= 1` and an explicit samplewise regularization-bias cap.

`BanditRLProof.OFULScalarRegularizationBias` now discharges the generic bias
premise for `V_0=lambda I`. Its deterministic energy proof yields
`||V_n^-1(lambda thetaStar)||_(V_n) <= sqrt(lambda) ||thetaStar||_2` from
`0 < lambda` and Gram PSD, and its terminal wrapper uses
`euclideanLength thetaStar <= S` to expose the standard
`noiseRadius + sqrt(lambda) S` confidence radius.

`BanditRLProof.OFULFiniteActionOptimism` now compiles the weighted dual-norm
bound, finite score argmax, pointwise comparator-gap certificate, and a
fixed-horizon theorem bounding the existence of any action-gap violation by
`ENNReal.ofReal delta`. Candidate features may depend on the sample because
the proof only includes the violation event into the confidence bad event.

`BanditRLProof.OFULMeasurableRecursiveSelection` now closes measurable
deterministic tie-breaking for `Fin K` and canonical recursive
selected-action/feature alignment. It uses the existing strict finite argmax,
packages a deterministic history kernel, and transports selector-graph
support from the canonical history/action composition-product law.

`BanditRLProof.OFULConcreteHistoryRidgeSelection` now closes that concrete
state gap. For an inclusive finite history at index `n`, it extracts the
observed arm features and Real responses at coordinates `0,...,n`, evaluates
the scalar-ridge state at horizon `n+1`, and proves every fixed-arm optimistic
score measurable. The inverse-Gram proof is local and finite-dimensional:
determinants are finite sums/products, adjugate entries are determinants of
row updates, and `Matrix.inv_def` supplies the nonsingular inverse.

The same module packages the concrete strict-fold selector as a deterministic
history algorithm and proves that the feature of the actual canonical
successor action agrees almost surely with the feature selected from the
realized ridge state. The process endpoint accepts any valid
`Thompson.HistoryEnvironment (Fin K) Real`; its feedback laws are already
packaged as Markov kernels, and no independence is inferred. These statements
require no positivity or confidence law: `lambda`, `R`, `delta`, and `S` are
arbitrary for measurability.

`BanditRLProof.OFULUniformTimeConfidence` now closes the generic
deterministic finite-window confidence budget. It names the scalar-ridge
failure event, unions it over exactly `n <= horizon`, proves the simultaneous
confidence complement, and exposes both arbitrary `(0,1]` schedules and the
equal allocation `delta/(horizon+1)`. The scheduled failure probability is
bounded by the sum of its budgets; the equal-share endpoint is bounded by
`ENNReal.ofReal delta`.

This is not an infinite-horizon anytime theorem. It uses a finite union bound,
requires the fixed-time sub-Gaussian and response contracts only below the
chosen horizon, and does not identify the abstract process with the canonical
generated history algorithm.

`BanditRLProof.OFULAllTimeConfidence` now closes the corresponding
single-process all-time concentration leaf. Its general endpoint applies
`MeasureTheory.measure_iUnion_le` and `ENNReal.tsum_le_tsum` to the countable
union of fixed-time scalar-ridge failures. The concrete schedule
`delta / ((n+1)*(n+2))` is proved positive, at most one, and to have exact
`ENNReal` sum `ENNReal.ofReal delta` by a finite reciprocal telescope,
`HasSum.toNNReal`, and `ENNReal.hasSum_coe`. The terminal theorem therefore
bounds one simultaneous deterministic-horizon failure event by `delta`.

The contracts are all-time versions of the fixed-time source: a Standard
Borel probability space, finite decidable nonempty features, positive
regularization/noise scale/budget, theta norm control, predictable features,
adapted zero-initialized noise, deterministic projection domination, and
all-time conditional sub-Gaussian and response laws. No event measurability,
independence, stationarity, bounded rewards, feature ceiling, stopping-time
claim, generated policy law, or regret integrability is added. Retrieval used
the compiled fixed-time confidence route, Mathlib countable-measure and
infinite-sum APIs, the Abbasi-Yadkori paper card, and the OFUL weapon only as
route inspiration; targeted local retrieval found no pre-existing
countable-union telescope declaration.

Status is `leanCompiled`, root imported, focused/root/`Tests.Basic` built,
externally canaried for the exact schedule and full terminal theorem, and
baseline-axiom audited. Independent review found no correctness/P0/P1 issue;
its stale-status and direct-import-ledger findings are resolved, and the full
project check passes. Failure policy: do not identify the existing
horizon-dependent generated algorithm family with one anytime policy. The
separate scheduled canonical consumer described next is required for that
one-policy interpretation.

`BanditRLProof.OFULScheduledAllTimeConfidence` now compiles that scheduled
generated-process layer under an explicit all-time residual-law source. At
history index `n`, the strict-fold selector uses
`allTimeTelescopingDelta delta (n+1)`, exactly matching the confidence event
at horizon `n+1`. The module proves scheduled score/action measurability and
maximality, packages one fixed `HistoryAlgorithm`, constructs the strict-past
predictable feature and residual, proves simultaneous a.e. equality with the
actual selected features, and transports the countable confidence event back
to the actual canonical trajectory.

The terminal event existentially quantifies every successor round and states
that the true comparator gap exceeds twice the matching scheduled confidence
radius times the selected confidence width. Exact finite-history/trajectory
ridge-state identities and the existing optimism theorem show this event is
a.e. contained in the countable confidence failure event, hence its measure
is at most `ENNReal.ofReal delta`.

The regularity contract is `0<K`, finite decidable nonempty features,
`0<lambda`, `0<R`, `0<delta<=1`, theta norm control, a valid Real-reward
history environment, and an all-time conditional sub-Gaussian MGF law for the
scheduled predictable residual on this one trajectory measure. No
independence, stationarity, bounded rewards, feature ceiling, integrability,
event measurability, cumulative-width bound, stopping-time selection, or
regret premise is introduced. Status is `leanCompiled`, root imported,
focused/root/`Tests.Basic` built, with all 28 declarations checked and
external canaries for generated all-time confidence and the full existential
gap-tail endpoint.

The concrete scheduled law route now also compiles in the same module.
Algorithm-parametric canonical reward bridges identify the initial reward law
under an explicit Dirac initial-action contract and the successor reward
`condDistrib`/trimmed `condExpKernel.map` law through
`Thompson.historyStepKernel`. The scheduled step marginal is then rewritten to
`environment.feedback` at the scheduled selected action.

`canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment`
constructs the all-time source from
`CanonicalLinearSubgaussianEnvironmentLaw`, and the direct terminal wrapper
`measure_telescopingCanonicalHistoryTrajectoryAllTimeSuccGapViolationSet_le_of_linearSubgaussianEnvironment`
therefore needs no caller-provided residual law. The contracts remain
kernel-section centered sub-Gaussian laws, not independence, stationarity, or
bounded rewards.

Failure policy: one-policy all-time confidence and successor-gap control is
closed under the concrete environment law. This is not cumulative regret or a
stopping-time theorem. The next route is an all-horizon cumulative-gap tail on
the same scheduled trajectory using deterministic radius-width summation.

`BanditRLProof.OFULSelectedWidthSummation` now closes the deterministic width
consumer. It proves
`clippedConfidenceWidth V x = min 1 (confidenceWidth V x)` for positive
definite `V`, applies finite Cauchy--Schwarz to the compiled logarithmic
elliptical potential, and exposes the resulting
`sqrt(T) * sqrt(2*d*log(1+T*L2/(d*lambda)))` bound directly for arbitrary
selected-action sequences. The raw-width endpoint retains an explicit
pointwise `width <= 1` contract.

The generated-trajectory confidence/index hookup, cumulative successor
optimism-gap assembly, concrete feedback-kernel residual-law producer, and
standard radius-times-selected-width assembly now compile. The trajectory
consumer uses the complete actual prefix `0,...,horizon` with
`T = horizon + 1`, while the gap sum covers only successor actions
`1,...,horizon`; this preserves the true prefix Gram at every width. The raw
route keeps `confidenceWidth <= 1` explicit. The normalized downstream
consumer now derives that premise under `L2 <= lambda`; initial-round
accounting and expected bad-event control remain separate, so this theorem is
not recorded as complete regret.

### Concrete OFUL history-environment reward law

`OFUL-HISTORY-ENVIRONMENT-LINEAR-SUBGAUSSIAN-REWARD-LAW` now compiles in
`BanditRLProof.OFULHistoryEnvironmentRewardLaw`. It identifies the initial and
successor reward laws, converts Real-valued `condDistrib` surfaces to trimmed
`condExpKernel.map` equality without `Countable Real`, freezes the strict-past
linear center, and constructs `CanonicalPredictableScalarRidgeResidualLaw`
from `CanonicalLinearSubgaussianEnvironmentLaw`.

This closes the stochastic source producer and reaches the existing
successor-gap delta tail. Its normalized radius-width consumer now compiles
under `L2 <= lambda`. It does not infer sub-Gaussianity from Markovness,
include initial-round regret, or control the expected bad-event contribution.

### Standard OFUL radius-width successor-gap tail

`OFUL-GENERATED-TRAJECTORY-STANDARD-RADIUS-WIDTH-GAP-TAIL` now compiles in
`BanditRLProof.OFULGeneratedTrajectoryRadiusWidth`. It names the deterministic
standard log-determinant budget, a uniform confidence-radius upper bound, the
selected-width budget, and their doubled product. Every prefix radius
`n <= T` is bounded by the terminal standard radius, and the exact scalar Gram
is identified with the regularized prefix feature Gram.

The generated consumer applies selected-width summation to all actual actions
at times `0,...,horizon`, hence `T = horizon + 1`, and removes only the
nonnegative time-zero radius-width term. It does not build a fictitious Gram
from successor actions alone. The resulting deterministic successor-gap
violation event is included in the concrete linear-sub-Gaussian environment
violation event and therefore has canonical measure at most
`ENNReal.ofReal delta`.

This base route still assumes every realized raw confidence width before
`horizon + 1` is at most one. The normalized downstream leaf below discharges
that premise when `L2 <= lambda`. Time-zero gap control and expected bad-event
loss remain subsequent leaves.

### Normalized OFUL radius-width successor-gap tail

`OFUL-GENERATED-TRAJECTORY-NORMALIZED-RADIUS-WIDTH-GAP-TAIL` now compiles in
`BanditRLProof.OFULNormalizedRadiusWidth`. For
`V = lambda I + sum_{s<T} x_s x_s^T`, `z = V⁻¹ x`, and `q = xᵀz`, inverse
cancellation and the exact regularized-Gram energy expansion give
`lambda * ||z||^2 <= q`. Finite Cauchy--Schwarz gives
`q^2 <= ||x||^2 * ||z||^2`; therefore `||x||^2 <= lambda` and
inverse-quadratic nonnegativity imply `q <= 1`.

The canonical wrapper derives `||x||^2 <= lambda` from the arm-feature bound
`||x||^2 <= L2` and the explicit normalization `L2 <= lambda`. It then reuses
the standard deterministic and concrete linear-sub-Gaussian measure
consumers, so the terminal theorem has no pathwise `hwidth` premise. Targeted
retrieval found no direct finite-matrix inverse-Loewner API with the required
shape; the compiled route uses local positive-definite inverse cancellation,
the exact energy expansion, and `Finset.sum_mul_sq_le_sq_mul_sq`.

The explicit sufficient normalization used by this leaf is
`L2 <= lambda`; the lower-level inverse-quadratic theorem only requires the
selected vector's squared norm to be at most `lambda`. The terminal theorem
still excludes the fixed time-zero gap and expected bad-event loss, and it is
not a complete OFUL regret theorem.

### All-round OFUL standard-gap tail

`OFUL-GENERATED-TRAJECTORY-ALL-ROUND-STANDARD-GAP-TAIL` now compiles in
`BanditRLProof.OFULInitialRoundGap`. Finite-dimensional Cauchy--Schwarz and
the parameter/arm norm envelopes bound any two-arm linear gap by
`2*S*sqrt(L2)`. The canonical time-zero action is the fixed arm `0` almost
surely, so this charge covers the previously omitted initial round.

The named all-round violation event sums over
`Finset.range (horizon + 1)`. After `Finset.sum_range_succ'` splits time zero,
its violation implies the compiled normalized successor violation almost
surely; `measure_mono_ae` therefore yields the same
`ENNReal.ofReal delta` terminal bound without a pathwise `hwidth` premise.
At this boundary, the remaining OFUL gap was the measurable bad-event loss
envelope and expectation integration; the next leaf below closes it.

### Expected finite-window OFUL pseudo-regret

`OFUL-GENERATED-TRAJECTORY-EXPECTED-PSEUDOREGRET` now compiles in
`BanditRLProof.OFULExpectedRegret`. The complete comparator-gap sum is
measurable and bounded in absolute value by
`(horizon+1)*2*S*sqrt(L2)`, so it is integrable. A generic theorem splits the
expectation at the all-round violation event: the standard gap budget applies
off the event, while a measurable indicator charges the deterministic
envelope on it.

The concrete environment theorem converts the compiled
`ENNReal.ofReal delta` tail to a Real probability bound and obtains
`standardScalarAllRoundGapBound + envelope*delta`. With a certified optimal
fixed arm, the integral is also nonnegative and therefore has the intended
pseudo-regret semantics. The terminal corollary chooses
`delta_T=1/(horizon+1)`, making the bad-event charge exactly
`standardScalarInitialGapBound S L2`; the algorithm's local confidence input
is `1/(horizon+1)^2`.

This closes finite-window expected fixed-optimal-arm pseudo-regret under the
concrete linear-sub-Gaussian environment and `L2<=lambda`. It does not assert
an anytime, minimax, contextual, dynamic-regret, or asymptotic theorem. A
closed-form rate presentation is supplied by the next leaf.

### Explicit finite-window OFUL expected rate

`OFUL-GENERATED-TRAJECTORY-EXPLICIT-EXPECTED-PSEUDOREGRET-RATE` now compiles
in `BanditRLProof.OFULExpectedRegretRate`. It proves that the outer budget
`1/(horizon+1)`, after equal-share uniform-time scheduling, is exactly the
algorithm parameter `1/(horizon+1)^2`. It then normalizes the confidence
radius using Mathlib log/sqrt identities.

Writing
`B_T = d*log(1+(T+1)*L2/(d*lambda))`, the terminal expected pseudo-regret is
nonnegative and at most

`4*S*sqrt(L2) + 2*(R*sqrt(B_T+4*log(T+1))+sqrt(lambda)*S)
  *sqrt(T+1)*sqrt(2*B_T)`.

The theorem retains the same concrete linear-sub-Gaussian environment,
certified optimal arm, feature ceiling, and `L2<=lambda` contracts. This
closes the explicit finite-window rate presentation; its separate asymptotic
consumer is recorded below. It is not itself a minimax, anytime, contextual,
or dynamic-regret theorem. Focused,
root, `Tests.Basic`, and full project checks pass. Independent review found
no P0/P1 issue; its budget-notation and direct composition-canary findings
were resolved. The public axiom audit is baseline-only.

### Asymptotic OFUL expected rate

`OFUL-GENERATED-TRAJECTORY-ASYMPTOTIC-EXPECTED-PSEUDOREGRET-RATE` now
compiles in `BanditRLProof.OFULExpectedRegretAsymptotics`. It fixes the
feature type, model parameters, action features, environment, and certified
best arm while the horizon varies, names the exact canonical expected
pseudo-regret for the generated algorithm at parameter `1/(T+1)^2`, and
proves

`canonicalStandardExpectedPseudoRegret ... =O[Filter.atTop]
  (fun T => sqrt(T+1) * log(T+1))`.

The support route proves the standard determinant budget and augmented
confidence budget are `O(log(T+1))`, transports square roots and products
through Mathlib's asymptotics API, absorbs `sqrt(log(T+1))` into
`log(T+1)` eventually, and applies the compiled pointwise explicit bound.
The actual imports are `Mathlib.Analysis.Asymptotics.Lemmas`,
`Mathlib.Analysis.SpecialFunctions.Log.Base`, and
`Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`; the previously recorded
aggregate asymptotics module does not exist in the pinned checkout.

The contracts remain `0<K`, finite decidable nonempty features,
`0<lambda`, `0<R`, `0<=S`, `0<=L2`, the arm squared-norm ceiling,
`L2<=lambda`, a certified optimal fixed arm, and the concrete canonical
linear-sub-Gaussian environment law. This is a fixed-model expected-regret
asymptotic corollary, not a minimax, anytime, high-probability all-horizon,
contextual, dynamic-regret, uniform-over-parameters, or unrestricted
linear-bandit theorem. Focused/root/`Tests.Basic` and full checks pass.
Public signature checks cover all seven declarations, while external proof
canaries instantiate the explicit-bound helper and full terminal composition.
Independent review found no P0/P1 or mathematical/Lean semantic issue; its
stale-snapshot and canary-description findings were resolved. The public
axiom audit is baseline-only.

### OFUL expected-average consistency

`OFUL-GENERATED-TRAJECTORY-EXPECTED-AVERAGE-PSEUDOREGRET-CONSISTENCY` now
compiles in `BanditRLProof.OFULExpectedRegretConsistency`. It defines the
exact complete canonical expected pseudo-regret divided by `T+1` and proves

`Tendsto (canonicalStandardExpectedAveragePseudoRegret ...)
  Filter.atTop (nhds 0)`.

The analytic bridge is
`sqrt(T+1)*log(T+1)=o(T+1)`. It is proved from Mathlib
`isLittleO_log_rpow_atTop` at exponent `1/2`, `Real.sqrt_eq_rpow`,
`IsLittleO.mul_isBigO`, and `Real.mul_self_sqrt`. The compiled canonical
`IsBigO` theorem then yields little-o regret through
`IsBigO.trans_isLittleO`, and `IsLittleO.tendsto_div_nhds_zero` closes the
average.

All model and regularity contracts are unchanged from the fixed-model
asymptotic theorem. This is expected-value convergence for a horizon-indexed
algorithm family whose horizon-`T` parameter is `1/(T+1)^2`. It is not
pathwise or probability convergence, almost-sure Hannan consistency, an
anytime theorem, or consistency of one horizon-independent policy.
Focused/root/`Tests.Basic` and full project checks pass. Public signature
checks cover all five declarations, while external proof canaries instantiate
the analytic little-o bridge and terminal canonical convergence theorem.
Independent review found no P0-P3 issue, and the public axiom audit is
baseline-only.

### OFUL explicit high-probability pseudo-regret rate

`OFUL-GENERATED-TRAJECTORY-EXPLICIT-HIGH-PROBABILITY-PSEUDOREGRET-RATE`
now compiles in `BanditRLProof.OFULHighProbabilityRegretRate`. With

`B_T = standardScalarLogDetBudget lambda (T+1) L2`

and

`H_T(delta) = B_T + 2*log((T+1)/delta)`,

the module proves the exact confidence-radius identity at algorithm parameter
`delta/(T+1)` and rewrites the named all-round budget as

`2*S*sqrt(L2) +
  2*(R*sqrt(H_T(delta))+sqrt(lambda)*S)*sqrt(T+1)*sqrt(2*B_T)`.

The terminal theorem fixes a certified optimal arm, proves the complete
`0,...,T` trajectory pseudo-regret is pointwise nonnegative, and bounds the
measure of the strict exceedance event by `ENNReal.ofReal delta`. Its
contracts are exactly the existing canonical linear-sub-Gaussian contracts,
including `0<delta<=1` and `L2<=lambda`; no new law transport, integrability,
independence, or pathwise-width premise is introduced.

The focused module, root import, and `Tests.Basic` builds pass. All six public
declarations have signature checks; external canaries instantiate the radius
identity and full terminal composition. The public axiom audit is
baseline-only. This is finite-window high probability, not anytime,
simultaneous all-horizon, minimax-optimal, contextual, dynamic, or
uniform-over-parameter regret. Independent review found one P2 retrieval-only
statement truncation at `(Feature := Feature)`; the bracket-aware scanner and
CLI regression test resolve it, the declaration index now contains the full
strict-event conclusion, and `python3 tools/bandit.py check` passes.

## UCB Canonical Selected-Reward Consistency Route

`BanditRLProof.Algorithms.UCBArmStreamConditionalReward` now closes the adaptive
next-unused-coordinate law. In addition to complement independence, recursive
causality, and condition reconstruction, it defines measurable fibers of the
coordinate encoded by each successor `(finite history, action)` condition.
Those fibers and the corresponding stream branches are pairwise disjoint and
cover their full spaces. `Measure.restrict_iUnion`, `Measure.restrict_map`, and
`Measure.restrict_prod_eq_prod_univ` turn every branch into the restricted
condition marginal times `nu target.2`; `Measure.map_sum` and
`Measure.compProd_sum_left` reassemble the exact full joint law. Consequently
`armStreamReward_succ_condDistrib_ae_eq_nu` and the packaged environment
feedback law compile without a caller selected-law premise.

`BanditRLProof.Algorithms.UCBRealStationarySelectedRewardConsistency` transports
the exact `(finitePairHistoryOfTrace action reward n, action (n+1))` condition
marginal through the compiled complete trajectory `IdentDistrib`. The fresh
canonical `Kernel.trajMeasure` process therefore has the stationary selected-arm
law for its initial reward and every successor reward, a.e. on the corresponding
generated condition marginal. Its terminal theorem combines both reward-law
families with the same-process explicit `realHistoryNextArm` event and the
armwise-bounded expected-average pseudo-regret `Tendsto` result.

The focused modules, root import, and `Tests.Basic` compile with public checks
and generated-successor/terminal external canaries. The generic law needs only
positive finite arms and a Markov Real kernel; the terminal adds per-arm
probability laws and armwise a.s. interval support. No action-only conditioning,
moment substitute, global kernel equality on null histories, horizon-indexed
process, common interval, caller selected law, or pathwise/probability/a.s.
consistency claim is introduced.

## RL Finite Policy Trajectory Value Identity

`RL-FINITE-HORIZON-POLICY-TRAJECTORY-VALUE-IDENTITY` now compiles in
`BanditRLProof.RL.FiniteHorizonTrajectory`. The module constructs a true finite
`Fin n -> Action × State` trace, recursively composes policy-action and MDP
transition kernels, and proves every remaining-horizon kernel Markov. The
cumulative reward is jointly measurable; finite-range `Integrable.of_bound`
removes any caller reward-bound or integrability premise. Two nested Mathlib
`integral_compProd` expansions identify its statewise expectation with
`valueRemaining`, and the final `Measure.compProd` expansion proves the joint
trajectory expected return equals the initial-law integral of `valueAt 0`.

Contracts are finite state/action measurable spaces, the compiled MDP and
Markov-policy contracts, and a probability initial-state measure for the final
theorem. This closes policy trajectory generation and policy evaluation only.
Bellman optimality, a maximizing policy, occupancy recursion, optimism, and RL
regret remain open; literature cards are retrieval evidence, not local proofs.

## RL Finite-Horizon Bellman Optimality

`RL-FINITE-HORIZON-BELLMAN-OPTIMALITY` now compiles in
`BanditRLProof.RL.FiniteHorizonOptimality`. Mathlib `Finite.exists_max` supplies
a genuine Bellman-Q maximizing action. On a finite state space with measurable
singletons, `measurable_of_finite` makes that selector measurable, so the
greedy policy is constructed explicitly with deterministic Markov kernels.
Finite-type integrability and `integral_mono` establish transition, Bellman-Q,
and policy-Bellman monotonicity. Backward optimal values satisfy terminal and
chronological Bellman equations; decreasing induction proves universal policy
dominance and, separately, greedy-policy attainment at every stage.

The exact added contracts are nonempty finite actions and singleton-measurable
finite states. No initial law, reward bound, caller integrability, compactness,
occupancy, conditional expectation, optimism, UCB-VI, or regret premise is
used. The downstream occupancy/performance-difference route now compiles.

## RL Finite-Horizon Occupancy Regret

`RL-FINITE-HORIZON-OCCUPANCY-REGRET` now compiles in
`BanditRLProof.RL.FiniteHorizonOccupancyRegret`. `stateOccupancy` gives the
chronological policy-induced state laws and preserves probability.
`policyBellmanGap` is measurable and nonnegative. The induced-kernel integral
bridge expands `Kernel.map` and `Kernel.compProd`, then the recursive
`occupancyGapRemaining` theorem telescopes the finite gap sum to the integrated
optimal-policy value difference. The compiled trajectory/value identity turns
the same difference into `expectedRegret`; the final endpoint packages exact
occupancy equality, nonnegativity, and greedy-policy zero regret.

This closes a finite single-episode performance-difference bridge. It does not
provide an empirical MDP, estimated transition/reward model, confidence set,
optimistic bonus, multi-episode process, UCB-VI concentration event, or regret
rate. Those remain the next substantive RL gaps.

## RL Finite-Horizon Optimistic Bellman Certificate

`RL-FINITE-HORIZON-OPTIMISTIC-BELLMAN-CERTIFICATE` now compiles in
`BanditRLProof.RL.FiniteHorizonOptimisticCertificate`. Local true optimal-
Bellman upper inequalities and a zero terminal condition imply global
optimal-value optimism. Generic recursive occupancy sums are monotone under
pointwise stage-cost bounds. The certificate's policy residual sum telescopes
exactly to upper value minus policy value, agrees with the old occupancy gap
for the canonical optimal certificate, and bounds expected regret. A
pointwise residual-to-bonus inequality yields the final true-occupancy bonus
regret bound.

This removes the deterministic optimism-induction and episode-regret-
telescope gaps from the RL roadmap. The deterministic estimated-model
confidence producer now compiles downstream; empirical estimation and the
probability of its confidence contract remain open.

## RL Estimated-Model Optimistic Regret Producer

`RL-FINITE-HORIZON-ESTIMATED-MODEL-OPTIMISTIC-REGRET` now compiles in
`BanditRLProof.RL.FiniteHorizonEstimatedModelCertificate`. A stage-indexed
estimated reward/transition model and separate radii recursively generate the
optimistic values and deterministic greedy policy. Two-sided reward error and
transition-expectation error on the generated tail value imply both true-Q
optimism and a factor-two selected-radius residual bound. The existing
certificate/occupancy route converts these into global optimism and a
single-episode expected-regret bound.

Still missing are finite episode histories and visit counts, empirical reward
and transition estimators, concentration events proving these two-sided
errors, any required reward/value range or clipping contracts, cross-episode
filtration, bonus/martingale summation, and the final high-probability or
minimax UCB-VI theorem.

## RL Coordinate Model Confidence Transport

`RL-FINITE-HORIZON-COORDINATE-MODEL-CONFIDENCE-REGRET` now compiles in
`BanditRLProof.RL.FiniteHorizonCoordinateModelConfidence`. Mathlib
`integral_fintype` expands estimated and true next-state expectations into
finite singleton-mass sums. Coordinate transition errors and an absolute
envelope on the recursively generated tail upper value then bound the
expectation error by a finite coordinate-radius sum. Radius coverage packages
this result, together with the reward error, as the existing
`EstimatedModelPlan.Confidence`; the compiled optimism and single-episode
expected-regret endpoint follows unchanged.

This closes the deterministic finite-state coordinate/L1-to-Bellman bridge.
It does not construct empirical transition frequencies, visit counts, a
simultaneous confidence event or its probability. The next producer must
define those episode-history observables and prove reward plus singleton
transition-coordinate concentration before cross-episode regret assembly.

## RL Finite-Batch Empirical Model Producer

`RL-FINITE-HORIZON-FINITE-BATCH-EMPIRICAL-MODEL-CONFIDENCE-REGRET` now
compiles in `BanditRLProof.RL.FiniteHorizonEmpiricalModel`. Finite records
define visit counts, empirical reward means, next-state counts, normalized
positive-count PMFs, an explicit zero-count Dirac fallback, and a finite-state
Markov kernel. `FiniteBatchModel.plan` is therefore generated from empirical
statistics rather than supplied by the confidence consumer. Raw reward and
singleton-frequency error contracts transport through `CoordinateConfidence`
to the compiled optimism and single-episode expected-regret theorem.

The remaining gap is probabilistic, not an empirical-model placeholder. The
batch is not yet identified with measurable functions of generated episodes;
there is no simultaneous event, confidence probability, reward-range or
clipping theorem, count lower bound, episode filtration, failure-budget union
bound, cross-episode bonus sum, or cumulative/high-probability UCB-VI rate.

## RL IID Generated-Trajectory Batch Law

`RL-FINITE-HORIZON-IID-TRAJECTORY-BATCH-LAW` now compiles in
`BanditRLProof.RL.FiniteHorizonIIDTrajectoryBatch`. The previously arbitrary
finite records now have a concrete producer: a measurable pushforward of the
finite iid product of `MarkovPolicy.trajectoryMeasure`. Coordinate evaluation
recovers the genuine trajectory law, and `iIndepFun_pi` supplies independence
for fixed-stage source records and measurable statistics. A finite-product
map characterization transports that fact to record/statistic independence
directly under `iidEpisodeBatchMeasure`. Exact identities connect empirical
visit, reward, and transition aggregates to named independent per-trajectory
contributions. The measurable-space instance and field projection APIs are
owned with `EpisodeStep`; independent review's mapped-law P2 and both P3
findings are resolved. Focused, root, Tests, axiom, index, and full CLI gates
pass.

The remaining gap is no longer batch-law identification for fixed-policy iid
episodes. It is concentration and adaptivity. There is not yet a centered
bounded-variable tail for these contributions, a simultaneous finite
coordinate event, a visit-count lower bound, a reward/transition ratio theorem,
an adaptive episode filtration, confidence probability allocation, cumulative
bonus control, or a high-probability UCB-VI regret theorem. Reward randomness
beyond the deterministic `mdp.reward` field also requires a separate model.

## RL IID Fixed-Coordinate Count Confidence

`RL-FINITE-HORIZON-IID-COUNT-CONFIDENCE` now compiles in
`BanditRLProof.RL.FiniteHorizonIIDCountConcentration`. The fixed-policy iid
batch law now produces actual concentration, not only independence: each
fixed visit count and each fixed joint transition count has a two-sided
delta-calibrated tail around episode count times its single-trajectory mean.
The proof transports the common mean through mapped marginals, uses exact
count/cast algebra, and consumes the compiled `[0,1]` Hoeffding and independent
sub-Gaussian finite-sum APIs.

The route now makes the joint semantics explicit: the transition center is
the measurable event mass `P(S_h=s,A_h=a,S_{h+1}=s')`, lies in `[0,1]`, and is
at most `P(S_h=s,A_h=a)`. The total Hoeffding proxy is exactly `episodes / 4`.
Real count/deviation functions and both fixed-coordinate bad events are
measurable, so the next union route does not need to reconstruct that layer.
Independent review found no P0/P1/P2 and all P3 findings were resolved;
focused/full builds, external canaries, baseline axiom audit, and project gate
pass.

This does not yet prove a simultaneous confidence event. The bundled theorem
contains two separate inequalities and spends no shared failure budget. There
is also no occupancy lower bound, positive random denominator, empirical
transition-frequency ratio bound, stochastic reward-mean confidence,
adaptive episode filtration, cross-episode policy update, cumulative bonus
sum, or high-probability UCB-VI regret theorem.

## Closed Gap: Eligible Visit-Count Positivity

`RL-FINITE-HORIZON-IID-ELIGIBLE-VISIT-COUNT-POSITIVITY` now compiles. For each
coordinate in a caller-supplied finite eligible set, an expected-count margin
strictly larger than the common radius rules out realized count zero. The
measurable eligible zero-count union is included in the compiled simultaneous
bad event and inherits its global-delta tail; its complement exposes positive
Nat denominators directly.

The explicit margin remains essential because unreachable coordinates have
zero expectation. The next missing law is not denominator positivity: it is
the factorization of the named joint-transition probability into visit
probability times the true transition-kernel singleton mass. Empirical ratios
and reward confidence remain separate downstream gaps.

## Active Gap: Simultaneous IID Count Confidence

The route `RL-FINITE-HORIZON-IID-SIMULTANEOUS-COUNT-CONFIDENCE` is compiled.
It combines every finite visit and joint-transition count bad event under the
same mapped iid batch law, calibrates each at
`delta / Fintype.card CountCoordinate`, proves the union has measure at most
global `delta`, and recovers strict count bounds outside the measurable union.

No new probabilistic law transport is missing for this route: marginal laws,
independence, centered MGF witnesses, exact count identities, and each
coordinate tail compile. The finite index, exact cardinality, union-budget
assembly, and empty-horizon branch are now closed. The next separate gap is a
deterministic occupancy-margin contract that turns the simultaneous visit
deviation into positive visit counts; empirical conditional transition ratios
remain downstream of that denominator result.

## Closed Gap: Generated Stage-Transition Joint Factorization

`RL-FINITE-HORIZON-STAGE-TRANSITION-JOINT-FACTORIZATION` now compiles. The
generated fixed-policy population law satisfies
`stageTransitionJointProbability = stageVisitProbability * transitionMass`
for every stage/state/action/next-state coordinate, where `transitionMass` is
the Real singleton mass of the true MDP transition kernel.

The proof does not assume positive occupancy. It factors a singleton at the
action/next-state `compProd`, inducts through every earlier recursive trajectory
layer, transports the constant transition mass through the initial-state
`Measure.compProd`, and then converts ENNReal event masses to Real. A reachable
deterministic coordinate evaluates to one, an unreachable coordinate to zero,
and a horizon-two stage-one canary exercises successor-coordinate transport.
Independent review found no P0-P2; its two P3 findings were resolved by removing
unused singleton contracts and adding that successor-stage canary.

This closes population-law identification, not empirical ratio confidence.
The next gap is ratio algebra using the compiled positive eligible visit counts
and simultaneous visit/joint-count deviations. Reward confidence, adaptive
episode filtration, cumulative bonuses, and complete UCB-VI remain downstream.

## Closed Gap: Eligible Empirical Transition Singleton Confidence

`RL-FINITE-HORIZON-IID-ELIGIBLE-EMPIRICAL-TRANSITION-CONFIDENCE` now compiles.
For every caller-eligible stage/state/action coordinate whose genuine expected
count strictly exceeds the shared count radius, every next-state singleton obeys
`|empiricalTransitionMass - trueTransitionMass| < 2 * radius / visitCount`
outside the existing simultaneous-count event. That same measurable event keeps
its previously compiled mapped-iid-batch mass bound `<= ENNReal.ofReal delta`.

The proof uses the positive realized count from the eligibility margin, the
exact empirical `transitionCount / visitCount` law, both simultaneous count
deviations, and the compiled population joint factorization. The true kernel
singleton mass lies in `[0,1]`, so the joint and visit numerator errors sum to
at most twice the common radius before division by the positive realized count.
No additional next-state union budget is used.

Independent review found no P0-P1. Its stale-status and regularity/API ledger
observations were synchronized, and its semantic-coverage finding was resolved
with a concrete Bool-state four-record batch: visit count four, empirical
`true` mass `1/4`, true transition mass zero, and a public-theorem consumer that
reduces to the nonzero strict inequality `1/4 < 2 * radius / 4`.

This closes transition singleton-frequency confidence only on eligible
coordinates. The generated deterministic-reward exactness route below now
closes its reward-error consumer. Full empirical-model confidence still lacks
all-coordinate eligibility and the generated value-envelope/transition-radius
assembly. Adaptive episode policies, anytime confidence, cumulative regret, and
complete UCB-VI remain downstream.

## Closed Gap: Generated Empirical Reward Exactness

`RL-FINITE-HORIZON-IID-GENERATED-EMPIRICAL-REWARD-EXACTNESS` now compiles. The
current finite-horizon `MDP` has deterministic `reward : State -> Action -> Real`,
so trajectory-generated records do not require a separate noisy-reward
concentration theorem. A reusable `EpisodeBatch.RewardConsistent` contract now
gives `rewardSum = visitCount * mdp.reward`, and every positive-count empirical
reward cancels exactly to the true reward. Every `episodeBatchOfTrajectories`
satisfies that contract definitionally.

The eligible endpoint reuses the same simultaneous-count event: outside it,
reward-consistent batches have zero reward error and all next-state singleton
transition errors retain the compiled `2 * radius / visitCount` bound. No new
failure budget is allocated. The reward-consistency set is measurable, and
`ae_map_iff` proves that mapped iid episode batches satisfy it almost everywhere,
so the bundled endpoint no longer needs a caller-supplied support premise.
Canaries include a generated reward of seven and
an unvisited state where empirical reward remains zero while the true reward is
eleven, preventing accidental zero-count overstatement.

This closes the reward-error component only for generated/reward-consistent
records at eligible positive-count coordinates. Constructing a full
`FiniteBatchModel.Confidence` still requires all coordinates used by planning
to be eligible and a noncircular upper-value envelope plus transition-radius
coverage. Stochastic reward observations would require a different MDP model.
