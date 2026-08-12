# Bandit And RL Proof Backlog

## Accepted: Book Map Chapters 7--8 canonical completion

- Root: `BOOKMAP-CHAPTERS-7-8-CANONICAL-COMPLETION`, with independent gates
  `CH7-EXP3-CANONICAL-COMPLETION` and
  `CH8-TSALLIS-FTRL-CANONICAL-COMPLETION`.
- Chapter 7 evidence: typed horizon-tuned expected and fixed-window best-arm
  endpoints; fixed-process predictable/deviation parents, exact decomposition,
  and all-positive-prefix realized terminal; sparse endpoint with its explicit
  failure budget.
- Chapter 8 evidence: half-Tsallis minimizer regularity, scheduled generated
  action law and score alignment, all-rate expected stability/regret,
  fixed-gap self-bounding, exact IID mean-gap producer, and a concrete bounded
  nondegenerate two-arm IID Dirac-law application of the logarithmic generated-
  regret terminal, including exact means and a positive non-best gap.
- Boundary: the two chapter gates do not imply each other.  Horizon-free tuned
  EXP3, same-process best-arm aggregation, EXP3.P, paper-sharp/minimax complete
  Tsallis-INF, high-probability/realized Tsallis regret, and observed-reward
  restart detection remain distinct extensions.
- Acceptance evidence is recorded in
  `Tests/BookMapChaptersSevenAndEightCanary.lean`, the synchronized task/window/
  obligation/blueprint, and the repository/site gates.

## Accepted: Generated EXP3 Realized-Regret Geometric All-Time Tail

- Leaf: `EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL`.
- Lean statement: for one fixed generated process and supported comparator,
  the positive-prefix realized selected-loss regret crossing union at the sum
  of the scheduled parent budgets has outer measure at most `ofReal delta`.
- Local APIs/imports: accepted predictable-regret and realized-deviation
  all-time events; exact finite-prefix decomposition; membership/inclusion;
  finite union measure and ENNReal half-budget normalization.
- Proof route: split total delta between parent families -> prove realized
  regret equals predictable regret plus deviation -> include the combined
  event in the parent union -> add the two parent outer-measure bounds.
- Regularity: probability/Standard-Borel generated process, measurable action
  singletons, decidable nonempty arms, fixed positive eta, `0<gamma<1`, one
  predictable loss process, supported comparator, and positive delta; no event
  measurability, `delta<=1`, independence, stationarity, countable Action,
  supplied integrability, or new law transport.
- Retrieval/status: both accepted local all-time parents; fixed-horizon
  composition precedent; Mathlib measure/finite-sum/order cards; source cards
  placement only and weapons inspiration only. Six declarations,
  focused/root/Tests, five canaries, SafeVerify `34d6b6dd...5702`, and baseline
  axioms pass. Independent review found no P0/P1/P2/P3; lifecycle records are
  accepted; verified memory is `mem-2a0ffec376992850`; frontier shadow has zero
  mismatches; and the full harness passes.
- Failure policy/next leaf: add a finite supported-comparator union and
  best-arm external-regret surface. Do not claim that result here, or a tuned
  all-time rate, horizon retuning, Ville/Doob, mixture, optional stopping,
  self-normalization, general Freedman, horizon-free tuned EXP3, or EXP3.P.

## Accepted: Generated EXP3 Predictable-Regret Geometric All-Time Tail

- Leaf: `EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`.
- Lean statement: for one fixed generated process and supported comparator,
  the countable union of positive-prefix predictable-regret crossings at the
  scheduled fixed-horizon budget has outer measure at most `ofReal delta`.
- Local APIs/imports: fixed-horizon predictable-regret total tail; geometric
  confidence schedule; `measure_iUnion_le`; `ENNReal.tsum_le_tsum`.
- Proof route: exact `n+1` budget at inner share `geometricShare/2` -> parent
  outer-share tail -> countable subadditivity -> exact geometric tsum.
- Regularity: probability/Standard-Borel generated process, measurable action
  singletons, decidable nonempty arms, fixed positive eta, `0<gamma<1`, one
  predictable loss process, supported comparator, and positive delta; no event
  measurability, `delta<=1`, independence, stationarity, countable Action,
  supplied integrability, or new law transport.
- Retrieval/status: local predictable-Hedge/exploration/pure-cross/comparator
  and geometric schedule cards; Mathlib measure/finite-sum/order cards; source
  cards placement only and weapons inspiration only. Four declarations,
  root/focused/Tests, three canaries, SafeVerify `dc280a8f...b13a5`, and baseline
  axioms pass. Independent review found no P0/P1/P2 and its retrieval-timing P3
  is closed. Lifecycle records are accepted, verified memory is
  `mem-b8cfa9865d91f12a`, frontier shadow has zero mismatches, and the full
  harness passes.
- Failure policy/next leaf: the compiled realized-regret all-time route now
  combines this event with the accepted pure deviation event. Do not claim
  realized regret from this parent alone,
  tuned sublinear all-time rates, horizon retuning, Ville/Doob, mixture,
  optional stopping, self-normalization, general Freedman, or EXP3.P.

## Accepted: Pure Generated EXP3 Geometric All-Time Deviation

- Leaf: `EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`, with supporting
  leaf `EXP3-SELECTED-LOSS-VARIANCE-UNIT-BOUND`.
- Lean statement: exact selected-loss predictable variance is pointwise at
  most one and cumulative variance through `horizon` is at most `horizon`;
  therefore the pure realized-deviation crossing union over every positive
  prefix `n+1` has outer measure at most `ENNReal.ofReal delta` at the
  deterministic geometric-share radius using budget `n+1`.
- Local APIs/imports: finite action distributions, exact centered variance,
  generated probability source, predictable unit-loss bounds, finite sums,
  and the accepted geometric joint all-time event and terminal.
- Proof route: finite-law mean and square bounds -> generated pointwise and
  cumulative budget -> named pure event -> equality with the joint event at
  budget `n+1` -> measure-bound rewrite.
- Regularity: measurable Env, measurable-singleton Action, decidable nonempty
  arms, `0<=gamma<=1`, and one predictable loss process for generated support;
  the terminal adds a probability prior, Standard Borel nonempty Env/Action,
  arbitrary fixed eta, `0<gamma`, and positive delta. No event measurability,
  independence, stationarity, `delta<=1`, caller budget, or variance-good
  premise.
- Retrieval/status: local selected-variance, geometric, countable quadratic,
  and joint all-time leaves; Mathlib finite-sum/order/variance/MGF cards;
  textbook and EXP3 cards are placement only; tail weapon is inspiration only.
  Ten Lean declarations, root, focused modules, and six canaries compile;
  SafeVerify `5479f334...870` and baseline axiom audit pass. Independent review
  found no P0/P1 and its canary/contract findings are closed. Lifecycle and
  the full harness pass; verified memory is `mem-7ceab55257453017`, and
  frontier shadow has zero mismatches.
- Failure policy/next leaf: the same-process predictable-regret assembly now
  compiles above; next combine both events. Do not claim small-loss/self-
  normalized confidence, full regret, horizon retuning, Ville/Doob, mixture,
  optional stopping, general Freedman, horizon-free tuned EXP3, or EXP3.P.

## Accepted: Generated EXP3 Geometric All-Time Predictable-Variance Tail

- Leaf: `EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL`, with
  supporting leaf `CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`.
- Lean statement: on one fixed generated EXP3 trajectory law, the union over
  all positive prefixes `n+1` of scheduled realized-deviation crossings
  intersected with `predictableVariancePrefix <= varianceBudget n` has mass
  at most `ENNReal.ofReal delta`; the geometric `delta/2/2^n` shares sum
  exactly to that outer budget.
- Local APIs/imports: `ConcentrationConfidenceSchedule`,
  `ConcentrationQuadraticScheduled`, `Exp3RealizedPredictableVarianceTail`,
  Mathlib geometric `HasSum` plus NNReal/ENNReal transport, and the generated
  fixed-tilt pointwise tail.
- Proof route: exact geometric sum -> constant scale/cap one -> fixed-process
  tail at each `n+1` -> generic countable scheduled quadratic union -> exact
  outer-budget rewrite.
- Regularity: probability prior; Standard Borel nonempty Env/Action;
  measurable action singletons; decidable nonempty finite arms; fixed eta,
  `0<gamma<=1`, one predictable unit-loss process, positive variance budgets,
  and positive delta. No event measurability, independence, stationarity,
  `delta<=1`, or proved deterministic variance envelope.
- Retrieval/status: independent schedule owner; local countable/quadratic/
  fixed-tilt parents; OFUL exact-budget precedent; Mathlib measure/MGF/log/order
  cards; textbook/EXP3 cards are placement only. Seven declarations, root,
  focused modules, and three external canaries compile. SafeVerify
  `be643bca...73b2`, baseline axiom audit, and independent review pass. Status
  is `accepted`; verified memory is `mem-1d262929553ef1ca` and frontier shadow
  has zero mismatches.
- Failure policy/next leaf: the unit budget and pure-event consumer above now
  close the budget premise; next is same-process pathwise potential,
  exploration, and comparator assembly. Do not claim full all-time regret,
  horizon retuning, Ville/Doob, mixture, optional stopping, self-normalization,
  general Freedman, horizon-free tuned EXP3, or ideal EXP3.P.

## Accepted: Countable Scheduled Quadratic Fixed-MGF Tail

- Leaf: `CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`.
- Lean statement: the scheduled optimized radius feeds a countable family of
  joint deviation/variance events. Their union has mass at most
  `sum' n, ENNReal.ofReal (deltaAt n)`, and a supplied ENNReal sum budget gives
  a direct confidence bound.
- Local APIs/imports: `ConcentrationQuadraticFixedMGF`, the compiled one-event
  quadratic delta theorem, `MeasureTheory.measure_iUnion_le`, and
  `ENNReal.tsum_le_tsum`.
- Proof route: specialize the one-event theorem at every natural index, apply
  countable outer-measure subadditivity, compare the tsum termwise, and close
  the outer budget by transitivity.
- Regularity: measurable ambient space; pointwise-positive scale, variance
  budget, tilt cap, and share schedules; per-index fixed-tilt families. No
  event measurability, probability measure, independence, filtration,
  boundedness, stationarity, or `deltaAt n <= 1` is required.
- Retrieval/status: local quadratic-delta and finite-maximal routes plus
  Mathlib measure/MGF/log-sqrt/exp-order cards; textbook and EXP3 cards are
  placement only and the tail weapon is inspiration only. Three declarations,
  root import, external full-statement canary, statement/axiom/index/lifecycle,
  and full harness gates pass. Status is `accepted`.
- Failure policy/next leaf: the explicit geometric schedule and fixed-process
  EXP3 consumer now compile above. Do not claim Ville/Doob, a mixture boundary,
  horizon-free anytime control, optional stopping, self-normalization, general
  Freedman, or ideal EXP3.P from this wrapper.

## Accepted: Scalar Joint-Error Stopped-Return Confidence

- Leaf:
  `RL-STOPPED-SAMPLED-POLICY-RETURN-JOINT-ERROR-DETERMINISTIC-TAIL-HIGH-PROBABILITY-OPTIMALITY`.
- Lean statement: one measurable scalar maximum represents the six literal
  stopped-return errors. Every positive `epsilon, delta` has one natural
  cutoff such that all later indices have weak scalar bad mass
  `< ENNReal.ofReal delta`, strict scalar good real mass `> 1-delta`, and a
  scalar strict bound iff all six literal strict bounds.
- Local APIs/imports: accepted deterministic-tail parent and named events;
  six coordinate-measurability APIs; Mathlib distance/max measurability and
  max order semantics.
- Proof route: six-way max -> measurable scalar -> strict/weak max
  normalization -> named/scalar event equality -> parent mass transport and
  five-field terminal under its one all-later cutoff.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, exact actual-policy semantics, exact distinct stops,
  `4 < horizon`, and positive tolerances; no `delta <= 1`.
- Retrieval evidence: `mem-cd67b8453f91af1b`; scenario/paper cards are
  placement only and weapons are inspiration only.
- Status: seven declarations plus root and typed five-field canary compile;
  SafeVerify `f4fc8680...355a`, clean placeholders, and all-seven baseline
  axiom reports pass. Review's P2/P3 metadata findings are closed;
  lifecycle/frontier/full harness gates pass. Status is `accepted`; verified
  memory is `mem-6f587b6fba5f9bfd`.
- Failure policy: existential/noncomputable cutoff only; no rate,
  independence, optional stopping, expectation/random-index interchange,
  model uniformity, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI.

## Accepted: Stopped Return Deterministic-Tail High-Probability Optimality

- Leaf:
  `RL-STOPPED-SAMPLED-POLICY-RETURN-DETERMINISTIC-TAIL-HIGH-PROBABILITY-OPTIMALITY`.
- Lean statement: every positive `epsilon, delta` has one natural cutoff such
  that all later indices have measurable bad mass `< ENNReal.ofReal delta`,
  named good real mass `> 1-delta`, and good-event membership iff the same six
  literal stopped-return errors are `< epsilon`.
- Local APIs/imports: accepted simultaneous-confidence bad event and eventual
  bound; `eventually_atTop`; `probReal_compl_eq_one_sub`;
  `ENNReal.toReal_lt_toReal`; `ENNReal.toReal_ofReal`.
- Proof route: strict ENNReal-to-real conversion and complement arithmetic ->
  named good-set measurability/semantics -> eventual cutoff extraction ->
  four-field terminal at every later index.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, exact actual-policy semantics, exact distinct stops,
  `4 < horizon`, and positive tolerances; no `delta <= 1`.
- Retrieval evidence: `mem-89d817ed84c75c44`; scenario/paper cards are
  placement only and no theorem card or weapon is consumed.
- Status: seven declarations plus root and typed external canary compile;
  SafeVerify `09d8972f...a28f`, clean placeholders, and seven baseline-only
  axiom reports pass. Independent review's P2/P3 ledger findings are closed
  with no open P0-P3; lifecycle and full harness gates pass. Status is
  `accepted`; verified memory is `mem-5265bad6103b31c3`.
- Failure policy: the cutoff is existential/noncomputable and no rate,
  independence, optional stopping, expectation/random-index interchange,
  model uniformity, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI is claimed.

## Accepted: Stopped Return Simultaneous High-Probability Optimality

- Leaf: `RL-STOPPED-SAMPLED-POLICY-RETURN-SIMULTANEOUS-HIGH-PROBABILITY-OPTIMALITY`.
- Lean statement: one measurable common-index event is the union of six
  capped/uncapped stopped sampled-return, literal actual-policy-return, and
  same-prefix-gap distance violations. Its complement gives six strict
  epsilon bounds, its probability tends to zero, and it is eventually below
  every positive real confidence tolerance.
- Local APIs/imports: four local measurability wrappers, two inherited
  policy-return measurability lemmas, six accepted in-measure parents, and
  Mathlib distance-event, finite-union, order-limit, and `ENNReal.ofReal` APIs.
- Proof route: explicit six-way union and complement normalization -> six
  distance-event limits -> six-term sum -> repeated `measure_union_le` and
  squeeze -> qualitative eventual confidence.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, exact actual-policy semantics, exact distinct stops, and
  `4 < horizon`.
- Retrieval evidence: `mem-8642ef20df67310d`; scenario/paper cards are
  placement only and no theorem card or weapon is consumed.
- Status: eleven declarations plus root and typed external canary compile;
  SafeVerify `abeed7f0...2c443`, clean placeholders, and seven baseline-only
  axiom reports pass. Independent review's P2/P3 ledger findings are closed
  with no open P0-P3; lifecycle and full harness gates pass. Status is
  `accepted`.
- Failure policy: no independence is assumed and no rate/cutoff is produced.
  No optional stopping, expectation/random-index interchange, model
  uniformity, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI is claimed.

## Accepted: Stopped Return In-Measure And A.E. Optimality

- Leaf: `RL-STOPPED-SAMPLED-POLICY-RETURN-IN-MEASURE-AE-OPTIMALITY`.
- Lean statement: literal sampled return and literal actual-successor-policy
  trajectory-law expected return converge to optimal, while their same-prefix
  gap converges to zero, in measure and almost everywhere at both exact capped
  and genuine uncapped inverse-square-root stopping prefixes. The terminal has
  six in-measure and six a.e. contracts.
- Local APIs/imports: accepted stopped-return `L1` terminal and exponent-one
  norm limits; capped/uncapped realized and behavior a.e. parents; exact
  complement/deviation identities; Mathlib convergence-in-measure and
  continuous subtraction APIs.
- Proof route: capped a.e. transport plus deviation rearrangement; six
  `eLpNorm 1 -> 0` conversions to in-measure convergence; six independent
  a.e. algebra transports; twelve-field terminal package.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, actual successor-policy trajectory-law semantics, exact
  prefixes, and `4 < horizon`.
- Retrieval evidence: local-first `mem-1ae15dfd64b32dc6`; Mathlib
  `ConvergenceInMeasure`; scenario/paper cards are placement only and no
  theorem card or weapon is consumed.
- Status: fifteen declarations plus root and external typed twelve-contract
  canaries compile; SafeVerify `22635f14...ad041`, clean placeholders, and
  seven baseline-only representative axiom reports pass. Independent review's
  sole P3 stale-ledger finding is closed with no open P0-P3; lifecycle and full
  harness gates pass. Status is `accepted`.
- Failure policy: a.e. is not derived from in-measure convergence. No
  expectation/random-index interchange, optional stopping, rate, model
  uniformity, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI is claimed.

## Accepted: Stopped Sampled/Policy Return L1 Optimality

- Leaf: `RL-STOPPED-SAMPLED-POLICY-RETURN-L1-OPTIMALITY`.
- Lean statement: for exact capped and genuine uncapped inverse-square-root
  first-passage prefixes, the stopped sampled-return optimality error, literal
  actual-successor-policy expected-return optimality error, and their gap are
  `MemLp 1` coordinatewise and all six `eLpNorm · 1` sequences tend to zero.
- Local APIs/imports: accepted sampled/realized and policy/behavior
  complements, accepted sampled-policy/return-deviation identity, and all
  capped/uncapped realized/behavior/deviation `MemLp` and norm parents.
- Proof route: stable centered/gap definitions -> three exact pointwise
  identities -> negation/equality transport -> six `MemLp` and six norm limits
  -> terminal package.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, actual successor-policy trajectory-law semantics, exact
  prefixes, and `4 < horizon`.
- Retrieval evidence: `mem-de0a77c377532117`; `SCN-RL-MDP` and
  `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` are placement only; no weapon consumed.
- Status: twenty declarations plus root and external declaration/generic/
  explicit-twelve-contract canaries compile; SafeVerify
  `604b612b...a9562a`, empty placeholders, and baseline-only representative
  axioms pass. Independent review's sole P2 canary finding is closed with no
  open P0-P3; lifecycle and the full harness gate pass.
- Failure policy: no expectation/random-index interchange, optional stopping,
  pathwise/rate result, model uniformity, raw episodes, recommended-policy
  substitution, minimax/reachability, or complete UCB-VI.

## Accepted: Stopped Sampled/Successor-Policy Expected-Return Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-SAMPLED-RETURN-SUCCESSOR-POLICY-EXPECTED-RETURN-CONSISTENCY`.
- Lean statement: the literal trajectory-law return of each actual successor
  policy averages to optimal minus behavior expected regret. At both exact
  stopped prefixes, sampled return minus policy expected return equals return
  deviation pathwise and under the common measure; both signed and absolute
  expected gaps vanish and both expected policy returns converge to optimal.
  The terminal also retains the pointwise and integral
  policy-return/behavior-regret complements.
- Local APIs/imports: `MarkovPolicy.expectedRegret`; successor policy
  trajectory measure; cumulative reward; sampled complement; stopped
  realized/behavior/deviation decomposition; behavior `MemLp 1`; four parent
  integral limits; finite-sum and Bochner APIs.
- Proof route: literal integral semantics -> prefix complement -> exact stopped
  algebra -> stopped measurability/integrability -> integral identities ->
  return-deviation and behavior-regret limits -> terminal package.
- Regularity: exact generated source, actual `successorPolicyAt` indexing,
  equal-round and zero-prefix conventions, exact capped/uncapped stops, finite
  nonempty Standard Borel spaces, probability laws, positive proxy/floor,
  selected-reward MGF, support/floor, bounded means, and `4 < mdp.horizon`.
- Retrieval/status: exact no-hit; `mem-06aaf9949ace539d`; 29 declarations,
  root/Tests, SafeVerify `e35de2a4...7353`, clean placeholders, and
  baseline-only representative axiom audit. Independent review found no
  P0/P1; typed contract canaries and the expanded terminal close its P2/P3
  findings, so no P0-P3 remains.
- Failure policy/next route: fixed-model qualitative expected consistency
  only. Preserve the actual policy integral and same random prefix. Do not
  infer expectation/random-index interchange, optional stopping, pathwise
  return convergence, rates, raw episodes, recommended-policy substitution,
  minimax/reachability, or complete UCB-VI.

## Accepted: Stopped Average Sampled-Return Expected Optimality

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-AVERAGE-SAMPLED-RETURN-EXPECTED-OPTIMALITY`.
- Lean statement: the explicit natural-prefix average of observed
  successor-batch sample means, with optimal-value convention at prefix zero,
  equals optimal initial expected return minus average realized regret. At the
  capped and genuine uncapped stops, both coordinates are integrable, have
  exact expected complement identities, and their expectations tend to the
  optimal initial expected return.
- Local APIs/imports: sampled reward sums; natural average realized-regret
  adaptation; stopped-value measurability; stopped realized `MemLp 1`;
  capped/uncapped realized integral limits; finite-sum algebra;
  `integral_sub`; `Tendsto.const_sub`.
- Proof route: literal sampled finite sums -> total complement identity ->
  adapted/stopped regularity -> integrability and exact expectation transport
  -> capped/uncapped expected optimality -> terminal package.
- Regularity: exact generated source/schedule/filtration and both stops,
  finite nonempty Standard Borel spaces, probability laws, positive
  proxy/floor, selected-reward MGF, support/floor, bounded means, exact
  normalization, generic zero-batch totalization, positive scheduled batches,
  zero-prefix convention, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; `mem-31b7a2396410fc17`; 22 declarations,
  root/Tests, SafeVerify `cf81f234...e5f5`, clean placeholders, and
  baseline-only representative axiom audit. Independent review's two P3
  hardening findings are closed by the documented empty-batch contract and
  direct zero-prefix/capped/uncapped measurability canaries; no P0-P3 remains,
  lifecycle shadow and the full gate pass.
- Failure policy/next route: this is fixed-model expected return optimality,
  not expectation/random-index interchange, optional stopping, sample-path
  return convergence, a quantitative rate, model uniformity, raw episodes,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI.
  A downstream consumer may compare expected sampled return with the compiled
  successor-policy value benchmark while preserving the exact representatives.

## Accepted: Stopped Realized/Policy-Value Expected Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-REALIZED-POLICY-VALUE-EXPECTED-CONSISTENCY`.
- Lean statement: for capped and uncapped prefixes, expected realized regret
  minus expected successor-policy value gap exactly equals negative expected
  return deviation, and both signed/absolute vertical gaps tend to zero. The
  terminal retains the accepted horizontal behavior/realized gaps and an
  exact equality of both paths around the square.
- Local APIs/imports: accepted expected decompositions, return-deviation
  expectation limits, and behavior/realized horizontal gaps; `Tendsto.neg`;
  `continuous_abs`; `ring`.
- Proof route: exact decomposition normalization -> negative-return sequence
  rewrite -> signed convergence -> absolute convergence -> exact path
  equality -> terminal square.
- Regularity: exact generated source and both stops, finite nonempty Standard
  Borel spaces, probability laws, positive proxy/floor, selected-reward MGF,
  support/floor, bounded means, exact behavior/centering/normalization, and
  `4 < mdp.horizon`.
- Retrieval/status: no duplicate; `mem-4fafd4fc9904f47d`; seven declarations,
  root/Tests, SafeVerify `d07f9ed4...c7b9`, clean placeholders,
  baseline-only axiom audit, no-open-P0-P3 independent review, and full gate
  pass.
- Failure policy/next route: this is qualitative fixed-model expected
  consistency only. Do not infer expectation/random-index interchange,
  optional stopping, finite-index equality, a rate, model uniformity, raw
  episodes, behavior=recommended equality, minimax/reachability, or complete
  UCB-VI. A downstream consumer must preserve the exact policy-value process.

## Accepted: Componentwise Capped/Uncapped Expected Truncation

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-BEHAVIOR-RETURN-EXPECTED-TRUNCATION`.
- Lean statement: behavior-value and return-deviation uncapped-minus-capped
  signed expectation gaps and their absolute values tend to zero. Both exact
  expected decompositions hold, all six coordinates are integrable, and the
  four component expectations tend to zero.
- Local APIs/imports: accepted componentwise L1 truncation and realized
  expectation parents; exact stopped decomposition; `MemLp.integrable`;
  `integral_sub`; `continuous_abs`.
- Proof route: component integrability -> integral-difference rewrite ->
  signed/absolute expected-gap limits -> exact pathwise decomposition ->
  capped/uncapped integral identities -> terminal packaging.
- Regularity: exact generated source and both stops, finite nonempty Standard
  Borel spaces, probability laws, positive proxy/floor, selected-reward MGF,
  support/floor, bounded means, exact behavior/centering/normalization, and
  `4 < mdp.horizon`.
- Retrieval/status: no duplicate; `mem-bf148b8e7faff0cd`; seven declarations,
  root/Tests, SafeVerify `d46e2fb3...e0e53`, clean placeholders,
  baseline-only axiom audit, no-P0-P3 independent review, and full gate pass.
- Failure policy/next route: this closes qualitative fixed-model expectation
  replacement only. Do not infer expectation/random-index interchange,
  optional stopping, finite-index equality, a rate, model uniformity, raw
  episodes, or complete UCB-VI. A downstream policy-value consumer must keep
  the exact expected return-noise term.

## Accepted: Componentwise Capped/Uncapped Policy-Value L1 Truncation

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-BEHAVIOR-RETURN-L1-TRUNCATION`.
- Lean statement: capped behavior-expected regret and return deviation are
  measurable/`MemLp 1` as applicable with vanishing exponent-one norms and
  signed integrals. Capped and uncapped components are a.e.-eventually equal,
  their uncapped-minus-capped L1/integral errors vanish, both stopped
  decompositions hold, and `Delta return = Delta behavior - Delta realized`.
- Local APIs/imports: both eventual-base prefix theorems; capped stopping
  time; random-prefix composition; `2H` envelope; accepted uncapped semantic
  terminal; accepted realized truncation terminal; `MemLp.sub`;
  `memLp_congr_ae`; `eLpNorm_congr_ae`; `eLpNorm_sub_le`; integral
  continuity.
- Proof route: capped prefix divergence -> capped behavior dominated L1 ->
  exact decomposition -> capped return L1 -> behavior difference triangle ->
  exact difference algebra plus realized truncation -> return difference L1.
- Regularity: exact generated source and both stops, finite nonempty Standard
  Borel spaces, probability laws, positive proxy/floor, selected-reward MGF,
  support/floor, bounded means, exact behavior/centering/normalization, and
  `4 < mdp.horizon`.
- Retrieval/status: no duplicate; `mem-1011ebc0a0909b71`; eighteen
  declarations, root/Tests, SafeVerify `20132e52...62acb`, clean
  placeholders, baseline axiom audit, independent local review, and full gate
  pass.
- Failure policy/next route: no optional stopping, expectation/random-index
  interchange, finite-index equality, quantitative rate, model uniformity,
  raw episodes, or complete UCB-VI follows. A downstream expected policy-value
  consumer may now use the practical capped prefix without dropping the
  return-noise decomposition.

## Accepted: Uncapped Policy-Value And Return-Deviation L1

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPED-BEHAVIOR-EXPECTED-REGRET-AND-RETURN-DEVIATION-L1-CONSISTENCY`.
- Lean statement: the stopped successor-policy value-gap process is
  measurable, nonnegative, bounded by `2H`, `MemLp 1`, and converges a.e., in
  expected absolute value, exponent-one norm, and signed expectation. The
  stopped return deviation is `MemLp 1` with vanishing exponent-one norm and
  signed expectation, and realized equals behavior expected minus return at
  the exact same uncapped prefix.
- Local APIs/imports: deterministic behavior envelope; random-prefix
  measurability/composition; uncapped prefix divergence; dominated integral
  continuity; exponent-one `MemLp` identity; accepted realized L1;
  `memLp_congr_ae`; `MemLp.sub`; `eLpNorm_sub_le`; integral continuity.
- Proof route: pathwise successor-policy average -> exact random-prefix
  evaluation -> dominated behavior L1 -> same-prefix semantic decomposition
  -> return-deviation L1 triangle -> signed-integral limits.
- Regularity: exact generated source and uncapped stop, finite nonempty
  Standard Borel spaces, probability laws, positive proxy/floor,
  selected-reward MGF, support/floor, bounded means, exact behavior/centering/
  normalization contracts, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; `mem-cd29ac6abaf4cb55`; focused/root/Tests,
  SafeVerify `0af3bbb9...79da77`, baseline-only axiom audit, independent
  review with no P0-P3, and the full gate pass.
- Failure policy/next route: no optional stopping, expectation/random-index
  interchange, finite-index equality, quantitative rate, model-uniform
  control, raw episodes, behavior=recommended equality, or complete UCB-VI
  follows. A downstream route may now consume genuine successor-policy value
  gaps and return centering without retreating to realized regret alone.

## Accepted: Expected-Regret Truncation Replacement

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-UNBOUNDED-HITTINGAFTER-EXPECTED-REGRET-TRUNCATION-REPLACEMENT`.
- Lean statement: on the exact generated trajectory law, capped and uncapped
  coordinates are integrable; the integral of uncapped-minus-capped equals
  the difference of integrals; both forms and the absolute expected gap tend
  to zero; both signed expectations tend to zero.
- Local APIs/imports: accepted L1 truncation comparison; accepted uncapped
  integral limit; `memLp_one_iff_integrable`; `integrable_zero`;
  `eLpNorm_congr_ae`; `tendsto_integral_of_L1'`; `integral_sub`; and
  `continuous_abs`.
- Proof route: arbitrary-measure Bochner L1 continuity -> exact difference
  integral -> same-measure `integral_sub` -> signed and absolute expected gap
  -> capped direct integral limit + uncapped accepted limit.
- Regularity: exact generated law, exact capped/uncapped stop definitions,
  selected-reward/support/source/indexing/normalization/behavior contracts,
  and `4 < mdp.horizon`; the generic bridge needs no finite measure.
- Retrieval/status: no duplicate; local parents and exact Mathlib APIs under
  `mem-0c4479e50a03a4ce`; focused/root/Tests compile, SafeVerify
  `ef44a0df...b9741`, and the baseline-axiom audit passes. Independent review
  found no P0-P2; both P3 metadata findings are closed. Lifecycle shadow and
  the full gate pass, including 36 CLI tests with one expected skip.
- Failure policy/next route: no finite-index equality, delayed-event equality,
  quantitative rate, optional stopping, policy-value identity, model
  uniformity, raw episodes, or complete UCB-VI follows. A downstream theorem
  must separately connect these signed expectations to a policy-value or
  raw-regret semantic interface.

## Accepted: Capped/Uncapped HittingAfter L1 Truncation Equivalence

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-UNBOUNDED-HITTINGAFTER-L1-TRUNCATION-EQUIVALENCE`.
- Lean statement: outside the capped delayed set both stopping prefixes equal
  the common base and the stopped processes agree; almost every trajectory
  eventually has exact equality. The uncapped-minus-capped difference is
  `MemLp 1` and converges to zero in `eLpNorm 1`, named `Lp Real 1`, and
  measure.
- Local APIs/imports: delayed-set/base characterization, capped lower bound,
  uncapped immediate-base theorem, capped L1 terminal, uncapped Lp terminal,
  `MemLp.sub`, `eLpNorm_sub_le`, Lp convergence, and in-measure transport.
- Proof route: nonmembership -> both stops equal base -> pointwise support;
  summable delayed-set avoidance -> a.e. eventual equality; triangle bound on
  the two accepted L1 sequences -> difference L1/Lp/in-measure convergence.
- Regularity: exact generated source, both exact stop definitions, capped
  delayed set, selected-reward/support contracts, and `4 < mdp.horizon`.
- Retrieval/status: no duplicate; local compiled parents and Mathlib Lp APIs;
  focused module, root import, and external terminal canaries compile.
  SafeVerify `b68c4bc4...76a80`, placeholder and baseline-axiom audits,
  independent review, lifecycle shadow, and the full repository gate pass;
  the review's two P3 metadata findings are closed.
- Failure policy/next route: do not identify capped and uncapped delayed
  events, claim equality on the capped delayed set, or infer a quantitative
  rate or optional stopping. A downstream policy-value replacement theorem
  must be opened as a separate leaf with its own comparison contract.

## Accepted: Delayed-Event Expected Contribution At Exact HittingAfter

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-DELAYED-EVENT-EXPECTED-CONTRIBUTION`.
- Lean statement: for the existing measurable capped first-passage delayed
  events, their probabilities tend to zero and the genuine uncapped stopped
  process has both absolute and signed restricted expected contributions
  tending to zero.
- Local APIs/imports: accepted `integral_abs_restrict_le_of_uniformIntegrable_one`;
  ENNReal `Tendsto`/`Iio_mem_nhds`; `integral_nonneg`;
  `abs_integral_le_integral_abs`; delayed-set measurability; compiled
  `delayedProbability_tendsto_zero`; exact uncapped `UniformIntegrable`.
- Proof route: varying event mass -> eventually below the common UI delta ->
  half-epsilon restricted L1 bound -> signed-integral domination.
- Regularity: exact generated probability/source/indexing/normalization and
  selected-reward/support contracts, genuine uncapped stop, exact capped
  delayed set, and `4 < mdp.horizon`; the generic bridge is measure-agnostic.
- Retrieval/status: no duplicate; Mathlib source plus two accepted local
  parents; focused/root/Tests compile, SafeVerify `304b5afc...499c0`, clean
  placeholders, and baseline axioms. Independent review found no P0-P3 and
  the signed generic application canary now compiles; lifecycle shadow and
  the full repository gate pass.
- Failure policy/next route: no explicit rate or capped/uncapped equality is
  proved. A child may use this as the rare-event term in a truncation or policy
  decomposition only after proving the complementary pointwise comparison;
  no optional stopping, model uniformity, raw episodes, or complete UCB-VI.

## Accepted: Exact Uncapped HittingAfter Uniform Absolute Continuity

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-UNIFORM-ABSOLUTE-CONTINUITY`.
- Lean statement: one positive delta per positive epsilon uniformly controls,
  over all schedule indices and measurable small-probability events, both the
  restricted expected absolute stopped regret and the absolute signed
  restricted expectation.
- Local APIs/imports: accepted exact UI parent;
  `UniformIntegrable.unifIntegrable`; `UniformIntegrable.memLp`;
  `MemLp.indicator`; `MemLp.eLpNorm_eq_integral_rpow_norm`;
  `integral_indicator`; and `abs_integral_le_integral_abs`.
- Proof route: consume the UI epsilon-delta indicator norm; identify its
  exponent-one norm with the real restricted absolute integral; then apply
  the standard signed-integral domination.
- Regularity: unchanged exact generated probability/source/uncapped-stop and
  finite-MDP reward-law/support/indexing/normalization contracts,
  `4 < mdp.horizon`, plus event measurability.
- Retrieval/status: no memory/local duplicate; Mathlib source and accepted UI
  parent; focused/root/Tests builds, SafeVerify `db0cd463...71c67`, clean
  placeholders, and baseline axioms pass. Independent review's single P3
  fence-guard finding is repaired with no remaining P0-P3; lifecycle shadow
  and the full repository gate pass.
- Failure policy/next route: no quantitative delta or event-probability rate
  follows. A child must supply its own concrete vanishing event bound; do not
  infer optional stopping, stopping moments, model uniformity, raw episodes,
  or complete UCB-VI.

## Accepted: Exact Uncapped HittingAfter Uniform Integrability And Signed Expectation

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-UNIFORM-INTEGRABILITY-EXPECTED-CONSISTENCY`.
- Lean statement: the genuine uncapped stopped sequence is Mathlib
  `UniformIntegrable` at exponent one, and its signed Bochner expectations
  tend to zero.
- Local APIs/imports: accepted exact hittingAfter Lp parent;
  `unifIntegrable_of_tendsto_Lp`;
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`;
  `Metric.isBounded_range_of_tendsto`; `Lp.enorm_toLp`; and
  `tendsto_integral_of_L1'`.
- Proof route: L1 convergence yields `UnifIntegrable`; convergence of the
  named `Lp` sequence bounds its whole range, and `Lp.enorm_toLp` transports
  that bound to the raw stopped functions, completing probability UI. Apply
  Bochner-integral continuity separately for signed expectation convergence.
- Regularity: unchanged finite nonempty Standard Borel spaces, probability
  laws, positive proxy/floor, bounded means, selected-reward sub-Gaussianity,
  support/floor, exact source/filtration/indexing/centering/normalization/
  behavior, genuine uncapped stop, and `4 < mdp.horizon`.
- Retrieval/status: local-first parent plus exact Mathlib UI/Bochner source;
  theorem cards are not proofs; four declarations, root and external canaries,
  SafeVerify `2c010bef...fcd24`, clean placeholders, baseline axioms, and
  independent no-P0-P3 review pass.
- Failure policy: no optional-stopping identity, stopping-time moment/rate,
  uniform-in-model/index theorem, raw episodes, behavior=recommended equality,
  minimax/reachability, or complete UCB-VI.

## Accepted: Exact Uncapped HittingAfter Lp Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-LP-CONSISTENCY`.
- Lean statement: the genuine uncapped stopped process is strongly adapted,
  measurable, integrable, and in `MemLp 1` coordinatewise; its expected
  absolute value, exponent-one `eLpNorm`, and named `Lp Real 1` value tend to
  zero, together with in-measure and a.e. convergence.
- Local APIs/imports: accepted exact hittingAfter L1/integrability/a.e.
  parents; `memLp_one_iff_integrable`;
  `MemLp.eLpNorm_eq_integral_rpow_norm`; `MemLp.toLp`; `coeFn_toLp`;
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; Lp-to-in-measure transport.
- Proof route: rewrite fixed-index integrability to `MemLp 1`; identify
  exponent-one norm with `ofReal` of the canonical expected absolute value;
  map the accepted real Tendsto through continuous `ofReal`; lift every
  coordinate to `Lp`; use the Lp metric characterization; collect the existing
  exact a.e. endpoint and derive in-measure from the L1 norm limit.
- Regularity: unchanged finite nonempty Standard Borel state/action,
  probability laws, positive proxy/floor, bounded means, selected-reward
  sub-Gaussianity, support/floor, exact source/filtration/indexing/centering/
  normalization/behavior, genuine uncapped stop, and `4 < mdp.horizon`.
- Retrieval/status: local-first exact parents plus Mathlib Lp APIs; theorem
  cards are not proofs; focused/root/Tests builds and SafeVerify
  `30ec3b42...aaca8a8` pass; independent review found no P0-P3 and its typed
  terminal-consumer request is closed; lifecycle shadow and the full gate pass.
- Failure policy: no optional stopping, uniform integrability, stopping-time
  moment/rate, uniform-in-model/index theorem, raw episodes,
  behavior=recommended equality, minimax/reachability, or complete UCB-VI.

## Accepted: Exact Uncapped HittingAfter L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-L1-CONSISTENCY`.
- Lean statement: the canonical expected absolute exact natural-causal average
  realized behavior regret stopped at the genuine uncapped inverse-square-root
  `hittingAfter` tends to zero.
- Local APIs/imports: the accepted expected-positive-part and explicit-prefix
  L1 leaves; successor conditional/global MGF and MGF second-moment APIs; exact
  average recursion; Mathlib `hittingAfter`; the new
  `UnboundedStoppingTimeWeightedL2CoordinateIntegrability` foundation.
- Proof route: obtain a uniform successor-regret L2 envelope; a delayed first
  hit has a positive predecessor average, so the exact recursion bounds the
  negative overshoot by `|X_(hit-1)| / hit`; reciprocal-square stopping-fiber
  Cauchy-Schwarz makes this term vanish; the summable base-prefix L1 term pays
  for immediate hits; finally add the accepted positive-part limit.
- Regularity: finite nonempty Standard Borel state/action spaces, probability
  initial/generated laws, positive variance proxy and visit floor, bounded mean
  rewards, selected-reward uniform sub-Gaussianity, exploratory support/floor,
  exact source/filtration/indexing/centering/per-batch normalization/behavior,
  and `4 < mdp.horizon`.
- Retrieval/status: local-first compiled parents plus Mathlib
  Holder/inverse-square/dominated-tsum/integral APIs; theorem cards are not
  proofs; focused foundation/RL/root/Tests builds, SafeVerify hash
  `42966e22...7b0`, independent review, lifecycle shadow, and full gate pass.
- Failure policy: fixed-model L1 consistency only; no optional stopping,
  uniform-integrability theorem, stopping-time moment/rate bound,
  uniform-in-model/index control, raw-episode regret, behavior=recommended
  equality, minimax/reachability, or complete UCB-VI.

## Compiled: Expected Positive-Part Consistency At Exact HittingAfter

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-EXPECTED-POSITIVE-PART-CONSISTENCY`.
- Statement: under the exact generated-source contracts, the expectation of
  `max stoppedAverageRealizedBehaviorRegret 0` tends to zero along the
  inverse-square-root threshold schedule.
- Route/APIs: accepted stopped-process integrability; `Integrable.abs.mono'`;
  `Measurable.max`; exact a.e.-finite at-hit threshold inequality;
  `integral_mono_ae`; threshold positivity and convergence; `squeeze_zero`.
- Contracts: finite nonempty Standard Borel spaces, generated probability law,
  positive proxy/floor, bounded means, selected-reward uniform
  sub-Gaussianity, support/floor conditions, exact source/filtration/indexing/
  centering/normalization/behavior, and `4 < mdp.horizon`.
- Retrieval/status: no matching local theorem or typed memory result; exact
  local/Mathlib route compiled as `mem-f0db6d1dd3a432a9`; `leanCompiled` with
  four declarations, three external canaries, SafeVerify
  `151c8c10...e9815`, baseline axioms, and independent local review no P0-P3.
- Failure policy/next route: this proves only one-sided excess consistency.
  Signed expectation, expected-absolute/L1 convergence, uniform integrability,
  optional stopping, raw episodes, and complete UCB-VI remain separate leaves.
  A next consumer may use this endpoint directly or add an independently
  justified lower-side statement without changing the exact stopping time.

## Compiled: Cauchy-Schwarz Degree-Four Expected-Absolute Asymptotics

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-CAUCHY-SCHWARZ-ABSOLUTE-FIRST-MOMENT-ISBIG-O-DEGREE-FOUR`.
- Statement: for fixed finite-MDP/generated-source parameters, the actual
  expected absolute stopped average realized behavior regret is
  `O((scheduleIndex+1)^4)`.
- Route/APIs: finite-sum `Real.sum_mul_le_sqrt_mul_sqrt`; nonnegative
  finite-sum-to-`tsum` transport; exact weighted fiber-moment identity;
  coordinate-L2 stopped-value theorem; polynomial moment parent;
  `Asymptotics.IsBigO.sqrt`; exact `sqrt(s^8)=s^4`.
- Contracts: the generic layer requires finite measure, measurable/a.e.-finite
  fixed stopping time, rounds `MemLp 2`, coordinate `MemLp 2`, and a uniform
  coordinate second moment. The terminal retains exact generated probability/
  Standard-Borel/MGF/support/indexing/centering/normalization/behavior,
  positive proxy/floor, bounded means, and `4 < mdp.horizon`.
- Retrieval/status: no direct card; local/Mathlib route compiled in scratch as
  `mem-e0a6fb8355363a3e`; `leanCompiled` with twelve declarations, five
  external canaries, SafeVerify `11fca241...145b4`, baseline axioms, and
  independent review no P0-P3.
- Failure policy/next route: degree four is an improved fixed-model growth
  envelope, not sharpness, decay, uniform-in-model/index control, UI/L1,
  optional stopping, raw episodes, or complete UCB-VI. Improve the underlying
  stopping-round tail/moment input or connect a concrete consumer in a
  separate leaf.

## Compiled: Degree-Eight Stopping-Round Moment Asymptotics

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-POLYNOMIAL-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-ISBIG-O`.
- Statement: for fixed finite-MDP/generated-source parameters, the actual
  successor stopping-round second moment and expected absolute stopped
  average realized behavior regret are both `O((scheduleIndex+1)^8)`.
- Route/APIs: degree-eight natural algebra; nonnegative fixed-constant
  absorption with `1 <= scale`; `Asymptotics.isBigO_iff`;
  `Real.norm_eq_abs`; `integral_nonneg`; `tsum_nonneg`; accepted
  pointwise moment and stopped-process bounds.
- Contracts: exact generated probability/Standard-Borel/MGF/support/indexing/
  centering/normalization/behavior contracts, positive proxy/floor, bounded
  means, and `4 < mdp.horizon`; model/source parameters fixed.
- Retrieval/status: no matching card; local parent, OFUL/UCB asymptotic
  patterns, and exact Mathlib APIs retrieved as `mem-208816c27b4594b9`;
  `leanCompiled` with twenty-five declarations, five external canaries,
  SafeVerify `ee350657...66dc1c`, baseline axioms, and review no P0-P3.
- Failure policy/next route: degree eight remains the actual stopping-round
  second-moment growth; the expected-absolute exponent is superseded by the
  Cauchy--Schwarz child above. This is not convergence, uniform
  moments/UI/L1, optional stopping, sharpness, or
  uniformity across models. A separate leaf may bound the named weighted MDP
  constant or sharpen the tail/moment exponent when a consumer requires it.

## Compiled: Polynomial Stopping-Round Second-Moment Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-POLYNOMIAL-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Statement: for each fixed inverse-sqrt index, the explicit tail start plus
  one is linearly bounded by `(ceil rateCoefficient + 2) * (n+1)`. The actual
  successor stopping-round second moment and stopped-regret absolute integral
  are therefore bounded by an explicit degree-eight checkpoint polynomial
  plus a named finite MDP-only weighted failure constant.
- Route/APIs: `Real.sqrt_le_iff`; `Nat.le_ceil`; `Nat.ceil_le`; max and product
  monotonicity; `Nat.pow_le_pow_left`; weighted `tsum` finiteness;
  `ENNReal.toReal_add`; `ENNReal.toReal_mono`; accepted explicit endpoint.
- Contracts: finite scalar MDP layer and fixed index; `4 < mdp.horizon` for
  Real conversion; exact generated probability/Standard-Borel/MGF/support/
  indexing/centering/normalization/behavior contracts, positive proxy/floor,
  and bounded means at the terminal.
- Retrieval/status: no prior polynomial-start memory hit; exact local parent
  and Mathlib order/sqrt/integral APIs found; `leanCompiled` with sixteen
  declarations and five external canaries.
- Failure policy/next route: the named weighted constant remains a convergent
  `tsum`, not a numerical closed form. The fixed-model degree-eight
  `IsBigO` child above now compiles; do not infer uniform moments, UI/L1
  convergence, optional stopping, raw episodes, or complete UCB-VI.

## Compiled: Explicit Tail-Start Deterministic Second-Moment Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-EXPLICIT-TAIL-START-DETERMINISTIC-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Statement: for each fixed inverse-sqrt index, a max/ceiling expression is a
  valid all-later tail start and bounds the canonical `Nat.find` witness. Under
  `4 < mdp.horizon`, it yields explicit deterministic second-moment and
  stopped-regret absolute-first-moment budgets without visit-floor parameter,
  stopping fibers, or random integral on the RHS.
- Route/APIs: exact reciprocal-linear rate envelope; `Nat.le_ceil`; positive
  sqrt/division algebra; `Nat.find_min'`; checkpoint and weighted-budget
  monotonicity; ENNReal finiteness; `ENNReal.toReal_mono`; accepted
  deterministic stopped-value endpoint.
- Contracts: finite MDP scalar layer and fixed index; exact generated RL
  probability/Standard-Borel/MGF/support/indexing/centering/normalization/
  behavior contracts, positive proxy/floor, bounded means, and
  `4 < mdp.horizon` at the terminal.
- Retrieval/status: no prior explicit-ceiling memory hit; local rate and
  canonical-start parents plus Mathlib order/sqrt/integral APIs found;
  `leanCompiled` with fifteen declarations and four external canaries.
- Failure policy/next route: the polynomial child above isolates the finite
  weighted failure `tsum` and supplies the schedule-index envelope. Do not
  infer uniform moments, UI/L1 convergence, optional stopping, raw episodes,
  or complete UCB-VI.

## Compiled: Deterministic Stopping-Round Second-Moment Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-DETERMINISTIC-STOPPING-ROUND-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Statement: for each fixed inverse-sqrt index and `4 < mdp.horizon`, the
  actual successor stopping-round second moment is bounded by a canonical
  squared checkpoint plus the seventh-degree weighted exact model/return
  failure-budget series; the stopped process has a deterministic absolute
  first-moment budget with no fibers or random integral.
- Route/APIs: rate convergence and threshold positivity; `Nat.find` tail
  start; delayed-event violation transport; squared checkpoint layer cake;
  `lintegral_tsum`; weighted-budget finiteness; `ENNReal.toReal_mono`;
  compiled actual-moment stopped-value consumer.
- Contracts: probability/measurability at the generic layer; exact generated
  RL source and inherited probability/Standard-Borel/MGF/support/indexing/
  centering/normalization/behavior contracts; positive proxy/floor, bounded
  means, `4 < horizon`, and fixed index.
- Retrieval/status: no prior memory hit; exact local and Mathlib evidence;
  `leanCompiled` with canonical start, generic/source moment bridges, named
  deterministic budgets, endpoint, and external canary.
- Failure policy/next route: the explicit child above bounds the canonical
  start. Keep this parent for compatibility and do not infer a uniform moment,
  UI/L1 convergence, optional stopping, raw episodes, or complete UCB-VI.

## Compiled: Stopping-Round Second-Moment Absolute First-Moment Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPING-ROUND-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Statement: for each fixed inverse-sqrt index and `4 < mdp.horizon`, the
  exact stopped process is integrable and its expected absolute value is
  controlled by the uniform coordinate L2 envelope times one half of the
  actual stopping-round second moment plus the shifted inverse-square series.
- Route/APIs: exact ENNReal fiber decomposition; `ENNReal.tsum_toReal_eq`;
  `integral_eq_lintegral_of_nonneg_ae`; Young; shifted p-series;
  `Summable.tsum_add`; compiled fiber/Holder absolute theorem; exact RL L2
  stopping-time and coordinate moments.
- Contracts: finite-measure measurable/a.e.-finite stopping time, `MemLp 2`
  successor rounds and coordinates, one uniform coordinate second-moment
  ceiling; exact generated RL source and inherited probability/Standard
  Borel/MGF/support/indexing/centering/normalization/behavior contracts plus
  `4 < horizon`; fixed index.
- Retrieval/status: exact local and Mathlib evidence; `leanCompiled` with four
  generic theorem surfaces, named budget, terminal wrapper, and external
  canary.
- Failure policy/next route: the deterministic child above now bounds the
  actual second moment. A closed rate still requires an explicit bound on its
  canonical tail start; do not infer uniformity or asymptotics from per-index
  `MemLp 2`, and do not invoke optional stopping, raw episodes, or complete
  UCB-VI.

## Compiled: Stopping-Fiber Absolute First-Moment Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPING-FIBER-ABSOLUTE-FIRST-MOMENT-BOUND`.
- Statement: for each fixed inverse-sqrt index and `4 < mdp.horizon`, the
  exact stopped process is integrable and its expected absolute value is at
  most the named uniform-coordinate-L2 times stopping-fiber square-root-mass
  budget.
- Route/APIs: exact equality fibers; local indicator Holder;
  `summable_sqrt_stoppingFiberRealMeasure_of_memLp_two`;
  `integral_tsum_of_summable_integral_norm`; `Summable.tsum_le_tsum`;
  compiled RL coordinate moments and square-integrable hit.
- Contracts: finite-measure measurable/a.e.-finite stopping time, `MemLp 2`
  successor rounds and coordinates, one uniform coordinate second-moment
  ceiling; exact generated RL source and inherited probability/Standard
  Borel/MGF/support/indexing/centering/normalization/behavior contracts.
- Retrieval/status: exact local and Mathlib evidence; `leanCompiled` with a
  generic theorem, named budget, terminal wrapper, and external canary.
- Failure policy/next route: keep the fiber sum explicit. A useful next leaf
  must prove a schedule-index-uniform or asymptotic fiber-budget estimate;
  do not infer one from summability at each fixed index, and do not invoke
  optional stopping, raw episodes, or complete UCB-VI.

## Compiled: Unbounded HittingAfter Integrable Expected Upper Bound

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-INTEGRABLE-EXPECTED-UPPER-BOUND`.
- Statement: for each fixed threshold index and `4 < mdp.horizon`, the exact
  stopped average realized behavior regret is integrable and its expectation
  is at most the inverse-sqrt threshold.
- Route/APIs: measurable equality fibers; L2 weighted fiber mass; Young and
  inverse-square summability; indicator Holder; uniform RL coordinate moment;
  compiled square-integrable hit and finite-hit semantics; integral monotonicity.
- Contracts: exact generated source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior regularity;
  no independence or optional stopping.
- Retrieval/status: exact local/Mathlib retrieval; `leanCompiled` with seven
  declarations, root import, external canary, clean placeholders, and
  baseline-only axiom reports.
- Failure policy: retain fixed-index scope. Expected nonnegativity, absolute-
  moment rates, uniform integrability/L1 convergence, raw episodes,
  behavior=recommended, minimax/reachability, and complete UCB-VI are separate.

## Compiled: Unbounded HittingAfter Square-Integrable Finite Stopping Time

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-SQUARE-INTEGRABLE-FINITE-STOPPING-TIME`.
- Statement: for each fixed threshold index and `4 < mdp.horizon`, the genuine
  uncapped inverse-sqrt `hittingAfter` is finite a.e. and
  `((tau.untopA+1:Nat):Real)` belongs to `MemLp 2` under the exact generated
  trajectory law.
- Route/APIs: seventh-degree squared fourth-power checkpoint widths;
  inverse-tenth local confidence shares; shifted burn-in model-tail
  reindexing and inverse-cube pair envelope; exact exponential return share;
  measurable indicators, `lintegral_tsum`, `memLp_two_iff_integrable_sq`, and
  `OFUL.SquareIntegrableFiniteStoppingTime`.
- Contracts: exact dependent source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior
  regularity, plus explicit horizon at least five; no event independence or
  optional stopping.
- Retrieval/status: exact local/Mathlib retrieval; `leanCompiled` with 17
  declarations, root import, external root canary, clean placeholders, and
  baseline-only critical theorem axioms. Independent checks found no route
  mismatch.
- Failure policy/next route: for horizon at most four, use the compiled first
  moment. A downstream overflow/UI consumer must preserve fixed-index scope
  and prove its own expectation transport; do not infer a uniform moment
  rate, exponential tail, optional stopping, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Unbounded HittingAfter Integrable Finite Stopping Time

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-INTEGRABLE-FINITE-STOPPING-TIME`.
- Statement: for each fixed threshold index, the genuine uncapped inverse-sqrt
  `hittingAfter` is finite a.e. and `((tau.untopA+1:Nat):Real)` is integrable
  under the exact generated trajectory law.
- Route/APIs: cubic fourth-power checkpoint widths; shifted burn-in model-tail
  reindexing with `notMemRangeEquiv` and antidiagonals; inverse-power and
  polynomial-exponential summability; delayed-checkpoint-to-violation
  inclusion; measurable indicators and `lintegral_tsum`; prior a.e.
  finiteness; `OFUL.IntegrableFiniteStoppingTime`.
- Contracts: exact dependent source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior
  regularity; positive horizon supplies exponent at least six; no event
  independence or optional stopping.
- Retrieval/status: exact local/Mathlib retrieval; `leanCompiled` with 21
  declarations, root import, direct final-contract canary, clean placeholders,
  and baseline-only critical theorem axioms. Independent checks found no
  P0-P3 issue.
- Failure policy/next route: require a second moment or explicit UI envelope
  before uncapped L1/expectation transport. Do not infer uniform-in-index
  moments, exponential tails, optional stopping, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Unbounded HittingAfter A.E. Finiteness And In-Measure Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-AE-FINITE-EVENTUAL-IMMEDIATE-STOPPING-AND-IN-MEASURE-CONSISTENCY`.
- Statement: genuine Mathlib `hittingAfter` searches below `1/sqrt(n+1)`
  after `(n+1)^4`; every fixed hit and all countably many scheduled hits are
  finite a.e.; hits eventually equal their bases; stopped values converge
  a.e. and in measure.
- Route/APIs: exact `hittingAfter` lower/base/hit/stopping wrappers;
  all-prefix a.e. convergence plus positive threshold;
  `hittingAfter_eq_top_iff`; `ae_all_iff`; inverse-sqrt summable-delay parent;
  explicit-base divergence; generic stopped a.e. theorem;
  `tendstoInMeasure_of_tendsto_ae`.
- Contracts: exact dependent source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior
  regularity; no independence or optional stopping.
- Retrieval/status: exact no-hit followed by exact Mathlib/local parent
  retrieval; `leanCompiled` with 12 declarations, root import, external
  semantic/finiteness/eventual-base/root canaries, clean placeholders, and
  baseline-only public theorem axioms. Independent review's P3 semantic-canary
  gap was repaired, and no P0-P3 remain.
- Failure policy/next route: the separate fixed-index first-moment route now
  controls expected horizon; require second moments/UI before claiming L1 for
  the uncapped stopped process. Do not infer
  pointwise finiteness, raw episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI.

## Compiled: Inverse-Sqrt First-Passage Summable Delay And Eventual Immediate Stopping

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-SUMMABLE-DELAY-AND-EVENTUAL-IMMEDIATE-STOPPING-L1-CONSISTENCY`.
- Statement: with threshold `1/sqrt(n+1)`, capped first-passage delay
  probabilities have finite total mass; almost every trajectory eventually
  stops exactly at base `(n+1)^4`; the complete stopped L1, `eLpNorm`,
  in-measure, and a.e. terminal remains available.
- Route/APIs: exact finite first-passage delay characterization; scheduled
  expected-absolute Markov theorem; sqrt/rpow normalization; shifted
  p-series summability; ENNReal tsum comparison; first Borel-Cantelli;
  first-passage lower bound and order antisymmetry.
- Contracts: exact dependent source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior
  regularity; no event independence or optional stopping.
- Retrieval/status: exact no-hit, followed by exact local parent and Mathlib
  p-series/rpow/Borel-Cantelli retrieval; `leanCompiled` with twenty
  declarations, root import, and direct summability/finite-mass/
  eventual-base/root canaries. Placeholder and public-axiom audits are
  clean/baseline-only; independent review's initial P3 canary gap was closed,
  and no P0-P3 findings remain.
- Failure policy/next route: the scheduled a.s. statement supplies no
  deterministic eventual index, pointwise all-trajectory result, uncapped
  first-passage finiteness, expected delay, or exponential crossing tail.
  Those require stronger tail or uniform-integrability infrastructure. Do
  not infer raw episodes, behavior=recommended, minimax/reachability, or
  complete UCB-VI.

## Compiled: Reciprocal-Threshold First-Passage Vanishing Delay Probability And L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-RECIPROCAL-THRESHOLD-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-VANISHING-DELAY-PROBABILITY-AND-L1-CONSISTENCY`.
- Statement: with threshold `1/(n+1)`, probability that capped first passage
  advances beyond `(n+1)^4` tends to zero; the complete stopped L1,
  `eLpNorm`, in-measure, and a.e. terminal remains available.
- Route/APIs: exact finite first-passage delay characterization; measurable
  scheduled process; absolute-distance inclusion; scheduled expected-absolute
  Markov theorem; exponent-three/exponent-two L1 envelope; scale atTop and
  ENNReal squeeze.
- Contracts: exact dependent source and inherited Standard Borel/probability/
  MGF/support/bounded-mean/indexing/centering/normalization/behavior
  regularity; no independence or optional stopping.
- Retrieval/status: exact no-hit, followed by exact local first-passage,
  Markov, envelope, and asymptotic declaration retrieval; `leanCompiled`
  with sixteen declarations, root import, external threshold/delay/subset/
  rate/probability/root-`MemLp` canaries, baseline-only theorem axioms, and
  independent read-only review with no P0-P3 finding.
- Failure policy/next route: the inverse-linear return term is not summable.
  Eventual immediate stopping a.s. needs a stronger threshold schedule or
  sharper tail; uncapped `hittingAfter` additionally needs finiteness and
  uniform-integrability/tail contracts. Do not infer raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Capped Double-Linear Raw-Window First-Passage Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: Mathlib `hittingBtwn` scans the exact natural average realized
  behavior-regret process on `[(n+1)^4,(n+1)^4+(2*n+1)]`, returns its first
  value at or below deterministic `threshold n`, and otherwise returns the
  cap; the stopped process converges in expected absolute value,
  `eLpNorm 1`, measure, and a.e.
- Route/APIs: compiled strong adaptation; Mathlib finite hitting-time
  definition, first-hit/no-prior/interval/stopping lemmas; local hitting-time
  precedent; double-linear candidate rate; generic raw-window L1 terminal.
- Contracts: exact dependent source and inherited regularity; deterministic
  threshold; fixed fourth-power base and double-linear finite window; no
  independence or optional stopping.
- Retrieval/status: the exact search found only the previous non-first-passage
  card, followed by exact Mathlib and local declaration retrieval;
  `leanCompiled` with eleven declarations, root import, and external semantic,
  stopping-time, and full-terminal canaries. Independent review found no
  P0-P3 findings, and representative axioms are baseline only.
- Failure policy/next route: a strict pre-cap stop is a hit, while the cap may
  be a hit or fallback. The next route needs either uncapped hitting-time L1
  infrastructure or threshold calibration/crossing control. Do not infer a
  cap hit, crossing probability, raw episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI.

## Compiled: Threshold-Triggered Double-Linear Raw-Window Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-THRESHOLD-TRIGGERED-DOUBLE-LINEAR-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the exact base observation at `(n+1)^4` selects that prefix
  when it is at most a deterministic threshold and otherwise selects
  `(n+1)^4+(2*n+1)`; the resulting exact-filtration stopping process
  converges in expected absolute value, `eLpNorm 1`, measure, and a.e.
- Route/APIs: strong adaptation and `measurableSet_le`; Mathlib
  `isStoppingTime_piecewise_const`; branch/window wrappers; the compiled
  double-linear candidate rate and generic rate-controlled L1 terminal.
- Contracts: exact dependent source and inherited regularity; deterministic
  threshold; fixed fourth-power base and double-linear right endpoint; no
  independence or optional stopping.
- Retrieval/status: exact no-hit, exact local declaration retrieval, and
  Mathlib stopping source; `leanCompiled` with nine declarations, root
  import, external branch/stopping/full-terminal canaries, baseline-only
  axioms, and an independent review with no P0-P3 findings.
- Failure policy/next route: this is not a first-passage time over
  intermediate prefixes. A richer threshold-hitting rule requires a new
  event-family/stopping-time proof. Do not infer arbitrary widths/candidate
  sets, raw episodes, behavior=recommended, minimax/reachability, or complete
  UCB-VI; conditional branch canaries are not positive-probability witnesses.

## Compiled: Rate-Controlled Raw-Window Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-RATE-CONTROLLED-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: exact-natural-filtration stopping times in
  `[baseRounds n,baseRounds n+windowWidth n]` preserve expected absolute,
  `L1/eLpNorm`, in-measure, and a.e. convergence when bases are positive,
  `n<=baseRounds n`, and the candidate-count/base-square-root ratio vanishes.
- Route/APIs: compiled `D/sqrt rounds` envelope; `Real.sqrt_le_sqrt`;
  `Finset.sum_const`; filter multiplication/squeeze; WithTop selector;
  stopped `MemLp`; finite-sum integration; L1/in-measure/stopping a.e. parents.
- Contracts: exact dependent source and inherited regularity, positive base,
  explicit ratio limit, index/base lower envelope, one `IsStoppingTime` per
  index, and both pointwise window bounds; no independence or optional
  stopping.
- Retrieval/status: compiled explicit parent and exact declarations, recorded
  Mathlib/RL cards, weapon inspiration only; `leanCompiled` with nineteen
  declarations, root import, and a width-`2n+1` endpoint-reaching trajectory
  canary. Independent review found no P0/P1 and all P2/P3 findings are closed.
- Failure policy/next route: base divergence alone is insufficient for this
  finite-union proof, and a.e. still needs a lower envelope. A stronger theorem
  needs either a concrete adaptive schedule calibration or genuine
  optional-stopping/uniform-integrability infrastructure. Do not infer raw
  episodes, behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Polynomial-Base Growing Raw-Window Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-BASE-GROWING-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: exact-natural-filtration stopping times satisfying
  `explicitRounds n <= tau_n <= explicitRounds n+n` preserve expected
  absolute, L1/eLpNorm, in-measure, and a.e. convergence.
- Route/APIs: Mathlib log/sqrt inequalities; the compiled behavior and return
  all-prefix L1 parents; fourth-power square-root comparison;
  `Finset.sum_const`; WithTop fixed-window selector; stopped-value `MemLp`;
  finite-sum integration; L1/in-measure/stopping a.e. parents.
- Contracts: exact dependent source and inherited regularity, one
  `IsStoppingTime` per index, and both pointwise bounds; no independence or
  optional-stopping identity.
- Retrieval/status: exact no-hit; compiled local and Mathlib evidence,
  recorded cards, weapon inspiration only; `leanCompiled` with twenty-two
  declarations, root import, endpoint-reaching trajectory canary, and
  independent review with its P3 L1 canary request closed.
- Failure policy/next route: the broader rate-controlled raw-window theorem
  now compiles. Do not infer arbitrary candidate sets, arbitrary
  diverging-stop L1, sharper rates, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Growing-Window Grid Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-GROWING-WINDOW-GRID-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: exact-natural-filtration stopping times selecting any finite
  candidate among `explicitRounds (n+offset)`, `offset <= windowAt n`, preserve
  expected-absolute, `L1/eLpNorm`, in-measure, and a.e. convergence when
  `windowAt -> infinity`.
- Route/APIs: fourth-power grid monotonicity and `untopA` transport; compiled
  summable explicit-prefix L1 envelope; `summable_nat_add_iff`;
  `Summable.sum_le_tsum`; `tendsto_sum_nat_add`; stopped-value `MemLp`;
  finite-sum integration; L1 norm and in-measure APIs; stopping a.e. parent.
- Contracts: exact dependent source and inherited regularity, one
  `IsStoppingTime` per index, divergent finite candidate width, and pointwise
  grid membership; no independence or optional-stopping identity.
- Retrieval/status: exact no-hit; compiled local and Mathlib evidence,
  recorded cards, weapon inspiration only; `leanCompiled` with eighteen public
  declarations, root import, and a trajectory-dependent width-`n` canary that
  reaches the growing right endpoint.
- Failure policy/next route: the explicit fourth-power-base width-`n` raw
  window now compiles downstream. Do not infer arbitrary raw
  growing intervals, arbitrary diverging-stop L1, sharper rates, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Fixed-Window Stopping-Time L1 Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: pointwise `n+1 <= tau_n <= n+1+window` exact-natural-filtration
  stopping times preserve expected-absolute, `L1/eLpNorm`, in-measure, and
  almost-everywhere convergence of the exact natural average realized
  behavior-regret process.
- Route/APIs: finite `WithTop` offset transport; shifted finite sum of the
  compiled all-prefix L1 envelopes; `memLp_stoppedValue`;
  `Finset.single_le_sum`; finite-sum integration;
  `MemLp.eLpNorm_eq_integral_rpow_norm`; compiled stopping a.e. parent.
- Contracts: exact dependent generated source and inherited regularity, one
  `IsStoppingTime` per index, and one deterministic pointwise window; no
  independence or optional-stopping identity.
- Retrieval/status: exact no-hit; compiled local and Mathlib evidence,
  recorded cards, weapon inspiration only; `leanCompiled` with twelve public
  declarations, root import, and deterministic external canary.
- Failure policy/next route: the downstream sparse-grid growing-window route
  is compiled; a raw-prefix result still needs a quantitative envelope/window
  comparison. Do not infer arbitrary diverging-stop L1 convergence, a sharper
  rate, raw episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI.

## Compiled: Deterministic-Moment Expected Bounded-Stopping Regret

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-DETERMINISTIC-MOMENT-EXPECTED-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: the exact stopped second moment is bounded by a deterministic
  finite sum of positive-prefix envelopes; fixed-quarter overflow is at most
  `(1/2)*sqrt(momentBudget)`, and expected stopped regret is at most the finite
  logarithmic-rate budget plus that deterministic term.
- Route/APIs: conservative `HasSubgaussianMGF` second moment; cumulative
  behavior envelope; exact expected-minus-deviation identity; stopped-value
  coordinate selection; `integrable_finset_sum`, `integral_finset_sum`, and
  `sqrt_le_sqrt`; compiled exact-moment parent.
- Contracts: exact finite Standard Borel dependent causal source, bounded
  means, selected-reward sub-Gaussianity, support/floor, positive deterministic
  coordinates, and pointwise `1 <= tau <= T` exact-filtration stopping time;
  no independence or optional-stopping identity.
- Retrieval/status: exact no-hit; compiled local and Mathlib evidence,
  recorded cards, and OFUL/weapon inspiration only; `leanCompiled` with nine
  declarations in two modules and external stopped-moment/expectation canaries.
- Failure policy/next route: the finite moment sum may grow with `T`; simplify
  it or prove a rate-compatible envelope separately. Do not infer the sharp
  variance bound, endpoint monotonicity, asymptotic expected rate, arbitrary
  confidence, unbounded stopping, raw episodes, behavior=recommended,
  minimax/reachability, or complete UCB-VI.

## Compiled Parent: Exact-Moment Expected Bounded-Stopping Regret

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-EXPECTED-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: the exact stopped average realized behavior regret is in `L2`;
  on the fixed quarter bad event its absolute overflow is at most
  `(1/2)*sqrt(exact stopped second moment)`, and expected stopped regret is at
  most the finite positive-prefix logarithmic-rate sum plus that overflow.
  The same result retains three-quarter good mass and the pathwise stopped rate.
- Route/APIs: generic `2,2` Holder indicator wrapper; bounded behavior
  `MemLp.of_bound`; return-deviation `HasSubgaussianMGF.memLp`; exact process
  identity; `memLp_stoppedValue`; `Finset.single_le_sum`; `integral_mono`;
  compiled three-quarter parent.
- Contracts: exact finite Standard Borel causal source, bounded means,
  selected-reward sub-Gaussianity, support/floor, positive horizon and finite
  bound, and pointwise `1 <= tau <= T` exact-filtration stopping time; no
  independence or optional-stopping identity.
- Retrieval/status: exact no-hit; compiled local and exact Mathlib evidence,
  recorded cards, and OFUL/weapon inspiration only; `leanCompiled` with eleven
  declarations, two root-imported focused modules, and external canaries.
- Failure policy/next route: retain the exact second moment. A numerical or
  asymptotic expected rate needs a separate stopped-moment envelope; do not
  infer arbitrary confidence, unbounded stopping, nonnegative expected regret,
  raw episodes, behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Explicit Three-Quarter Bounded-Stopping Good Event

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-THREE-QUARTER-GOOD-EVENT-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: the unchanged self-consistent model schedule costs at most `1/8`
  on every finite prefix; with a global return budget `1/8`, the joint and
  stopped bad events cost at most `1/4`, their measurable complement has real
  mass at least `3/4`, and the stopped logarithmic pathwise rate holds there.
- Route/APIs: exponent-six shifted-power comparison to the inverse-square sum;
  exact local-delta/model-budget rewrites; `ENNReal.ofReal_sum_of_nonneg` and
  `ENNReal.ofReal_add`; compiled single-model terminal;
  `MeasureTheory.probReal_compl_eq_one_sub`.
- Contracts: inherited causal source/support/MGF semantics plus explicit
  `0 < mdp.horizon`, `0 < T`, and one exact-filtration stopping time satisfying
  `1 <= tau <= T`; the confidence schedule is unchanged and no independence
  or optional-stopping identity is used.
- Retrieval/status: exact no-hit; compiled local parent and scalar/budget APIs,
  recorded Mathlib/scenario/textbook/paper cards, and weapon inspiration only;
  `leanCompiled` with five declarations, root/focused/Tests builds, and direct
  one-or-two stopping-time canaries for the `1/8`, `1/4`, and `3/4` outputs.
- Failure policy/next route: arbitrary confidence requires a parameterized
  model/episode schedule. This leaf does not prove stopped expectation,
  unbounded-anytime, raw episodes, behavior=recommended, minimax/reachability,
  optimal UCB-VI rates, or complete UCB-VI.

## Compiled: Bounded Stopping-Time Single-Model-Event Tail

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-SINGLE-MODEL-EVENT-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: for one exact-natural-filtration stopping time with
  `1 <= tau <= T`, the stopped violation is contained in one horizon-`T`
  model event plus the finite return-deviation window and has probability at
  most `modelFailureBudget mdp T + ENNReal.ofReal returnDelta`.
- Route/APIs: heterogeneous finite-horizon event monotonicity; equal allocation
  over `Finset.Icc 1 T`; fixed-prefix violation-to-model/return inclusion;
  `measure_biUnion_finset_le_of_uniform`; `measure_union_le`; stopped-event
  containment and `measure_mono`.
- Contracts: inherited causal source/support/MGF semantics plus `0 < T`, one
  positive bounded `IsStoppingTime`, and `0 < returnDelta <= 1`. The model
  coordinate event family and local-delta schedule remain unchanged across
  prefixes; no event independence is used.
- Retrieval/status: exact no-hit; compiled bounded-stopping, fixed-prefix,
  model-confidence, and return-concentration parents plus exact finite-union
  APIs/cards; `leanCompiled` with thirteen declarations, root/focused/Tests
  builds, trajectory-dependent one-or-two-prefix canary, baseline-only axioms,
  clean placeholders, and no P0-P3 in independent review.
- Failure policy/next route: retain the horizon model budget; this is not a
  total-`delta` theorem. Unbounded stopping needs a summable all-time event or
  moment route. No optional stopping, expectation identity, raw episodes,
  behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Bounded Stopping-Time High-Probability Equal-Round Regret

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: for one exact-natural-filtration stopping time with pointwise
  `1 <= tau <= T`, the stopped exact average realized behavior regret exceeds
  its stopped scheduled logarithmic rate only on a filtered-measurable event
  contained in the finite fixed-prefix window; the window and stopped event
  are bounded by the exact sum of their model and return budgets.
- Route/APIs: `WithTop` finite-bound coercion; prior `StronglyAdapted` natural
  process; `stronglyMeasurable_stoppedValue_of_le`; fixed-prefix violation
  inclusion/tail; `Finset.Icc`; finite biUnion measurability and outer-measure
  subadditivity.
- Contracts: inherited causal source/support/MGF semantics plus one
  `IsStoppingTime`, pointwise positive finite bounds, and scheduled positive
  unit-bounded return shares on the finite window. No event independence is
  used.
- Retrieval/status: exact no-hit; two compiled RL parents, local OFUL pattern,
  Mathlib stopping/finite-union APIs, and recorded literature/cards;
  `leanCompiled` with fourteen declarations, root/focused/Tests builds, and a
  genuine trajectory-dependent one-or-two-prefix canary; baseline-only axioms
  and independent review with no P0-P3.
- Failure policy/next route: preserve the exact finite sum. A single global
  delta needs an allocation theorem; unbounded stopping needs a summable
  all-time event or moment route. No optional stopping, expectation identity,
  raw episodes, behavior=recommended, minimax/reachability, or complete UCB-VI.

## Compiled: Diverging Stopping-Time Almost-Sure Equal-Round Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-DIVERGING-STOPPING-TIME-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the exact average realized behavior-regret process is strongly
  adapted to the dependent natural batch filtration; every stopped value is
  measurable; and schedule-indexed stopping times converge a.e. to zero when
  their `untopA` values diverge. Pointwise `n <= tau_n.untopA` is a
  compiled sufficient contract.
- Route/APIs: dependent `Filtration.piLE`; finite restriction and coordinate
  evaluation; successor-batch finite-sum adaptedness; `ProgMeasurable`;
  Mathlib `measurable_stoppedValue`; compiled random-prefix limit transport.
- Contracts: inherited causal source/support/MGF semantics, exact natural
  successor indexing and normalization, one `IsStoppingTime` proof per
  schedule index, and `untopA` divergence on the same source measure. Since
  `top.untopA` is an arbitrary fixed Nat default, divergence forces eventual
  finiteness but permits finitely many early `top` values.
- Retrieval/status: exact no-hit; Mathlib filtration/stopping source, compiled
  random-prefix parent, and local OFUL stopping patterns are direct evidence;
  `leanCompiled` with fourteen declarations, root import, focused/Tests builds,
  and an extensionally trajectory-dependent two-point source canary with
  explicit witnesses for both branches.
- Failure policy/next route: no optional stopping, stopped expectation identity,
  anytime rate, raw episodes, behavior=recommended, minimax/reachability, or
  UCB-VI. A quantitative stopped consumer needs separate event and moment or
  integrability contracts.

## Compiled Parent: Diverging Random-Prefix Almost-Sure Equal-Round Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-DIVERGING-RANDOM-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: every coordinate of the exact natural realized behavior-regret
  process evaluated at a measurable random prefix is measurable, and the
  process tends to zero a.e. whenever those prefixes diverge a.e. on the same
  causal measure; pointwise `n <= tau_n` is a compiled sufficient contract.
- Route/APIs: deterministic all-prefix parent; countable-product joint
  measurability; random-index composition; a.e. set intersection;
  `Tendsto.comp`; atTop lower-envelope transport.
- Contracts: inherited finite/Standard-Borel/probability/support/MGF/source
  semantics plus coordinatewise schedule measurability and a.e. divergence.
  No independence, stopping-time, or optional-stopping premise is introduced.
- Retrieval/status: exact no-hit; compiled local parent/UCB pattern and exact
  Mathlib APIs; `leanCompiled` with eight declarations, root import, generic
  random-Bool and trajectory-dependent Bool/Bool source canaries, baseline
  axioms, no placeholders, and defect-free independent re-review.
- Failure policy/next route: bounded or recurrent schedules are rejected.
  Genuine stopping-time/adaptedness, anytime rates, raw episodes,
  behavior=recommended, minimax/reachability, and UCB-VI remain separate.

## Compiled Parent: All-Prefix Almost-Sure Equal-Round Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-ALL-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the exact per-batch-normalized, equal-round-weighted realized
  behavior-regret process is measurable on every deterministic prefix and
  tends to zero almost everywhere under the generated heterogeneous causal
  trajectory measure.
- Route/APIs: compiled expected-regret a.e. limit plus Mathlib Cesaro;
  inverse-square return delta; square-root/log radius envelope; measurable
  shifted return events; event-measure tsum; first Borel-Cantelli; shift back
  from `n+1`; exact expected-minus-deviation identity.
- Contracts: inherited finite nonempty Standard Borel spaces, probability,
  positive horizon/floor/proxy, bounded rewards, uniform selected-reward MGF,
  support/floor and filtration/measurability; no independence or stopping time.
- Retrieval/status: exact no-hit; compiled local/Mathlib evidence;
  `leanCompiled` with 21 declarations, root import, direct component/terminal
  canaries, clean placeholders, baseline-only axioms, and defect-free review.
- Failure policy/next route: preserve one source, natural successor indexing,
  global centering, and per-batch normalization before equal round weights.
  Its measurable a.e.-diverging random-prefix consumer now compiles above;
  stopping-time/anytime/raw-episode, behavior=recommended, minimax,
  reachability, and complete UCB-VI remain separate unfinished routes.

## Compiled Parent: Explicit Polynomial-Prefix Almost-Sure Equal-Round Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the exact per-batch-normalized, equal-round-weighted realized
  behavior-regret process on prefixes `(n+1)^4` tends to zero almost
  everywhere under the generated heterogeneous causal trajectory measure.
- Route/APIs: compiled all-prefix L1 decomposition; polynomial specialization;
  shifted p-series; Markov; integral/ENNReal bridges; first Borel-Cantelli;
  reciprocal-natural threshold intersection.
- Contracts: inherited finite nonempty Standard Borel spaces, probability,
  positive horizon/floor/proxy, bounded rewards, uniform selected-reward MGF,
  support/floor and filtration/measurability; no independence or stopping time.
- Retrieval/status: exact no-hit; compiled local/Mathlib evidence;
  `leanCompiled` with 21 declarations, root import, direct terminal canaries,
  clean placeholders, baseline-only axioms, and defect-free local review.
- Failure policy/next route: retain the sparse fourth-power schedule and exact
  natural process. The all-prefix deterministic a.e. consumer now compiles
  above; this route remains regression evidence and does not imply anytime,
  stopping-time, raw-episode, behavior=recommended, minimax, reachability, or
  complete UCB-VI results.

## Compiled: All-Prefix L1 Equal-Round Natural Realized Regret

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-ALL-PREFIX-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the per-batch-normalized, equal-round-weighted natural average
  realized behavior-regret process is integrable and `MemLp 1` on every
  deterministic prefix; its expected absolute value and named `Lp Real 1`
  value tend to zero, and it tends to zero in measure.
- Route/APIs: adapted normalized-return increments and conditional-MGF sum;
  MGF absolute integral; linear variance-proxy bound; `Real.sqrt` order and
  inverse-square-root limit; exact expected-minus-deviation identity;
  expected-process logarithmic envelope; Mathlib integral/Lp/in-measure APIs.
- Contracts: inherited finite nonempty Standard Borel spaces, probability,
  positive horizon/floor/proxy, bounded rewards, uniform selected-reward
  sub-Gaussianity, support/floor, global-return measurability and filtration;
  no new independence, summability, or stopping-time premise.
- Retrieval/status: exact no-hit; compiled local and Mathlib evidence;
  `leanCompiled` with 23 declarations, root import, Bool/Bool canaries,
  baseline-only representative axioms, and no placeholders.
- Failure policy: keep one source, natural successor indexing, per-batch
  normalization then equal round weights, and global centering. Do not use the
  total-mass-weighted L1 theorem as an equality. No almost-sure, anytime,
  raw-episode, minimax, reachability, behavior=recommendation, or UCB-VI claim.

## Compiled: Explicit Polynomial-Prefix Absolute In-Measure Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-ABSOLUTE-IN-MEASURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: the per-batch-normalized, equal-round-weighted natural average
  realized behavior-regret process at `(n+1)^4` prefixes is measurable and
  tends to zero in Mathlib `TendstoInMeasure`; every fixed positive distance
  event is measurable, eventually lies in the exact parent event, and has
  ENNReal probability tending to zero.
- Route/APIs: parent event-good upper envelope; expected-regret
  nonnegativity; exact expected-minus-return-deviation identity; strict
  return-event complement; positive division; `abs_lt`; `measure_mono`;
  ENNReal squeeze; `tendstoInMeasure_iff_dist`.
- Contracts: full inherited finite nonempty Standard Borel, probability,
  positivity, bounded-mean, selected-reward sub-Gaussian, path-support,
  filtration, and StronglyAdapted ledger; no new independence, summability,
  or stopping-time assumption.
- Evidence/status: exact no-hit; compiled local and Mathlib
  measure/order/asymptotic APIs; UCB-VI/scenario placement and weapons
  inspiration only; `leanCompiled`; 11 declarations, root import, focused and
  `Tests.Basic` builds, complete Bool/Bool canaries, clean placeholders, and
  baseline-only axioms. Independent review found no proof/scope issue; its
  stale-blueprint and two direct-canary observations were resolved.
- Failure policy: preserve one dependent source, `t -> t+1`, per-batch
  normalization followed by equal round weights, global centering,
  fourth-power schedule, and exact budget. Do not transport from the older
  total-mass-weighted `realizedSuccessorAverageRegret` theorem. This is not
  all-prefix, anytime, a.s., L1, minimax, reachability, behavior=recommended,
  raw-episode regret, or complete UCB-VI.
- Next route: L1/a.s./all-prefix consumers require separate uniform
  integrability or summable-tail work; no such strengthening is currently
  recorded as compiled.

## Compiled: Explicit Polynomial-Prefix Upper-Tail Probability Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-UPPER-TAIL-IN-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: for every fixed `epsilon > 0`, the measurable event
  `{epsilon < scheduled average realized behavior regret}` is eventually
  contained in the compiled rate violation, has trajectory probability at
  most the exact vanishing model-tail/return budget, and its ENNReal
  probability tends to zero.
- Route/APIs: parent rate `Tendsto`; `eventually_lt_const`; strict order
  transitivity; parent violation-probability projection; `measure_mono`; ENNReal
  squeeze between zero and the budget.
- Contracts: the full parent finite nonempty Standard Borel, probability,
  positivity, bounded-mean, selected-reward sub-Gaussian, path-support,
  filtration, and StronglyAdapted ledger; no new independence, summability, or
  stopping-time assumption.
- Evidence/status: exact no-hit; compiled local parent plus Mathlib
  measure/order/asymptotic APIs; UCB-VI/scenario placement and weapons
  inspiration only; `leanCompiled`; 8 declarations, root import, focused and
  `Tests.Basic` builds, typed Bool/Bool canaries for every root field, clean
  placeholders, baseline axioms, and independent review integrated.
- Failure policy: preserve one dependent source, `t -> t+1`, per-batch
  normalization, global centering, fourth-power schedule, and exact budget.
  One-sided subsequence only, not absolute in-measure, lower-tail, all-prefix,
  anytime, minimax, reachability, behavior=recommended, or complete UCB-VI.
- Next route: separately prove lower-tail/absolute control or a precise process
  transport to an existing absolute in-measure theorem.

## Compiled: Explicit Polynomial-Prefix High-Probability Average Realized Behavior-Regret Consistency

- Leaf: `RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`.
- Statement: `scale=burnin=n+1`, `rounds=scale^4`, and
  `returnDelta=exp(-scale)` give a vanishing exact model-tail/return budget
  and vanishing full average realized-regret envelope; the root terminal
  packages measurable one-sided violations, inclusion, exact probability
  bounds, eventual strict-subunit confidence, and event-good bounds for
  every scheduled prefix.
- Route/APIs: own-count proxy coordinate bound and exact finite sum; dummy
  zero removal; sub-Gaussian radius square; scheduled log/exp algebra;
  `ENNReal.ofReal`; Tendsto composition/addition; projection of the compiled
  burn-in/tail terminal.
- Contracts: finite nonempty Standard Borel State/Action, probability,
  positive horizon/base floor/proxy/counts, bounded means, uniform selected-
  reward sub-Gaussianity, path support/floor, and inherited filtration/
  StronglyAdapted contracts; no model/return independence.
- Evidence/status: exact no-hit; compiled local parent routes and Mathlib
  finite-sum/measure/martingale/sub-Gaussian/order/log-sqrt-exp/asymptotic
  APIs; UCB-VI/scenario placement and weapons inspiration only;
  `leanCompiled`; 25 declarations, root import, Bool/Bool terminal and limit
  canaries, clean placeholders, standard axioms, and no P0-P3 review finding.
- Failure policy: preserve one dependent source, `t -> t+1`, per-batch
  normalization, global initial-law centering, and exact union shares.
  Fourth-power prefix subsequence and one-sided upper tail only; no
  all-prefix/anytime/absolute-in-measure/minimax/reachability/raw-episode/
  behavior=recommended/complete-UCB-VI claim.
- Downstream status: consumed by the compiled fixed-`epsilon` upper-tail
  probability route above.

## Compiled: Burn-In Tail High-Probability Logarithmic Cumulative/Average Realized Behavior Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-BURNIN-TAIL-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: for fixed `burnin <= rounds`, measurable cumulative and
  positive-round average realized behavior-regret violations are contained in
  the infinite model-tail/normalized-return union and have measure at most
  `tailModelFailureBudget burnin + ENNReal.ofReal returnDelta`; every good path
  obeys `2H*burnin + C_mdp*(1+log rounds) + returnRadius` and its round average.
- Route/APIs: `Finset.sum_range_add_sum_Ico`; per-round `2H`; tail-complement
  coordinate planning; nonnegative full planning/log envelope; exact
  realized=expected-deviation identity; normalized return tail;
  `measure_union_le`; `measure_mono`; positive division.
- Contracts: finite nonempty Standard Borel State/Action, probability,
  positive horizon/rounds/floor/proxy, bounded means, uniform selected-reward
  sub-Gaussian law, path support/floor, `burnin <= rounds`, and
  `0 < returnDelta <= 1`; no model/return independence.
- Evidence/status: exact no-hit; compiled local fixed-prefix/tail/return routes
  and Mathlib finite-sum/measure/martingale/sub-Gaussian/order/log cards;
  UCB-VI placement and weapons inspiration only; `leanCompiled`; sixteen
  declarations, root import, typed Bool/Bool canaries, clean placeholders and
  baseline axioms.
- Failure policy: preserve one dependent source, actual `t -> t+1` successor
  batches, per-batch normalization, global initial-law centering, and exact
  two-share budget. Fixed burn-in/prefix only; no anytime/minimax/reachability/
  raw-episode/complete-UCB-VI claim.
- Next route: choose growing sublinear `burnin rounds` and vanishing
  `returnDelta rounds`; compile the deterministic average-envelope limit and
  total failure-budget limit before any asymptotic high-probability consumer.

## Compiled: Fixed-Prefix High-Probability Logarithmic Cumulative/Average Realized Behavior Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FIXED-PREFIX-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-AVERAGE-REALIZED-BEHAVIOR-REGRET`.
- Statement: natural round `t` uses the actual successor batch `t+1`; cumulative
  sample-average realized behavior regret and its positive-round average have
  measurable one-sided violation sets contained in the actual model/return
  union, with probability at most the accumulated model budget plus
  `ENNReal.ofReal returnDelta` and envelope equal to the compiled logarithmic
  expected-regret rate plus a normalized return radius.
- Nontrivial confidence: the terminal explicitly transports an exact total
  budget below one to strict subunit probability for the joint event and both
  violations; the unrestricted exact upper bound itself may be at least one.
- Route/APIs: reciprocal-batch `Kernel.HasSubgaussianMGF.const_mul`; dummy-zero
  `StronglyAdapted piLE`; local conditional finite-sum absolute tail;
  `successorGlobalReturnIncrement_succ_eq`; `Finset.sum_sub_distrib`;
  measurable finite sums; `measure_union_le`; `measure_mono`; the previous
  fixed-prefix expected-log parent.
- Contracts: finite nonempty Standard Borel State/Action, probability, positive
  horizon/rounds/floor/proxy and batches, bounded means, uniform selected-
  reward sub-Gaussian law, path support, and `0 < returnDelta <= 1`.
- Evidence/status: exact no-hit; compiled local causal return/model/log routes
  and Mathlib finite-sum/conditional-expectation/martingale/sub-Gaussian/
  measure/order/log-sqrt cards; UCB-VI placement and weapons inspiration only;
  `leanCompiled`; 41 declarations, root import, and Bool/Bool terminal canary.
- Failure policy: preserve one dependent source, actual batches, `t -> t+1`,
  per-batch normalization, global initial-law centering, positive prefix, and
  exact model-plus-return shares. No one-episode online, arbitrary model delta,
  anytime/uniform-time, minimax/optimal-rate, reachability, or complete UCB-VI
  claim. Next build an explicit all-prefix/asymptotic consumer only after
  scheduling `returnDelta` and addressing the accumulated model budget.

## Compiled: Fixed-Prefix High-Probability Logarithmic Cumulative Behavior Expected Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FIXED-PREFIX-HIGH-PROBABILITY-LOGARITHMIC-CUMULATIVE-BEHAVIOR-EXPECTED-REGRET`.
- Statement: on the genuine dependent causal source, the measurable event that
  the random natural-prefix cumulative actual behavior expected regret exceeds
  `C_mdp * (1 + log rounds)` is contained in the actual prefix model bad event
  and has measure at most the exact accumulated model-confidence budget; every
  model-good path is bounded through the natural planning sum.
- Route/APIs: unfold `finiteHorizonBadEvent` and use
  `Set.mem_iUnion_of_mem`; apply the coordinate actual-behavior planning
  theorem and `Finset.sum_le_sum`; dominate planning by the integrated/log
  parents; prove process and violation measurability with
  `Finset.measurable_sum` and `measurableSet_lt`; finish with set inclusion and
  `measure_mono`.
- Contracts: finite nonempty Standard Borel State/Action, probability initial
  law, positive horizon/floor/proxy, bounded means, uniform mean-compatible
  selected-reward sub-Gaussianity, and path support. No new independence or
  conditional-MGF contract is added beyond the compiled model-confidence
  parent.
- Evidence/status: exact route no-hit; compiled natural logarithmic,
  finite-prefix model-confidence, and coordinate planning routes plus Mathlib
  finite-sum/measure/kernel/sub-Gaussian cards; RL/UCB-VI placement and optimism
  inspiration only; `leanCompiled`; thirteen declarations, root import, and
  Bool/Bool terminal canary.
- Failure policy: preserve actual behavior versus recommendation, one source
  and samples, `t -> t+1`, schedules/budgets, initial exclusion, and both model
  shares. The exact accumulated budget is not an arbitrary delta and is not
  claimed to vanish. This is fixed-prefix probability for behavior expected
  regret, not realized return, uniform-time/anytime, every-trajectory,
  reachability, minimax/optimal-rate, or complete UCB-VI. The realized
  fixed-prefix consumer above now compiles the required normalized return
  process and combined event.

## Compiled: Natural Causal Explicit Logarithmic Cumulative/Average Behavior Rate

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-EXPLICIT-LOGARITHMIC-CUMULATIVE-AVERAGE-BEHAVIOR-EXPECTED-REGRET-RATE`.
- Statement: actual expected cumulative behavior regret on the one dependent
  causal source is at most `C_mdp * (1 + log rounds)`; actual average behavior
  expected regret is at most that quantity divided by `rounds`. Both actual
  objectives expose named Big-O interfaces and the actual average tends to
  zero.
- Route/APIs: expand the coordinate rate into inverse-square, shifted
  harmonic, and high-power terms; telescope through
  `1/((t+1)*(t+2))` with `Finset.sum_range_sub'`; use
  `one_div_pow_le_one_div_pow_of_le`; compare with Mathlib harmonic numbers and
  `harmonic_le_one_add_log`; absorb constants using the zero-safe
  `one_le_one_add_log_natCast`; close limits and asymptotics with
  `Real.isLittleO_log_id_atTop`,
  `tendsto_const_div_atTop_nhds_zero_nat`, and `Asymptotics.isBigO_iff`.
- Contracts: scalar finite-sum leaves are unconditional; causal consumers
  retain finite nonempty Standard Borel State/Action, probability initial law,
  positive horizon/floor/proxy, bounded means, uniform mean-compatible
  selected-reward sub-Gaussianity, and exploratory path support.
- Evidence/status: exact route no-hit; compiled finite-prefix and explicit
  integrated parents plus Mathlib finite-sum/order/log/asymptotic cards;
  RL/UCB-VI placement and optimism inspiration only; `leanCompiled`; thirty
  declarations, root import, and Bool/Bool pointwise, Big-O, zero-prefix, and
  limit canaries.
- Failure policy: preserve actual behavior versus recommendation, one source
  and samples, `t -> t+1`, schedules/budgets, initial exclusion, and both
  integrated confidence shares. This is expectation over source randomness,
  not realized-return, every-trajectory, anytime/high-probability,
  reachability, minimax/optimal-rate, or complete UCB-VI. Its fixed-prefix
  high-probability random-process consumer now compiles above and retains the
  accumulated nonvanishing confidence budget.

## Compiled: Natural Causal Finite-Prefix Cumulative/Average Behavior Rate

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-FINITE-PREFIX-CUMULATIVE-AVERAGE-BEHAVIOR-EXPECTED-REGRET-RATE`.
- Statement: the pathwise natural-prefix sum of actual exploratory successor-
  policy expected regrets is integrable on the same dependent causal measure;
  its expectation equals the sum of coordinate expected absolute regrets and
  is bounded by the cumulative explicit integrated envelope. The corresponding
  deterministic and actual averages tend to zero.
- Route/APIs: `IntegrabilitySums.integrable_finset_sum`;
  `ExpectationBochnerSums.integral_finset_sum`; coordinate nonnegativity;
  `Finset.sum_le_sum`; nonnegative division; unit-weight
  `natWeightedAverage`; `tendsto_natWeightedAverage_zero`; `squeeze_zero'`.
- Contracts: beyond the module-wide finite measurable-space assumptions, the
  finite-sum identity needs a probability initial law and bounded means for
  coordinate integrability; the rate terminal retains finite
  nonempty Standard Borel State/Action, positive horizon/floor/proxy, uniform
  selected-reward sub-Gaussianity, and path support.
- Evidence/status: exact route no-hit; compiled pointwise rate, finite-sum
  wrappers, and positive-weight-average candidate plus Mathlib finite-sum/
  integral/order/asymptotic cards; RL/UCB-VI placement and optimism inspiration
  only; `leanCompiled`; seventeen declarations and Bool/Bool exact-sum,
  cumulative-bound, zero-prefix, rate-limit, and actual-average-limit canaries.
- Failure policy: preserve actual behavior versus recommendation, one source,
  samples, `t -> t+1`, budgets, initial exclusion, and both integrated
  confidence shares. The explicit logarithmic consumer above closes the
  shifted finite sums and actual Big-O statements. This parent remains the
  exact finite-prefix assembly surface and is not realized-return,
  every-trajectory, anytime, reachability, minimax/optimal-rate, or complete
  UCB-VI control.

## Compiled: Natural Causal Explicit Integrated Behavior Rate

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-EXPLICIT-INTEGRATED-BEHAVIOR-EXPECTED-REGRET-RATE`.
- Statement: expected absolute regret of the actual exploratory successor
  policy at coordinate `t` is at most a named fully expanded envelope equal to
  planning rate plus `4 * horizon * localDelta`; the envelope tends to zero.
- Route/APIs: generic `rate + bad.indicator envelope` majorant;
  `integral_mono`, indicator/add/constant integrals and `Measure.real_def`;
  measurable model-round event; event-outside actual behavior planning bound;
  global `2H`; exact coordinate event mass; ENNReal `toReal` transport;
  summable local delta and `squeeze_zero'`.
- Contracts: generic lemma uses a probability measure, measurable event,
  integrable function, nonnegative rate, and local/global bounds; causal
  terminal retains finite nonempty Standard Borel State/Action, probability,
  positive horizon/floor/proxy, bounded means, selected-reward sub-Gaussianity,
  and path support.
- Evidence/status: exact combined route no-hit; compiled event/pointwise/L1
  parents plus Mathlib integral/order/asymptotic APIs; RL/UCB-VI placement only
  and optimism weapon inspiration only; `leanCompiled`; ten declarations and
  Bool/Bool bound/rate/limit canaries.
- Failure policy: preserve actual behavior versus recommendation, one source,
  samples, `n -> n+1`, budgets, initial exclusion, and two confidence shares;
  no realized-return MGF. The compiled finite-prefix consumer above now closes
  cumulative/average assembly and Cesaro consistency. This parent remains
  per-coordinate and does not provide realized-return, every-trajectory,
  anytime, reachability, minimax/optimal-rate, or complete UCB-VI control.

## Compiled: Natural Causal Behavior-Expected L1 Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-L1-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`.
- Statement: the actual exploratory successor-policy expected-regret process
  is coordinate integrable and `MemLp Real 1`, tends to zero in expected
  absolute value and named `Lp Real 1`, and shares one terminal/measure with
  the compiled realized-regret L1 result.
- Route/APIs: apply the pointwise policy bound to get `2 * horizon`; use
  `Integrable.of_bound`; apply Mathlib
  `tendsto_integral_filter_of_norm_le_const` to the compiled a.e. limit;
  simplify absolute values by nonnegativity; package with
  `memLp_one_iff_integrable`, exponent-one `eLpNorm`, `MemLp.toLp`, and
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`.
- Contracts: the bound/integrability need finite measurable nonempty State/
  Action, equality/singletons, probability initial law, and bounded means;
  convergence retains finite nonempty Standard Borel State/Action, positive
  horizon/floor/proxy, bounded means, selected-reward sub-Gaussianity, and
  path support.
- Evidence/status: exact combined theorem retrieval no-hit; compiled local
  a.e./measurability and realized-L1 parents plus Mathlib integral/Lp/
  asymptotic APIs; RL/UCB-VI placement only and weapon inspiration only;
  `leanCompiled`; thirteen declarations and Bool/Bool terminal/projection
  canaries.
- Failure policy: preserve actual behavior vs recommendation, one source,
  samples, `n -> n+1`, budgets, initial exclusion, and realized centering; the
  behavior proof uses no realized-return MGF. The explicit-rate consumer above
  closes the one-event finite-coordinate expectation bound. This parent has
  no cumulative/average, every-trajectory, anytime, reachability,
  minimax/optimal-rate, or complete-UCB-VI claim.

## Compiled: Natural Causal Behavior-Expected In-Measure Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-IN-MEASURE-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`.
- Statement: every coordinate of the actual exploratory
  `source.successorPolicyAt` expected-regret process is measurable and the
  process tends to zero in Mathlib `TendstoInMeasure` on the one genuine
  dependent causal measure; a joint terminal also retains realized-regret
  convergence in measure on that same source.
- Route/APIs: represent any measurable finite policy-table selector statistic
  as a finite sum of singleton indicators; use `Finset.measurable_sum`,
  `Measurable.ite`, and singleton measurability; compose sampled optimistic
  table measurability with `measurable_pi_apply t`; unfold the actual
  successor selector; promote coordinates to strong measurability and apply
  Mathlib `tendstoInMeasure_of_tendsto_ae`; pair with the compiled realized
  in-measure terminal.
- Contracts: the selector lemma needs finite measurable State/Action with
  equality and measurable singletons, a nonempty Action, and a probability
  initial law; it does not need a nonempty State. The
  terminal retains finite nonempty Standard Borel State/Action, positive
  horizon/base floor/reward proxy, bounded means, uniform mean-compatible
  selected-reward sub-Gaussianity, and full-exploration path support.
- Evidence/status: exact successor-policy expected-regret measurability
  retrieval no-hit; compiled sampled table selector, behavior a.e., and
  realized in-measure parents plus Mathlib finite-sum/measure/asymptotic APIs;
  RL/UCB-VI cards are placement only and `WEAPON-UCB-OPTIMISM` is inspiration
  only; `leanCompiled`; four declarations; direct/root/Tests Bool/Bool terminal
  and explicit projection canaries.
- Failure policy: preserve the actual exploratory policy, recommendation/
  behavior distinction, one dependent source, actual samples, `n -> n+1`,
  scheduled budgets, initial exclusion, and realized-regret global centering.
  The L1 consumer above now closes `MemLp 1`, expected-absolute, exact
  `eLpNorm`, and named `Lp` convergence. This parent supplies no explicit
  integrated finite-round rate, every-trajectory, anytime, reachability,
  minimax, optimal-rate, or complete-UCB-VI result.

## Compiled: Natural Causal Behavior-Expected And Realized A.E. Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-ALMOST-SURE-BEHAVIOR-EXPECTED-AND-REALIZED-CONSISTENCY`.
- Statement: on the one actual round-varying causal trajectory measure, the
  actual exploratory successor policy's expected regret tends to zero almost
  everywhere; on one common a.e. set this is joined with eventual all-state
  model optimism, the recommended-policy occupancy certificate, and realized-
  regret convergence.
- Route/APIs: outside one model-round event, consume coordinate confidence,
  transport the recommended policy to `source.successorPolicyAt` with the
  explicit exploration charge, evaluate the occupancy-radius sum, and bound
  by the causal planning rate; use model-only first Borel-Cantelli,
  `expectedRegret_nonneg`, `Metric.tendsto_atTop`, and the vanishing planning
  rate; intersect with the compiled realized a.e. terminal.
- Contracts: unchanged finite nonempty Standard Borel State/Action,
  probability initial law, positive horizon/base floor/reward proxy, bounded
  stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
  full-exploration path support. No round independence or extra return event is
  needed for the expected-regret limit.
- Evidence/status: exact local retrieval no-hit; compiled coordinate-
  confidence, exploratory-policy transport, occupancy, causal-rate, and
  Borel-Cantelli parents; RL/UCB-VI cards are placement only and
  `WEAPON-UCB-OPTIMISM` is inspiration only; `leanCompiled`; five declarations;
  direct/root/Tests Bool/Bool pointwise and joint-limit canaries.
- Failure policy: preserve the one dependent source, actual samples,
  `n -> n+1`, scheduled budgets, actual/recommended policy distinction, initial
  exclusion, global realized-regret centering, and a.e. burn-in. Its finite-
  selector consumer now proves coordinate measurability and same-source
  in-measure convergence. The remaining boundary is behavior `MemLp 1`/`L1`;
  no expected-value/every-trajectory/anytime/reachability/minimax/optimal-rate/
  complete-UCB-VI claim.

## Compiled: Heterogeneous Natural Causal Almost-Sure Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-ALMOST-SURE-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`.
- Statement: on the one actual round-varying causal trajectory measure, every
  regret coordinate is measurable and realized successor-average regret tends
  to zero for almost every trajectory; on the same a.e. full set, every
  sufficiently late actual sampled empirical model is globally optimistic for
  all states and satisfies its recommended-policy occupancy-radius certificate.
- Route/APIs: prove `exp (-sqrt n)` summable by Mathlib Schloemilch
  condensation; use positive episode batches to lower-bound actual successor
  mass by the round index; convert model and return bounds to finite ENNReal
  measure tsums; apply first Borel-Cantelli `ae_eventually_notMem` twice; feed
  the resulting trajectory-dependent burn-in to the compiled absolute-regret
  terminal and its vanishing deterministic envelope; intersect the resulting
  a.e. certificate with the model-good filter and consume the compiled
  one-coordinate confidence theorem without changing trajectory measures.
- Contracts: unchanged finite nonempty Standard Borel State/Action,
  probability initial law, positive horizon/base floor/reward proxy, bounded
  stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
  full-exploration path support. No round independence is assumed.
- Evidence/status: exact local retrieval no-hit; direct Mathlib
  `OuterMeasure.BorelCantelli`, Schloemilch, exponential-summability, ENNReal
  tsum, filter APIs, and the local coordinate-confidence consumer plus compiled
  causal parents; `leanCompiled`; 14 declarations; direct/root/Tests Bool/Bool
  canaries, including the joint terminal and all-state optimism projection.
- Failure policy: preserve the one dependent source, actual samples,
  `n -> n+1`, `episodes (n+1)`, coordinate budgets, initial exclusion, global
  centering, actual mass, and the a.e. trajectory-dependent finite burn-in.
  This is not an all-trajectory pathwise theorem, an anytime finite-sample
  envelope, minimax/reachability control, or complete UCB-VI. The behavior-
  expected consumer above now compiles the pointwise actual successor-policy
  rate and its a.e. limit. Coordinate measurability of that process is the next
  narrow boundary.

## Compiled: Heterogeneous Natural Causal L1 Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-L1-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`.
- Statement: on the one actual round-varying causal trajectory measure,
  expected absolute realized successor-average regret tends to zero; every
  coordinate is `MemLp 1`, exact exponent-one `eLpNorm` is identified, and the
  named `Lp Real 1` process tends to zero.
- Route/APIs: bound weighted mean-policy regret by `2 * horizon`; integrate the
  direct same-measure cumulative-return sub-Gaussian MGF; divide the first
  moment by actual successor mass; combine fixed-burn-in planning, model-tail
  overflow, and normalized return terms; package with Mathlib `MemLp`,
  `eLpNorm`, `Lp`, and `TendstoInMeasure` APIs.
- Contracts: unchanged finite nonempty Standard Borel State/Action,
  probability initial law, positive horizon/base floor/reward proxy, bounded
  stored means, uniform mean-compatible selected-reward sub-Gaussianity, and
  full-exploration path support.
- Evidence/status: exact same-stream causal L1 retrieval no-hit; compiled
  causal in-probability/MGF/planning parents and Mathlib/ABRL integral,
  asymptotic, `MemLp`, `eLpNorm`, and `Lp` APIs; `leanCompiled`; 27
  declarations; direct/root/Tests Bool/Bool projections.
- Failure policy: preserve the one dependent source, actual samples,
  `n -> n+1`, `episodes (n+1)`, coordinate budgets, initial exclusion, global
  centering, actual mass, and explicit burn-in. No independent-window or
  uniform-integrability axiom is used. The almost-sure consumer above now
  supplies the separate summable-event/Borel-Cantelli route; no all-trajectory
  pathwise/anytime/minimax/reachability/UCB-VI claim follows.

## Compiled: Heterogeneous Natural Causal In-Probability Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-NATURAL-CAUSAL-IN-PROBABILITY-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`.
- Statement: on the one actual round-varying causal trajectory measure, the
  measurable realized successor-average regret process converges to zero in
  Mathlib `TendstoInMeasure`.
- Route/APIs: rewrite the local model delta as a p-series; use
  `ENNReal.tendsto_tsum_compl_atTop_zero` for the post-burn-in model-event
  union; dilute early `2 * horizon` expected regret by actual successor mass;
  use compiled coordinate planning rates after burn-in; choose
  `exp (-sqrt successorMass)` for the return share; prove its normalized radius
  vanishes; close the distance-event form of convergence in measure.
- Contracts: finite nonempty Standard Borel State/Action, probability initial
  law, positive horizon/base floor/reward proxy, bounded stored means, uniform
  mean-compatible selected-reward sub-Gaussianity, and full-exploration path
  support.
- Evidence/status: exact natural heterogeneous causal convergence retrieval
  no-hit; compiled causal model/return/explicit-rate parents; Mathlib p-series,
  ENNReal tail, finite-sum, kernel, integral, log/sqrt, sub-Gaussian, and
  asymptotic APIs; `leanCompiled`; 38 declarations; direct/root/Tests Bool/Bool
  finite-tail and final-process projections.
- Failure policy: preserve one dependent causal source, actual samples,
  `n -> n+1`, `episodes (n+1)`, coordinate budgets, initial exclusion, global
  centering, actual-mass normalization, and explicit burn-in. This theorem is
  only convergence in probability, but its same-measure `L1` consumer now
  compiles above using a direct absolute-moment MGF bound. No independent-window
  reuse or pathwise/a.s./anytime/minimax/reachability/UCB-VI claim.

## Compiled: Heterogeneous Causal Explicit Weighted Rate

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EXPLICIT-WEIGHTED-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: the actual `episodes (t+1)`-weighted planning envelope and the
  fixed-half globally centered return envelope both tend to zero; one named
  finite-prefix event keeps the exact failure budget, all sampled-model
  optimism, and realized successor-average regret below their sum.
- Route/APIs: prove positive-weight averaging with Mathlib
  `IsLittleO.sum_range`; insert the scheduled reward and transition rate
  bounds coordinatewise; rewrite successor mass as a range sum; identify the
  heterogeneous return proxy as mass times one-episode proxy; specialize the
  normalized sub-Gaussian radius at `delta=1/2`; consume the causal terminal.
- Contracts: finite nonempty Standard Borel State/Action, probability initial
  law, positive rounds/horizon/base floor/reward proxy, bounded means, uniform
  mean-compatible selected-reward sub-Gaussianity, and full-exploration path
  support. Generic weighted averaging needs strictly positive natural weights.
- Evidence/status: exact weighted-causal and weighted-Cesaro retrieval no-hit;
  compiled causal realized and schedule-rate parents; Mathlib finite-sum,
  order, log/sqrt, asymptotic and sub-Gaussian APIs; `leanCompiled`; 20
  declarations; direct/root/Tests Bool/Bool terminal and limit projections.
- Failure policy: preserve actual samples, `n -> n+1`, `episodes (n+1)`,
  coordinate budgets, initial exclusion, global centering, exact finite budget,
  and actual-mass normalization. The deterministic envelope vanishes, but the
  accumulated model failure budget does not. The natural causal route above
  now tolerates those early failures through burn-in; this parent alone has no
  convergence-in-probability/pathwise/a.s./anytime/minimax/reachability/UCB-VI
  conclusion.

## Compiled: Heterogeneous Causal Realized Successor Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: successor coordinate `n+1` uses the exploratory policy selected
  from the dependent prefix through `n`, contributes `episodes (n+1)` complete
  episodes, and is normalized by the actual finite successor episode mass.
  The terminal gives one measurable model/return event, its exact finite
  failure budget, every sampled model's optimism, and realized successor-average
  behavior regret below the weighted planning average plus the heterogeneous
  globally centered return radius.
- Route/APIs: prove the exact weighted identity `realized = expected -
  deviation`; expose the return bad event and generic expected-to-realized
  transport; identify each successor exploratory policy; apply sampled-model
  optimism/recommended-regret and the exploratory behavior charge; sum with
  `Finset`; union the causal model and return events.
- Contracts: finite measurable nonempty State/Action with equality/singletons,
  probability initial law, Standard Borel State/Action, positive rounds,
  horizon, base visit floor, and reward proxy, bounded stored means by one,
  uniform mean-compatible selected-reward sub-Gaussianity, and full-exploration
  path support.
- Evidence/status: exact route no-hit; compiled causal model-confidence,
  causal return-concentration, and sampled cumulative exploratory-behavior
  parents; Mathlib finite-sum, measure-integral, kernel, sub-Gaussian, and order
  cards; `leanCompiled`; 26 declarations; direct/root/Tests Bool/Bool terminal.
- Failure policy: preserve actual batches, `n -> n+1` policy selection,
  coordinate episode weights/budgets, successor-only initial exclusion, global
  centering, exact finite failure sum, and actual-mass normalization. The
  explicit heterogeneous weighted planning/return envelope now compiles; no inherited
  fixed-window rate, common-space, uniform-time, pathwise/a.s./anytime/minimax,
  reachability, or complete-UCB-VI claim.

## Compiled: Heterogeneous Causal Empirical-Model Confidence

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EMPIRICAL-MODEL-CONFIDENCE`.
- Statement: coordinate zero uses the initial exploratory policy and coordinate
  `n+1` uses the policy selected from the prefix through `n`. Their actual
  sampled count/reward model events have exact selected iid fiber bounds; the
  first `rounds` coordinates are bounded by the genuine finite sum of their
  coordinate-specific shares. Under the self-consistent schedule, every actual
  batch `0..rounds-1` yields optimism and recommended expected-regret.
- Route/APIs: pull initial/successor events back to the dependent trajectory;
  use the exact initial marginal and prefix/next `compProd`; integrate selected
  iid fiber bounds; apply the finite Fintype union bound; recover each
  generating-policy event outside the union; specialize fixed-policy
  self-consistent calibration coordinatewise.
- Contracts: finite measurable nonempty State/Action with equality/singletons,
  probability initial law, Standard Borel State/Action, positive selected-reward
  sub-Gaussian proxy, bounded means by one, positive horizon/base path floor,
  and exploratory path support. Generic shares are positive and at most one;
  no adaptive-round independence is assumed.
- Evidence/status: exact route no-hit; compiled causal source, fixed-window
  sampled confidence, and self-consistent fixed-policy calibration;
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`;
  `leanCompiled`; direct/root/Tests rounds-two application.
- Failure policy: preserve actual samples, coordinate-specific episodes,
  shares, exploration rates and budgets, `n -> n+1` generating-policy indexing,
  and the exact finite `ENNReal` sum. The prefix budget is not claimed to vanish
  with `rounds`. The downstream realized-successor route performs the event
  union and causal regret assembly; no old rates, independence, uniform-time,
  pathwise/a.s./anytime/minimax/reachability/UCB-VI claim.

## Compiled: Heterogeneous Causal Sampled-Return Concentration

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SAMPLED-RETURN-CONCENTRATION`.
- Statement: the dependent causal source has two `piLE`-adapted processes.
  The supporting process centers every sampled batch at its own sampled
  initial-state policy value. The regret-facing process is zero at coordinate
  zero and globally centers successor batches `1..rounds` by the initial-law
  expected selected-policy value. Both obey fixed-round two-sided delta tails;
  the latter uses `iidGlobalProxy(episodes t)` at every successor coordinate.
- Route/APIs: map exact batch fibers with `retainedInputKernel`; use dynamic
  `condDistrib`, trimmed `condExpKernel`, and conditional-MGF transport; prove
  dependent-prefix increment measurability; apply the strongly-adapted
  conditional sub-Gaussian finite-sum theorem.
- Contracts: finite measurable nonempty State/Action, equality/singletons,
  probability initial law, Standard Borel dependent prefixes/batches/trajectory
  generically and Standard Borel State/Action concretely, bounded stored means,
  uniform selected-reward sub-Gaussianity, positive rounds/horizon/reward proxy,
  and `delta` in `(0,1]`.
- Evidence/status: exact route no-hit; compiled causal-law and homogeneous
  adaptive-return parents; `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-FINSET-SUMS`; `leanCompiled`; direct/focused/Tests application canary.
- Failure policy: preserve actual samples, `episodes round`, `n -> n+1`,
  successor-only indexing, global initial-law centering, dependent `piLE`, and
  the heterogeneous global proxy including initial-state value fluctuation.
  The downstream realized-successor route now unions this event with causal
  sampled empirical-model confidence; no old rates,
  uniform-time/pathwise/a.s./anytime/minimax/UCB-VI claim.

## Compiled: Heterogeneous Actual-Sampled Causal Projective Law

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SOURCE-PROJECTIVE-LAW`.
- Statement: one dependent `Kernel.trajMeasure` carries batch size
  `episodes n` at coordinate `n`; the self-consistent actual-sampled source has
  its exact initial law, selected iid history fibers, successor `condDistrib`,
  prefix/next `compProd`, and projective finite marginals.
- Route/APIs: define dependent trajectory/prefix/source types; select the
  latest actual sampled batch measurably; use budget index `n` for its
  optimistic table and rate/batch-size index `n+1` for the next kernel; apply
  Mathlib dependent Ionescu-Tulcea and finite-restriction map identities.
- Contracts: finite measurable nonempty State/Action with equality and
  measurable singletons plus probability initial law; Standard Borel
  State/Action only for the regular conditional endpoint.
- Evidence/status: exact route no-hit; compiled sampled source/schedule;
  local `KernelTrajectoryPrefix` congruence; `MLIB-PROBABILITY-KERNEL`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`; `leanCompiled`;
  direct/root/Tests, dependent projection canary, review, and full gate.
- Failure policy: this is a new round-varying causal algorithm, not a common
  coupling of the old fixed-window laws. Actual rewards/latest-batch semantics
  and selected iid fibers are preserved, but old confidence/optimism/regret
  rates are not inherited. The return-concentration and empirical-model
  confidence consumers now compile; next union their events and assemble
  causal successor regret, with no
  pathwise/a.s./anytime/minimax/UCB-VI claim.

## Compiled: Actual-Sampled Common-Space In-Probability Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-COMMON-SPACE-IN-PROBABILITY-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY`.
- Statement: the actual-sampled scheduled window law has an absolute realized
  successor-average certificate; an independent `Measure.infinitePi` coupling
  has every scheduled law as an exact coordinate marginal, and its realized
  regret process tends to zero in Mathlib `TendstoInMeasure`.
- Route/APIs: rebuild the model-good expected bound, combine it with the
  two-sided globally centered return deviation, construct window source/law,
  use `Measure.infinitePi_map_eval` and `measurePreserving_eval_infinitePi`,
  then squeeze distance-event mass by the explicit regret/failure envelopes.
- Contracts: unchanged finite nonempty Standard Borel State/Action,
  probability initial law, positive horizon/base floor/proxy, uniform selected-
  reward sub-Gaussian law, bounded means, and full-exploration path floor.
- Evidence/status: exact route no-hit; compiled explicit-rate parent and
  stochastic common-space template; `MLIB-PROBABILITY-KERNEL`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-METRIC-TOPOLOGY`, `MLIB-ASYMPTOTICS`;
  `leanCompiled`; focused/root/Tests canaries and full gate.
- Failure policy: preserve actual rewards, successor indexing, initial
  exclusion, three shares, global centering, `episodes*rounds`, and absolute
  control. This is an exact-marginal independent product of complete windows,
  not one causal online run. A distinct heterogeneous causal source now
  compiles, but requires new concentration/regret transports; do not infer
  pathwise/a.s./anytime/minimax/UCB-VI.

## Compiled: Scheduled Actual-Sampled Explicit Realized Rate

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-EXPLICIT-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: for `scale=n+2`, the exact fixed-point transition budget is at
  most `12*card(State)*horizon/scale^2`; the three confidence shares equal
  `ofReal(3/scale)`. The named planning envelope adds the scale-squared reward
  and transition terms to the explicit exploration charge, and the full
  realized envelope adds the inverse-scale globally centered return radius.
  Both rate envelopes tend jointly to zero, and the actual-sampled terminal
  exposes these finite-window bounds while preserving all-round optimism.
- Route/APIs: compiled self-consistent schedule; reward and contraction
  envelopes; calibration `q<=1/2`; exact fixed-point budget; ordered division;
  `exploratoryBehaviorRegretCharge`; normalized global-return envelope;
  `ENNReal.ofReal_add`; `Tendsto` arithmetic.
- Contracts: unchanged from the parent terminal: finite nonempty measurable
  State/Action with equality/singletons; Standard Borel State/Action;
  probability initial law; positive horizon/base floor/reward proxy; uniform
  sub-Gaussian selected rewards; means bounded by one; full-exploration path
  floor. The rate consumer adds no probabilistic or regularity assumption.
- Evidence/status: exact explicit-rate memory no-hit; compiled schedule and
  realized parents; `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, and
  `MLIB-ASYMPTOTICS`; `leanCompiled`; focused/root/Tests canaries and full gate.
  `SCN-RL-MDP` and the UCB-VI paper card are placement only;
  `WEAPON-UCB-OPTIMISM` is inspiration only.
- Failure policy: preserve actual samples, successor indexing, initial
  exclusion, three shares, global centering, and `episodes*rounds`. Constants
  are sufficient and loose. This is not a natural shared stream, reachability,
  almost-sure/anytime/minimax control, or complete UCB-VI; next cross the
  natural shared-causal-stream boundary or isolate a genuinely tighter rate.

## Compiled: Scheduled Actual-Sampled Self-Consistent Realized Consistency

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-CONSISTENCY`.
- Statement: with `scale=n+2`, `explorationRate=delta=1/scale`,
  `rounds=scale^(horizon+4)`, the scaled path-support visit floor, and episodes
  one above the maximum calibration/count-shrink/reward-shrink threshold,
  `rewardBudget<scale^-2`, `q<4*card(State)*horizon/scale^2`, and the exact
  self-consistent transition budget tend to zero. The full realized
  successor-average bound and three-share failure budget tend jointly to zero;
  every finite window retains actual-sampled optimism and realized control.
- Route/APIs: self-consistent actual-sampled realized parent; decaying
  exploration rate/round/floor/delta schedules; path calibration threshold;
  explicit sub-Gaussian radius squares; `Nat.ceil`; denominator algebra;
  `squeeze_zero`; `Tendsto` arithmetic; normalized global-return envelope;
  Standard Borel finite-batch instances.
- Contracts: finite nonempty measurable State/Action with equality/singletons;
  Standard Borel State/Action; probability initial law; positive horizon,
  base visit floor, and reward variance proxy; one mean-compatible uniform
  sub-Gaussian selected-reward law; true means bounded by one; exploratory
  path-support floor at full exploration. Schedule positivity, margins,
  `q<1`, model/return proxy positivity, and batch regularity are discharged.
- Evidence/status: exact schedule-route memory no-hit; compiled self-consistent,
  decaying-exploration, and global-return parents; Mathlib finite-sum, measure,
  kernel, conditional-expectation, sub-Gaussian, topology-limit and ordered-
  field APIs; `leanCompiled`; focused build and external Unit/Bool canaries.
- Failure policy: preserve actual samples, `n -> n+1`, initial exclusion,
  three shares, global centering, and `episodes*rounds`. This is a changing
  finite-window family, not a common process, state-reachability theorem,
  almost-sure/anytime/minimax control, or complete UCB-VI. Next isolate a
  natural shared-stream or sharper algorithm-specific-rate leaf.

## Compiled: Actual-Sampled Self-Consistent-Budget Realized Successor Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: for `q=card(State)*uniformFloorTransitionCoordinateRadius*horizon<1`,
  `T=q*(rewardBound+2*rewardBudget)/(1-q)` satisfies
  `q*(rewardBound+2*rewardBudget+T)=T`. One three-share event controls every
  actual sampled plan's optimism and realized successor-average regret by
  `2*horizon*(rewardBudget+T)+explorationCharge` plus the global-return radius
  over `episodes*rounds`.
- Route/APIs: arbitrary-budget iid all-coordinate confidence; self-consistent
  fixed point; finite transition sum; exploratory path-support expected-count
  floor; adaptive selected-policy batch-event transport; cumulative sampled
  exploratory-behavior regret; exact occupancy evaluator; generic two-budget
  expected-to-realized transport; `ENNReal.ofReal_add` and positive division.
- Contracts: finite measurable nonempty Standard Borel State/Action with
  equality/singletons; probability initial law; positive rounds/episodes/model
  and return proxies; mean-compatible uniform sub-Gaussian reward source;
  three valid shares; valid exploration; bounded true means; path support and
  visit floor; strict local count margin and strict `q<1`; composite stochastic
  batch/trajectory regularity. Sampled rewards may be unbounded.
- Evidence/status: exact route/declaration no-hits; compiled fixed-policy,
  adaptive confidence/cumulative, occupancy, and realized-transport parents;
  Mathlib finite-sum, measure, kernel, conditional-expectation, sub-Gaussian,
  integral and ordered-field APIs; `leanCompiled`; focused and external canary
  builds.
- Failure policy: preserve actual samples, `n -> n+1`, initial exclusion,
  global centering, all three shares and `episodes*rounds`. The explicit
  vanishing schedule now compiles above; retain this row as its finite-window
  parent. No state-reachability, anytime/minimax, or complete-UCB-VI inference.

## Compiled: Actual-Sampled Explicit-Budget Realized Successor Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-EXPLICIT-BUDGET-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: the actual sampled occupancy-radius sum is exactly
  `rounds*horizon*2*(rewardBudget+transitionBudget)`; with the calibrated
  transition budget, the prior three-share realized successor terminal has
  trajectory-independent planning average
  `2*horizon*(rewardBound+3*rewardBudget)+explorationCharge` plus the unchanged
  global-return radius over `episodes*rounds`.
- Route/APIs: fixed-radius stochastic empirical model; `FiniteBatchModel.plan`;
  `selectedRadiusRemaining`; `MarkovPolicy.occupancySumRemaining_const`;
  finite constant sum; `uniformFloorStochasticTransitionBudget`; positive
  division; prior actual-sampled realized terminal.
- Contracts: the algebraic equalities use finite measurable State/Action,
  equality/singletons, `Nonempty Action`, and a probability initial law;
  unnecessary `Nonempty State` is omitted. The terminal adds nothing to the
  parent's finite Standard Borel, sub-Gaussian, positivity/share, exploration,
  bounded-mean, path-support, strict-margin, half-contraction, and composite
  stochastic regularity contracts. Sampled rewards remain unbounded.
- Evidence/status: exact route no-hit; compiled actual-sampled realized parent,
  constant occupancy evaluator and fixed stochastic radii; Mathlib finite-sum,
  measure, kernel, conditional-expectation, sub-Gaussian, integral and ordered-
  field APIs; `leanCompiled`; focused and external Unit/Bool canary builds.
- Failure policy: preserve actual samples, `n -> n+1`, initial exclusion,
  global centering, all three shares and `episodes*rounds`. The coarse
  `transitionBudget=rewardBound+2*rewardBudget` leaves an irreducible
  `2*horizon*rewardBound`; fixed-budget schedule tuning cannot prove vanishing
  regret. The compiled self-consistent route above is the downstream repair.

## Compiled: Actual-Sampled Realized Successor Average Behavior Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET`.
- Statement: one three-share event controls every actual sampled plan's
  optimism and the realized average regret of source successor batches
  `1..rounds`; the bound is the sampled occupancy-radius average plus the
  exploration charge and a globally centered successor return radius divided
  by `episodes * rounds`.
- Route/APIs: sampled successor exploratory expected-regret parent; concrete
  finite-table `GlobalReturnMeasurability`; `successorGlobalReturnDeviationBadEvent`;
  successor return tail and exact realized decomposition; `measure_union_le`;
  positive division.
- Contracts: finite measurable nonempty Standard Borel State/Action,
  probability initial law, positive rounds/episodes/reward variance proxy and
  cumulative return proxy, one mean-compatible uniform sub-Gaussian reward
  law, separate valid count/reward/return deltas, valid exploration, bounded
  true means, path support, strict count margin, and half-contraction. Sampled
  rewards need not be bounded.
- Evidence/status: exact route search no-hit; compiled sampled successor
  expected-regret and successor return-tail/decomposition parents; Mathlib
  finite-sum, measure, kernel, conditional-expectation, sub-Gaussian, integral,
  and order cards; `leanCompiled`; focused build and external canaries.
- Failure policy: preserve sampled-coordinate `n` to successor batch `n+1`,
  exclude the initial batch, retain actual samples, all three shares, global
  centering including the initial-state value fluctuation, and the
  `episodes * rounds` denominator. The explicit-budget consumer above now
  closes the occupancy term, but no vanishing, anytime/minimax, or complete-
  UCB-VI rate follows from this parent alone.

## Compiled: Actual-Sampled Successor Exploratory Behavior Expected Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-SUCCESSOR-EXPLORATORY-BEHAVIOR-EXPECTED-REGRET`.
- Statement: sampled coordinate `n` selects the concrete source successor
  exploratory policy for coordinate `n + 1`; on the unchanged two-share event,
  their cumulative expected regret is at most the actual-sampled occupancy-
  radius sum plus `rounds` times the explicit exploration charge.
- Route/APIs: sampled optimistic table-to-policy identity;
  `successorPolicy`; `Preorder.frestrictLe`; deterministic exploratory-policy
  regret comparison; cumulative recommendation parent; `Finset.sum_le_sum`
  and `Finset.sum_add_distrib`.
- Contracts: the terminal inherits the exact parent finite Standard Borel,
  probability, sub-Gaussian, positivity/share, exploration, bounded-mean,
  path-support, strict-margin, and half-contraction contracts. The algebraic
  charge transport only uses the reward bound and valid exploration rate.
- Evidence/status: exact route search no-hit; compiled actual-sampled
  recommendation and deterministic exploration-charge parents; Mathlib
  finite-sum, measure, kernel, sub-Gaussian, and order cards; `leanCompiled`;
  focused and external-canary builds.
- Failure policy: preserve `n -> n+1` successor indexing, exclude the initial
  policy, retain actual samples and separate confidence shares, and do not
  identify this parent alone with realized sampled return. The three-share
  realized consumer now compiles above; explicit-rate, anytime/minimax, and
  complete-UCB-VI claims remain downstream.

## Compiled: Actual-Sampled Cumulative Recommended Expected Regret

- Leaf: `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-CUMULATIVE-RECOMMENDED-EXPECTED-REGRET`.
- Statement: on the same measurable two-share finite-round event, every actual
  sampled-reward empirical plan is optimistic and the finite sum of its
  recommended policy's expected regret is at most the finite sum of its
  occupancy selected-radius certificate.
- Route/APIs: sampled stochastic trajectory coordinate to `EpisodeBatch`;
  all-coordinate empirical model and plan; `MarkovPolicy.expectedRegret`;
  `occupancySumRemaining`; `selectedRadiusRemaining`; `Finset.sum_le_sum`;
  parent confidence/path-support terminal.
- Contracts: exactly the parent finite Standard Borel, probability,
  sub-Gaussian, positivity/share, exploration, bounded-mean, path-support,
  strict-margin, and half-contraction contracts. The finite-sum helper itself
  only assumes the supplied roundwise certificates.
- Evidence/status: exact route search no-hit; compiled sampled confidence and
  deterministic cumulative-recommendation patterns; Mathlib finite-sum,
  measure, kernel, sub-Gaussian, and order cards; `leanCompiled`; focused and
  external-canary builds.
- Failure policy: preserve actual sampled rewards, one plan per batch,
  generating-policy confidence indexing, separate shares, and recommendation-
  level semantics. The successor exploratory-policy charge now compiles above;
  sampled-return/realized, explicit-rate, anytime/minimax, and complete-UCB-VI
  claims remain downstream.

The compiled sampled-reward confidence route remains the probabilistic parent:
its measurable event, exact selected-policy iid fibers, and pointwise
certificates are consumed here rather than replaced by a known-mean projection.

## Latest Finite-Horizon RL Route

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EXPLICIT-WEIGHTED-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET` | actual `episodes (t+1)`-weighted planning and fixed-half return envelopes tend to zero; one named fixed-prefix event keeps exact failure, all optimism, and realized successor-average regret below their sum | causal realized terminal; schedule reward/transition rates; successor mass/proxy; sub-Gaussian radius; `IsLittleO.sum_range`; finite sums/order/log-sqrt/asymptotics | positive-weight average lemma -> coordinate comparison -> actual-mass range sum -> exact return-proxy identity -> fixed-half sqrt limit -> consume causal terminal | finite nonempty Standard Borel State/Action, probability, positive rounds/horizon/base floor/proxy, bounded means, uniform selected-reward sub-Gaussian law, path support; positive Nat weights | exact weighted-causal/Cesaro no-hit; compiled causal/rate parents; Mathlib APIs and cards; theorem cards/weapons evidence only | `leanCompiled`; 20 declarations; direct/root/Tests limit/event/failure/optimism/regret canaries; review/full gate before handoff | preserve samples, `n -> n+1`, weights/budgets, initial exclusion, centering, exact finite budget and actual mass; deterministic envelope vanishes but cumulative model failure does not; next tolerate early failures, no causal convergence/common-space/pathwise/a.s./anytime/minimax/reachability/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET` | actual successor batches are weighted by `episodes (t+1)` and normalized by their finite sum; one model/return event yields all sampled-model optimism and realized successor-average behavior-regret control | causal model-confidence/return terminals; exact global-return sum; sampled occupancy identity; exploratory charge; finite sums/unions; sub-Gaussian radius | exact weighted regret identity -> generic return transport -> selected-policy expected bound -> coordinate planning sum -> model/return event union -> concrete terminal | finite nonempty Standard Borel State/Action, probability, positive rounds/horizon/base floor/proxy, bounded means, uniform selected-reward sub-Gaussian law, path support | exact no-hit; three compiled parents; sum/integral/kernel/sub-Gaussian/order cards; theorem cards/weapons evidence only | `leanCompiled`; 26 declarations; direct/root/Tests full Bool/Bool application; review/full gate before handoff | preserve samples, `n -> n+1`, coordinate weights/budgets, initial exclusion, global centering, finite budget and actual-mass denominator; consumed by explicit weighted rate, no old rates/common-space/uniform-time/pathwise/a.s./anytime/minimax/reachability/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-EMPIRICAL-MODEL-CONFIDENCE` | exact selected-policy iid fibers bound coordinate-varying actual-sampled model events; their finite ENNReal sum controls the prefix, and self-consistent actual batches yield optimism/recommended-regret certificates | causal initial/`compProd`; sampled model bad event and iid tail; measurable selected exploratory event; finite union; fixed-policy self-consistent calibration | pull back coordinate events -> integrate exact fibers -> sum nonuniform shares -> recover generating policy outside union -> specialize every scheduled coordinate | finite nonempty Standard Borel spaces, probability, positive uniform reward proxy, bounded means, path support, positive horizon/base floor; coordinate shares positive and at most one; no round independence | exact no-hit; compiled causal/sampled-confidence/self-consistent parents; kernel/sub-Gaussian/integral/finite-sum/order cards; theorem cards/weapons evidence only | `leanCompiled`; 23 declarations; direct/root/Tests rounds-two full application; review/full gate before handoff | preserve actual samples, per-coordinate episodes/shares/rates/budgets, `n -> n+1`, finite failure sum; consumed by the realized-successor route, no vanishing-prefix/old-rate/independence/uniform-time/pathwise/a.s./anytime/minimax/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SAMPLED-RETURN-CONCENTRATION` | supporting own-initial-state deviations and regret-facing successor-only globally centered deviations are `piLE` adapted with exact selected conditional MGFs; heterogeneous proxy sums give fixed-round two-sided tails | causal `compProd`; retained-input kernel; dynamic `condDistrib`; trimmed `condExpKernel`; iid sampled/global-return MGFs; conditional sub-Gaussian sum | map exact selected iid fibers -> conditional-law transport -> coordinate MGF at `episodes round` -> dependent adaptedness -> zero coordinate plus successors -> sum global proxies -> self-consistent wrapper | generic Standard Borel/Nonempty dependent prefixes, batches and trajectory; concrete finite Standard Borel spaces, probability, bounded means, uniform selected-reward sub-Gaussian law, positive rounds/horizon/proxy, valid delta | exact no-hit; compiled causal/homogeneous-return parents; sub-Gaussian/conditional-expectation/kernel/finite-sum cards; theorem cards/weapons evidence only | `leanCompiled`; 41 declarations; direct/focused/root/Tests full applications; clean own linter; review/full gate before handoff | preserve actual samples, `episodes round`, `n -> n+1`, successor-only initial exclusion, global initial-law centering, `piLE`, heterogeneous global proxy; consumed by realized-successor event union, no old rates/uniform-time/pathwise/a.s./anytime/minimax/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-HETEROGENEOUS-CAUSAL-SOURCE-PROJECTIVE-LAW` | one dependent Ionescu-Tulcea source with coordinate batch size `episodes n`; exact initial/selected-iid/condDistrib/compProd laws and projective finite marginals | sampled optimistic-table measurability; exploratory iid kernel/comap; dependent `Kernel.trajMeasure`; conditional distribution; prefix restriction/map APIs | define dependent source -> latest-batch table at budget index n -> next kernel at schedule index n+1 -> instantiate self-consistent schedules -> expose every causal and projective law | finite measurable nonempty spaces with equality/singletons and probability; Standard Borel State/Action only for condDistrib terminal | exact no-hit; sampled source/schedule and local prefix congruence; probability-kernel/conditional-expectation/measure cards; theorem cards/weapons only evidence | `leanCompiled`; 15 declarations; direct/root/Tests/full gate; concrete 2-to-0 projective canary; terminal root-visible; own linter clean; independent review | new round-varying algorithm, not old window marginals; preserve actual rewards/latest batch/selected iid law; next heterogeneous return/model confidence and regret transport, no old rates/pathwise/a.s./anytime/minimax/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-COMMON-SPACE-IN-PROBABILITY-REALIZED-SUCCESSOR-AVERAGE-CONSISTENCY` | one independent product coupling has every actual-sampled self-consistent scheduled trajectory law as its exact marginal, and realized successor-average regret tends to zero in `TendstoInMeasure` | explicit-rate parent; absolute realized adapter; window source/law; `Measure.infinitePi`; eval map/measure-preserving APIs; convergence-in-measure distance form | recover expected bound on model-good event -> combine with two-sided return deviation -> pull union through eval -> squeeze each distance event by vanishing absolute and failure envelopes | unchanged finite nonempty Standard Borel/probability/positive proxy/sub-Gaussian selected-reward/bounded-mean/full-exploration path-floor contracts | exact no-hit; compiled sampled explicit-rate and stochastic common-space parents; probability-kernel/measure/topology/asymptotic cards; theorem cards/weapons only evidence | `leanCompiled`; 12 indexed declarations; focused/root/Tests/full gate; exact-marginal canary; finite absolute and final terminals root-visible; own linter clean; independent review | preserve actual samples, successor indexing, initial exclusion, three shares, global centering and normalization; independent complete-window product only; distinct causal law now compiles but does not inherit rates; next heterogeneous concentration/regret, no pathwise/a.s./anytime/minimax/UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-SAMPLED-EMPIRICAL-OPTIMISTIC-SELF-CONSISTENT-SCHEDULED-EXPLICIT-RATE-REALIZED-SUCCESSOR-AVERAGE-BEHAVIOR-REGRET` | with `scale=n+2`, exact transition budget `<=12*|S|*H/scale^2`, failure budget `=ofReal(3/scale)`, and a named explicit planning-plus-return realized envelope tending to zero; the pointwise actual-sampled terminal exposes these bounds with all-round optimism | compiled self-consistent schedule; reward/contraction/half-calibration bounds; exact fixed point; exploration charge; normalized return envelope; `ENNReal.ofReal_add`; ordered field and `Tendsto` APIs | use `B<=1/4` and `q<=1/2` to prove `q*(1+2B)/(1-q)<=3q`; insert the compiled `q` envelope; lift through planning and return bounds; combine three shares; reuse the unchanged source terminal | exactly the parent finite nonempty Standard Borel/probability/sub-Gaussian/bounded-mean/path-floor contracts; no new law or regularity assumption | exact route no-hit; compiled schedule/realized parents; `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS`; RL/UCB-VI placement and optimism weapon inspiration only | `leanCompiled`; 11 indexed declarations; focused/root/Tests/full gate; concrete transition/joint-limit canaries; terminal root-visible and typechecked; own linter clean; independent review | preserve samples, successor indexing, initial exclusion, shares, centering, and normalization; loose sufficient changing-window rate only, no shared stream/reachability/a.s./anytime/minimax/UCB-VI claim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EXPLORATORY-PATH-SUPPORT-EXPLICIT-CALIBRATION` | one common expected-count floor and scalar half-contraction construct explicit reward/transition budgets, all coordinate covers, the two-share stochastic empirical-model confidence event, optimism, and exploratory-policy recommended expected regret | stochastic iid all-coordinate parent; `ExploratoryPathUniformVisitFloor`; `uniformFloorTransitionCoordinateRadius`; expected-count transition radius; finite sums and ordered division | divide the simultaneous reward-sum radius by `episodes*visitFloor-countRadius`; enlarge every coordinate denominator to the common floor; set transition budget to `rewardBound+2*rewardBudget`; use the half-contraction to cover the doubled stochastic envelope; derive the exploratory policy's count floor from path support; invoke the parent terminal | finite measurable nonempty Standard Borel State/Action with equality/singletons; probability initial law; deterministic table, exploratory support/rate; mean-compatible uniform sub-Gaussian reward source; positive episodes/proxy; two valid shares; mean-reward bound; common floor with strict scalar margin; half-contraction; no sampled-reward bound | exact compiled stochastic-confidence and path-support-calibration parents; sub-Gaussian/independence/kernel/integral/finite-sum/order cards; RL/UCB-VI placement only; optimism/tail weapons inspiration only | `leanCompiled`; focused/root/Tests/full gate; seven declarations; horizon-two 4194304-episode path-support canary with symmetric +/-1 rewards; clean placeholders; four baseline-only axiom audits; review no P0-P2 and P3 regularity leak repaired; indexes validated | preserve strict denominator, separate shares, explicit budgets and fixed-policy iid/path-support semantics; sufficient calibration only; next history-selected stochastic transport, no adaptive/cumulative/realized/anytime/minimax or complete UCB-VI claim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-ALL-COORDINATE-EMPIRICAL-MODEL-CONFIDENCE` | fixed-policy iid complete stochastic trajectories generate an actual sampled-reward empirical model; one measurable count/reward union has mass at most `ofReal countDelta + ofReal rewardDelta`; outside it a full `FiniteBatchModel.Confidence` yields optimism and recommended-policy one-episode expected regret | stochastic trajectory/IID reward law; reward erasure/count transport; simultaneous count event; empirical model/confidence; finite product independence and union bounds | prove masked coordinate reward MGFs, iid-sum tails, sampled-batch count equality and reward-sum identity; replace random denominators by strict expected-count margins; prove the stochastic value envelope; apply explicit reward/transition covers; union the two events and consume confidence | finite measurable nonempty State/Action with equality/singletons and Standard Borel; probability initial law; fixed policy; mean-compatible uniform sub-Gaussian reward source; positive episodes/total proxy; two valid deltas; reward mean bound; nonnegative budgets; all-coordinate margins and covers; no sampled-reward bound | exact compiled stochastic/count/confidence parents; sub-Gaussian/independence/kernel/integral/finite-sum/order cards; RL/UCB-VI placement only; theorem cards and weapons are not proofs | `leanCompiled`; focused/root/Tests and full gate; nondegenerate symmetric +/-1 Bool/Bool canary with proved 16384-episode margins/covers and sampled reward 1 versus mean 0; clean placeholders; baseline-only public axioms; review P2 repaired and no remaining P0-P2 | preserve sampled rewards, fixed-policy iid law, separate shares, positive denominator, and coarse `episodes*varianceProxy`; no count-adaptive radius, adaptive/cumulative/realized/anytime/minimax or complete-UCB-VI claim |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-BEHAVIOR-CONSISTENCY` | prove integrability and `MemLp 1` for every stochastic common-space regret coordinate; expected absolute value, exact exponent-one `eLpNorm`, and named `Lp` process tend to zero | compiled stochastic common-space route and cumulative conditional MGF; realized decomposition; Mathlib `HasSubgaussianMGF`, Bochner integral, `MemLp`, `eLpNorm`, and `Lp` APIs | bound only mean-policy regret by `2H`; evaluate the stochastic MGF at `1/sqrt(proxy)`; integrate the count-good/count-bad split; squeeze planner, one count share, and normalized first moment; identify `eLpNorm` and lift to `Lp` | finite measurable nonempty State/Action with equality/singletons and Standard Borel; probability initial law; positive horizon/base floor; support/uniform floor; bounded stored means; mean-compatible uniform selected-reward sub-Gaussian law; no sampled-reward bound | exact route no-hit; deterministic L1 assembly and stochastic common-space parents; exact Mathlib MGF/integral/Lp declarations; kernel/sub-Gaussian/asymptotic cards; RL placement only; weapons inspiration only | `leanCompiled`; reusable MGF first-moment adapter plus 30 route declarations; focused build; Bool/Bool five-surface canary; clean placeholders; four baseline-only axiom audits; independent review; index/full gate | preserve global centering, successor indexing, `episodes*rounds`, exact marginals, and unbounded samples; L1 pays one count share and integrates deviation; independent product only, no natural stream/pathwise/a.s./anytime, reward estimation, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY` | strengthen the stochastic finite-window endpoint to absolute realized regret; construct one dependent product of complete scheduled stochastic laws; prove exact marginals, measurable coordinates, and `TendstoInMeasure` to zero | regularity-closed stochastic cumulative endpoint; stochastic realized decomposition and sampled-return measurability; deterministic common-space template; Mathlib `Measure.infinitePi`, evaluation marginals/preimages, and convergence in measure | derive expected-regret nonnegativity and absolute control from the two-sided return event; define scheduled stochastic source/law; form the independent product; pull back finite bad events; bound every distance event by the vanishing bad-event budget | finite measurable nonempty State/Action with equality/singletons; Standard Borel State/Action; probability initial law; positive horizon/floor; path support; bounded mean rewards; mean-compatible uniform selected-reward sub-Gaussian law; inferred composite Borel instances | exact memory/local no-hit; deterministic common-space and stochastic cumulative declarations; kernel/sub-Gaussian/asymptotic cards; RL placement only; weapons inspiration only | `leanCompiled`; 17 declarations; fresh source/focused/root Tests; Bool/Bool exact marginal and terminal canaries; clean placeholders; five baseline-only axiom audits; independent review and full gate | preserve global centering, successor indexing, two shares, `episodes*rounds`, complete stochastic marginals, and absolute control; independent product only, not a natural shared stream; no pathwise/a.s./anytime, reward estimation, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REGULARITY-CLOSED-REALIZED-BEHAVIOR-CONSISTENCY` | infer Standard Borel structures for `EpisodeStep`, deterministic/stochastic finite batches, and their countable trajectories; expose finite/all-window stochastic consistency without composite witness arguments | `FiniteHorizonEpisodeBatchStandardBorel`; parent stochastic cumulative consistency; `EpisodeStep.toProdEquiv`; `upgradeStandardBorel`; measurable embedding/Borel/Polish transport; `StandardBorelSpace.pi_countable` | transport the product topology through the coordinate equivalence, identify the existing comap sigma algebra, synthesize finite products, use generic deterministic countable-product synthesis and add one stable stochastic trajectory instance, and reuse the unchanged parent terminals | measurable Standard Borel State/Action for `EpisodeStep`; stochastic trajectory additionally inherits finite State/Action; terminal retains finite/nonempty/equality/singletons, probability, positive horizon/floor, path support, bounded means, and uniform sub-Gaussian reward source; no composite Borel witnesses; sample spaces still change | exact route no-hit; local conditional-MGF consumer retrieval; exact Mathlib Standard Borel/embedding/Polish source; kernel/conditional-expectation cards; RL/UCB-VI placement and weapons inspiration only | `leanCompiled`; 5 declarations; focused/root/Tests; five inferred Bool/Bool instances and witness-free finite/all-window canaries; own linter clean; review/audits/index/full gate | preserve the parent laws, global centering, successor indexing, two shares, violation set, `episodes*rounds`, and changing-window semantics; no shared stream, in-probability/a.s./anytime, reward estimation, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-CUMULATIVE-DECAYING-EXPLORATION-REALIZED-BEHAVIOR-CONSISTENCY` | the stochastic cumulative projected-selector source maps exactly to the deterministic cumulative law; for every scheduled window its projected count and global-return events cover a named realized successor-average regret violation set, while the two-share failure budget and realized bound tend jointly to zero | compiled deterministic cumulative decaying expected-behavior terminal; compiled stochastic known-mean projection and global two-delta transport; cumulative selector/measurability; known-reward batch/prefix/trajectory maps; global proxy/radius; asymptotic APIs | construct the cumulative stochastic source; prove initial/fiber/joint/conditional/complete projection laws; pull back count/optimism/expected regret; derive finite-table global-return measurability; expose episode-linear proxy; normalize and squeeze the scheduled radius; cover the named violation set; pair all finite windows with scalar limits | finite measurable nonempty State/Action with equality/singletons; Standard Borel State/Action; the parent endpoint exposes deterministic/stochastic batch and trajectory Borel witnesses at each schedule index; the downstream regularity-closed wrapper infers them; probability initial law; positive horizon/base floor; exploratory path support; mean-compatible uniform-sub-Gaussian reward source; mean bound one; changing sample spaces | exact route no-hit; compiled deterministic and stochastic parents; `MLIB-PROBABILITY-KERNEL`; `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-MEASURE-INTEGRAL`; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; `MLIB-ASYMPTOTICS`; `SCN-RL-MDP`; UCB-VI placement and weapons inspiration only | `leanCompiled`; 33 declarations; focused/root/Tests; explicit Bool/Bool finite/all-window canaries; exact projection and joint failure/regret limits; own linter clean; review no P0/P1, P2/P3 repaired, downstream regularity closure compiled; five baseline-only axiom audits; index/full gate | preserve global centering, successor indexing, `episodes*rounds`, two confidence shares, and changing-window semantics; shared-stream coupling and reward estimation remain separate leaves; no in-probability/a.s./anytime, minimax, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EMPIRICAL-OPTIMISTIC-REALIZED-BEHAVIOR-REGRET` | the concrete projected-selector stochastic source satisfies projected all-coordinate confidence and optimism while its realized successor average behavior regret is bounded by the fixed-bonus planning term, explicit exploration charge, and globally centered stochastic return radius, with separate count and return confidence shares | compiled stochastic projection terminal; global stochastic expected-to-realized transport; exploratory-policy charge; fixed-bonus occupancy closed form; finite policy-table measurability; `measure_union_le` | add a two-delta generic transport; derive concrete global-return measurability; identify stochastic successor policies with projected exploratory tables; sum and average the exploration charge; close the occupancy term; add the return radius through the exact realized decomposition | finite measurable nonempty State/Action with equality/singletons; Standard Borel State/Action and deterministic/stochastic batch/trajectory endpoints; probability initial law; mean-compatible uniform-sub-Gaussian reward source; deterministic mean bound; positive rounds/episodes/total proxy; valid count/return deltas; exploration and calibration; dependent batch/trajectory Standard Borel instances remain caller-supplied | exact local no-hit; compiled projection, global realized-regret, exploratory-charge, and occupancy cards; Mathlib sub-Gaussian/kernel/integral/finite-sum/log cards; RL/UCB-VI placement only; weapons inspiration only | `leanCompiled`; 10 declarations; focused/root/Tests; automatic global-return regularity, positive proxy, actual Unit calibration, and a full-statement Bool/Bool two-action path-support terminal with symmetric non-degenerate rewards and distinct `1/2`,`1/4` shares; review no P0/P1, P2 repaired, P3 regularity boundary retained; audits/index/full gate | preserve global centering, successor coordinates, `episodes*rounds`, confidence shares, and exploration charge; next replace fixed bonus/charge by a scheduled or cumulative source; separately construct dependent Standard Borel instances before claiming a regularity-closed model; no initial batch, reward estimation, anytime/common-space, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-KNOWN-MEAN-EMPIRICAL-OPTIMISTIC-PROJECTION-CONFIDENCE` | a concrete stochastic exploratory empirical-transition optimistic source maps under complete known-reward projection to the deterministic adaptive source, so the projected count event has mass at most delta and implies projected optimism plus recommended-policy expected-regret control | adaptive stochastic/deterministic source structures; fixed-policy iid batch erasure; exploratory table kernels; `Measure.compProd`; condDistrib joint-law characterization; projective-limit trajectory identity; deterministic calibrated terminal | measurable batch/prefix/trajectory projections; table-indexed stochastic iid kernel and projected selector source; selected batch map; adaptive prefix/next compProd map; complete trajectory identity; deterministic event pullback | finite measurable nonempty State/Action with equality and measurable singletons; probability initial law; mean-compatible reward source; Standard Borel/nonempty deterministic batch at full-law endpoint; inherited exploration/calibration/mean-reward-bound/delta contracts; no sampled-reward bound or stochastic reward confidence | exact memory no-hit; exact fixed-policy map/deterministic terminal retrieval; Mathlib kernel/posterior/product/projective-limit cards; `SCN-RL-MDP`; textbook/UCB-VI placement; optimism weapon inspiration only | `leanCompiled`; 22 declarations; focused/root/Tests; symmetric non-degenerate reward source and selected-batch/full-trajectory/terminal canaries; clean placeholders; five baseline-only axiom audits; independent review; index/full gate | consumed by the concrete fixed-window stochastic realized-behavior route; preserve the exact process-law projection and do not infer reward estimation, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-ERASURE-IID-EPISODE-BATCH-LAW` | discarding sampled rewards maps each stochastic finite trajectory, initial-law trajectory, finite iid family, and known-reward episode-batch projection exactly to the existing deterministic laws | stochastic/deterministic trajectory kernels; `actionRewardStateKernel_map_dropReward`; compProd/map/comap; finite `Measure.pi`; deterministic/stochastic iid family laws; `episodeBatchOfTrajectories` | define measurable coordinate erasure; prove cons commutation; induct through the recursive trajectory kernels; lift through initial-state compProd and finite iid products; compose with the known-reward batch conversion | finite measurable State/Action; fixed MDP/policy/mean-compatible reward source; probability initial law for the full trajectory; finite episodes; final measurable `EpisodeBatch` projection additionally needs measurable singletons for State/Action; no Standard Borel, boundedness, MGF, confidence, or regret premise | exact memory no-hit; exact local head/kernel declarations; Mathlib kernel/product/measure cards; `SCN-RL-MDP`; textbook/UCB-VI placement only; weapons inspiration only | `leanCompiled`; 14 declarations; focused/root/Tests; two-action uniform policy with symmetric non-degenerate reward law; action/next-state retention; zero/positive horizon and zero/two-episode canaries; known-mean batch semantics; placeholder/baseline-axiom audits; review P2/P3 findings repaired; index/full gate | preserve actions and next states exactly; the projected batch reinstates known `mdp.reward`; next construct the adaptive source/count event; do not claim stochastic reward estimation, behavior regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT` | complete stochastic returns centered by the selected policy's global initial-law value have an iid batch MGF; successor coordinates 1..rounds satisfy an adaptive tail and exact realized/expected behavior-regret transport | compiled adaptive per-state-centered stochastic route; sampled return/value APIs; bounded-centered Hoeffding; iid product independence; generic same-space sub-Gaussian addition; retained-input dynamic conditional law; trimmed conditional expectation; `piLE` tail; deterministic realized-regret algebra | add the initial-state selected-policy value fluctuation to the existing per-state-centered return deviation; bound and sum it over independent complete episodes; combine with the honest squared-sum-of-square-roots proxy; require explicit dynamic measurability; transport successor conditional MGFs; prepend zero; prove tail, regret identity, and count/return union transport | finite measurable/Standard Borel State/Action; nonempty Action; probability initial law; mean-compatible reward source; selected-reward proxy; bounded deterministic means; Standard Borel batch/trajectory; explicit dynamic global-deviation measurability; positive total proxy/valid delta; no sampled-reward boundedness or cross-round/stage independence | exact no-hit; compiled stochastic concentration and deterministic realized-regret parents; exact local/Mathlib independence, sub-Gaussian, kernel, condDistrib, condExpKernel, filtration, integral, and finite-sum APIs; RL/UCB-VI placement only; tail weapon inspiration only | `leanCompiled`; 54 declarations; focused/root/Tests cover both MGF layers, constant/history-selected dynamic laws, successor tail, exact regret identity, and full event transport; placeholder/baseline-axiom audits; review no P0-P2/P3 history gap repaired; index/full gate | retain the initial-state value fluctuation and squared-sum-of-square-roots proxy; preserve successor coordinates and two confidence shares; next concrete stochastic selector/count event must add a nonzero two-action terminal test; schedules, anytime, minimax, and complete UCB-VI are downstream |
| `RL-FINITE-HORIZON-ADAPTIVE-STOCHASTIC-REWARD-EPISODE-BATCH-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL` | adaptive complete stochastic-reward episode batches have exact prefix-selected successor iid laws, initial/successor sampled-return/value-deviation MGFs, and a finite-round two-sided tail with a round-linear proxy | compiled stochastic iid total-return parent; adaptive episode batch law; `ConditionalExpectationReward`; retained-input kernel; `Kernel.trajMeasure`; `Filtration.piLE`; conditional sub-Gaussian sum tail | define adaptive stochastic source; retain prefix before dynamic deviation mapping; prove pair/dynamic condDistrib and trimmed condExpKernel laws; lift iid MGFs to the genuine initial and successor increments; prove strong adaptation and sum the proxies | finite measurable and Standard Borel State/Action; nonempty Action; Standard Borel batch and infinite trajectory at conditional-kernel endpoints; probability initial law; fixed mean-compatible reward source; common reward proxy; bounded deterministic means; explicit prefix×batch deviation measurability; positive total proxy/valid delta; no cross-round or within-episode independence | exact no-hit; compiled stochastic iid and deterministic adaptive parents; exact local/Mathlib kernel, conditional-distribution, conditional-expectation, filtration, and sub-Gaussian APIs; RL scenario evidence only; weapon inspiration only | `leanCompiled`; 33 declarations; focused/root/Tests; constant Bool/Unit law/MGF/proxy-22/tail canaries; history-sensitive piecewise source with unequal conditional iid batch laws; baseline-axiom audit; review P2/P3 repaired; index/full gate | preserve prefix-selected per-state value centering and variance-proxy addition; keep infinite-trajectory Standard Borel and dynamic measurability explicit; no global-mean substitution, radius addition, adaptive regret, uniform/anytime, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-IID-EPISODE-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL` | finite iid complete stochastic-reward trajectories yield independent sampled-return deviations whose sum has episode-linear MGF proxy and a fixed-sample two-sided delta tail | iid total-return module; initial-law parent; `Measure.pi`; eval marginal; `iIndepFun_pi`; Mathlib independent sub-Gaussian sum; local delta tail | construct product; prove exact marginals and coordinate independence; lift each MGF through eval; sum over episodes; consume delta tail | finite measurable/Standard Borel State/Action; nonempty Action; probability initial law; fixed policy/source; common reward proxy; bounded means; positive total proxy/valid delta for tail; no within-episode independence or adaptive policy | exact no-hit; compiled parent; local deterministic iid pattern; exact Mathlib product/independence/sum sources; RL scenario evidence only | `leanCompiled`; 12 declarations; focused/root/Tests; zero-episode empty-product/zero-sum/zero-proxy/MGF and two-episode marginal/independence/proxy-11/MGF/tail canaries; audits/review findings repaired/index/full gate | preserve full-episode iid and per-state value centering; next adaptive successor episode-law/conditional-MGF transport; do not replace proxy addition with per-episode radius addition; no adaptive/uniform/anytime, regret, optimism, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-INITIAL-LAW-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL` | under the full trajectory law, actual sampled cumulative return minus the recursive policy value at its sampled initial state has the common horizon MGF proxy and fixed-horizon two-sided tail | initial-law concentration module; compiled statewise sampled-return MGF; `Measure.integrable_compProd_iff`; `Measure.integral_compProd`; finite-state integrability; local delta tail | prove finite fiberwise MGF mixing by Fubini; integrate the common statewise bound over the probability initial law; instantiate the full generated trajectory kernel; consume the one-coordinate strongly-adapted tail | finite measurable/Standard Borel State/Action; nonempty Action; probability initial law; fixed MDP/policy/product source; common selected-reward proxy; bounded deterministic means; positive total proxy and valid delta for tail; no iid/adaptive/reachability premise | exact no-hit; compiled statewise parent; exact Mathlib compProd/sub-Gaussian sources; Mathlib sub-Gaussian/kernel/integral/finite-sum/log cards; RL scenario evidence only; weapons inspiration only | `leanCompiled`; 5 declarations; focused/root/Tests; Dirac and uniform Bool initial-law MGF/tail, distinct state values, and explicit per-state centering canaries; baseline axiom audit; independent review P2 repaired; index/full gate | preserve per-initial-state value centering and common fiber proxy; finite-iid episode sum compiles above and adaptive conditional transport is next; no global-mean substitution, state-mixture variance inference, uniform/anytime, regret, optimism, minimax, or complete UCB-VI overclaim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-SAMPLED-RETURN-VALUE-DEVIATION-SUBGAUSSIAN-TAIL` | actual sampled cumulative return minus recursive policy value splits pathwise into reward noise plus mean Bellman innovation and has generated MGF proxy `remaining*rewardVarianceProxy + meanBellmanInnovationVarianceProxy rewardBound remaining` with a fixed-horizon two-sided tail | total-return module; both concentration parents; retained action/state and centered reward kernels; exact map/compProd laws; `Kernel.HasSubgaussianMGF.add_compProd`; local delta tail | retain state/action/next state; conditionally sample centered reward; map exactly to the generated head; combine one-step MGFs; recurse on the sampled next state and combine with the tail; transport to the exact trace | finite measurable/Standard Borel State/Action; nonempty Action; fixed MDP/policy/mean-compatible product source; explicit state; common reward proxy; bounded deterministic mean rewards; positive total proxy and valid delta for tail; no cross-stage independence | exact no-hit; compiled reward-noise and Bellman parents; Mathlib sub-Gaussian/kernel/integral/finite-sum/log cards; RL/UCB-VI placement only; weapons inspiration only | `leanCompiled`; 33 declarations; focused/root/Tests; sampled-reward, randomized-action, and randomized-transition canaries; clean placeholders; baseline axiom audit; independent review; synchronized indexes/full gate | preserve exact sampled-return centering and conditional additive proxy; initial-law consumer compiles above and finite-iid is next; no marginal-MGF/radius addition, correlated source, uniform/anytime, regret, optimism, minimax, or complete UCB-VI overclaim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-MEAN-BELLMAN-INNOVATION-SUBGAUSSIAN-TAIL` | define cumulative `r(s,a)+V(s')-V_current(s)` innovation and prove generated-trajectory MGF proxy `sum k=1..remaining, (k*rewardBound)^2` plus a fixed-horizon two-sided delta tail | finite-horizon Bellman/value/action-state kernels; stochastic reward trajectory; bounded-centered Hoeffding; finite-state integral envelope; kernel fiber lift, retained-input product, map/compProd, `add_compProd`, existing delta tail | bound recursive values; identify action/transition mean return with `valueRemaining`; apply one-step Hoeffding; drop sampled reward exactly; recurse while retaining next state; prove duplicated-state agreement a.e.; add proxies and transport to generated trace | finite measurable and Standard Borel State/Action; nonempty Action; fixed MDP/policy/source and explicit state; NNReal bound on deterministic mean rewards; positive total proxy and `0 < delta <= 1` for tail; no sampled-reward bound or cross-stage independence | exact no-hit; compiled stochastic trajectory/reward-noise parents; Mathlib sub-Gaussian/kernel/integral/finite-sum/log cards; RL/UCB-VI placement only; tail/optimism weapons inspiration only | `leanCompiled`; 15 declarations; focused/root/Tests; randomized policy value `1/2`, nonzero innovation `3/2`, proxy four, MGF/tail canaries; uniform-transition masses `1/2` and trace innovations `+/-1/2`; review findings repaired; audits/index/full gate refreshed | preserve joint action/transition centering and squared-stage-envelope sum; its sampled-total-return consumer now compiles; no next-state-only substitution, `H^2` shortcut, standalone total-return inference, uniform/anytime, regret, optimism, minimax, or complete UCB-VI overclaim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-CUMULATIVE-DEVIATION-SUBGAUSSIAN-TAIL` | define the actual state/action-centered cumulative sampled reward deviation and prove generated-trajectory MGF proxy `remaining * varianceProxy` plus a fixed-horizon two-sided delta tail | stochastic trajectory recursion; compiled head MGF; generic fiber-to-kernel MGF bridges; `Kernel.id ×ₖ`, map, compProd, `Kernel.HasSubgaussianMGF.add_compProd`; existing delta tail | recurse on remaining horizon; retain sampled next state beside the tail; apply the induction MGF fiberwise; add head and tail proxies; prove the rebuilt trace map is exactly the original generated kernel; specialize one-coordinate strongly-adapted tail | finite measurable and Standard Borel State/Action; nonempty Action and explicit state; common selected-law NNReal proxy; positive total proxy and `0 < delta <= 1` for tail; conditionally independent reward/next-state product given state/action; no cross-stage independence, singleton, uniform-time, or regret premise | exact no-hit; compiled trajectory/head concentration parents; Mathlib sub-Gaussian/kernel/measure/martingale/log cards; RL/UCB-VI placement only; tail weapon inspiration only | `leanCompiled`; 7 declarations; focused/Tests; horizon-zero and nondegenerate two-step symmetric source, proxy-two and MGF; exact all-positive mass `1/4`, deviation two, positive-mass `delta = 3/4` tail; review findings resolved; audits/index/full gate refreshed | preserve actual state/action centering and linear proxy; its sampled-total-return consumer now compiles; no `H^2` shortcut, standalone total-return/value inference, regret, optimism, minimax, or complete UCB-VI overclaim |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-SUBGAUSSIAN-TAIL` | package a uniform selected-reward sub-Gaussian law, construct it from common interval support, and prove conditional/global MGF plus a one-step two-sided tail for the actual generated head reward deviation | compiled head `condExpKernel.map` selected-law route; mean-compatible reward identity; bounded Hoeffding wrapper; conditional-MGF transport; Mathlib trim/add bridge; strongly-adapted finite-sum tail | center `headReward` by `mdp.reward state headAction`; transport selected-law MGFs on `comap headAction`; add the conditional increment to zero on the trimmed conditioning space; specialize a constant full filtration to one coordinate | finite measurable and Standard Borel State/Action; nonempty Action, with State nonemptiness from explicit start state; common proxy or common a.s. interval; positive proxy and `0 < delta <= 1` for tail; no singleton, independence, multi-step, or regret premise | exact no-hit; compiled conditional-law parent; local conditional-MGF/adaptive-tail patterns; Mathlib sub-Gaussian/conditional-expectation/kernel/measure/log cards; RL/UCB-VI placement only; tail weapon inspiration only | `leanCompiled`; 10 declarations; focused/Tests; nondegenerate symmetric support, proxy-one, conditional/global MGF and `delta=1/2` tail canaries; clean placeholders; baseline axiom audit; independent review; synchronized indexes; full gate | preserve selected action law, exact centered deviation, and `comap headAction`; cumulative reward-noise concentration now compiles downstream; no randomized-mixture substitution, L1-to-sub-Gaussian inference, transition/Bellman tail, uniform/anytime, regret, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-CONDITIONAL-LAW` | identify the selected reward kernel as the first reward's conditional law given the sampled first action under both one-step and generated positive-horizon laws; expose the trimmed `condExpKernel.map` equality | stochastic head marginal parent; `RewardStepTrace.headAction/headReward`; `Kernel.sectR`; `Measure.ext_prod/fst_compProd`; `condDistrib_ae_eq_iff_measure_eq_compProd`; local Real condDistrib-to-condExpKernel bridge | freeze state; upgrade rectangle probabilities to the full action/reward compProd equality; derive the action marginal; characterize both conditional distributions from their joint laws; transport to the action-generated sigma-algebra | finite measurable State/Action and existing MDP/policy/source for joint and condDistrib; final condExpKernel adds Standard Borel State/Action and nonempty Action, deriving nonempty State from the explicit argument; no bound, second moment, sub-Gaussian, singleton, or deterministic-policy premise | exact no-hit; compiled head marginal and generic local condDistrib patterns; Mathlib kernel/posterior/conditional-expectation/measure cards; RL/UCB-VI placement only; no weapon dependency | `leanCompiled`; 10 declarations; focused/Tests; typed joint/condDistrib/condExpKernel plus generated action-dependent mass-one canaries; two reviews and baseline axiom audit | bounded/sub-Gaussian source, conditional/global MGF, and one-step tail compile downstream; next multi-step filtration transport; do not confuse selected and mixture laws or infer regret |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-HEAD-MARGINAL-FACTORIZATION` | at every positive recursive horizon identify the generated first action/reward/next-state law; expose action/reward and reward-only Markov marginals; prove exact joint rectangle and reward-event randomized-policy mixture formulas | stochastic trajectory parent; `RewardStepTrace` projections; `actionRewardStateKernel`; `Kernel.map_apply/map_comp_right/fst_compProd/compProd_apply_prod/prod_apply_prod`; `Measure.map_apply/map_map` | unfold one positive recursion; compose cons with head evaluation; discard the Markov tail; map away next state/action; rewrite measurable preimages as rectangles; expand action compProd and reward/transition product; simplify transition univ mass | finite measurable State/Action; MDP, Markov policy, mean-compatible Markov reward source; measurable action/reward events; no new bound/moment/singleton/Standard Borel/condDistrib/correlated law | exact no-hit; deterministic trajectory head-map and generic RewardKernel marginal patterns; Mathlib kernel/measure cards; RL/UCB-VI evidence only; tail weapon inspiration only | `leanCompiled`; 16 declarations; focused/Tests; exact randomized joint/reward masses, horizon-two stage-one mapping, and nondegenerate symmetric generated-law transport; placeholder/baseline axiom audits and independent review pass | next add explicit finite-history filtration/disintegration transport or separately contracted bounded/sub-Gaussian concentration; do not collapse randomized actions, replace samples by means, or claim condDistrib/concentration |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-TRAJECTORY-VALUE-IDENTITY` | generate finite `(action,reward,nextState)` traces; prove actual sampled cumulative reward `L1`; identify statewise expectation with stochastic backward value and the full expectation with stochastic and mean `valueAt 0` | stochastic Bellman parent; `RewardStepTrace`; action/reward/state and recursive kernels; kernel/measure `integrable_compProd_iff` and `integral_compProd`; `integrable_map_measure`; measurable kernel integrals | recursively follow sampled next states; combine selected reward and tail L1 through a measurable absolute-integral envelope and norm domination; transport through map; apply Fubini and the recursive value identity; integrate the initial law | finite measurable State/Action; parent MDP/policy; selected Real reward identity integrable with exact mean; probability initial law only for full endpoint; no boundedness, second moment, sub-Gaussian, Standard Borel, or correlated joint law | exact no-hit; compiled stochastic Bellman/deterministic trajectory parents; Mathlib kernel/integral/sum cards; RL/UCB-VI evidence only; weapons not dependencies | `leanCompiled`; 18 declarations; focused/root/Tests; explicit reward-one trace, generated symmetric first-reward mass `1/2`, symmetric statewise/full L1 and dual-value terminals, deterministic compatibility; audits and independent review refreshed | first-coordinate marginal factorization now compiles downstream; next prove finite-history conditional-law transport and add a separate bounded/sub-Gaussian concentration source; no correlated joint law, regret tail, optimism, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-STOCHASTIC-REWARD-KERNEL-BELLMAN-TRANSPORT` | package integrable Real reward laws with mean `mdp.reward`; prove sampled product-kernel action/policy Bellman and all backward values equal the existing mean model; embed deterministic rewards | `FiniteHorizonStochasticRewardBellman`; `RewardKernel.MarkovRewardKernel`; `Kernel.prod/prod_apply`; `Integrable.comp_fst/comp_snd`; `integral_prod`; finite-state integrability; policy/value recursion | form the conditionally independent reward/next-state kernel; prove product integrability; apply Fubini and split integrals; rewrite the reward mean and transition value; integrate pointwise under the policy; induct over a separate stochastic recursion; evaluate Dirac rewards | finite measurable State/Action; parent Markov transition/measurable mean reward; measurable continuation; selected reward identity integrable with exact stored mean; conditional independence through the product kernel; no bound/higher moment | exact no-hit; local reward-kernel and finite-horizon parents; Mathlib kernel/product/integral cards; RL/UCB-VI evidence only; weapons not dependencies | `leanCompiled`; 14 declarations; focused/root/Tests and deterministic plus non-degenerate symmetric-law canaries compile; baseline-only axiom audit; declaration/index/full-gate evidence refreshed | downstream reward-bearing trajectory/value identity compiles; arbitrary correlated joint laws, reusable reward-coordinate conditional laws, concentration, optimism, regret, minimax, and complete UCB-VI remain open |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-L1-REALIZED-CONSISTENCY` | prove exponent-one `MemLp`, exact expected-absolute `eLpNorm`, canonical difference-from-zero norm convergence, and convergence of a named `Lp Real 1` process | compiled expected-absolute parent; `memLp_one_iff_integrable`; `MemLp.eLpNorm_eq_integral_rpow_norm`; `ENNReal.continuous_ofReal`; `eLpNorm_congr_ae`; `MemLp.toLp`; `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; Lp-to-measure bridge | reuse coordinate integrability; simplify the exponent-one norm to the absolute integral; map the Real limit through `ofReal`; normalize subtraction by zero; package coordinates in `Lp`; transfer norm convergence to the Lp topology and recover convergence in measure | exactly the parent finite measurable nonempty state/action, probability, positive horizon/base floor, bounded deterministic reward, path support/full-exploration floor, and indexed Standard Borel witnesses; no new moment/dependence premise | exact common-space L1/eLpNorm/MemLp no-hit; compiled expected-absolute parent; Mathlib measure/integral/variance/asymptotic cards; RL/UCB-VI evidence only; tail weapon inspiration only | `leanCompiled`; 8 declarations; focused 3045 and external Tests canaries compile; MemLp/exact-eLpNorm/named-Lp/terminal consumers; declaration/axiom/index/full-gate audits refreshed | independent-coordinate finite-window product only; no natural nested stream, pathwise/a.s./anytime, stochastic rewards, minimax, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-EXPECTED-ABSOLUTE-REALIZED-CONSISTENCY` | prove every common-space realized-regret coordinate integrable, bound its expected absolute value explicitly, and prove those expectations tend to zero | compiled common-space parent; deterministic trajectory and optimal-return envelopes; generated-batch reward support; adaptive prefix/next compProd law; exact marginals; Bochner integral and ENNReal topology APIs | transport iid reward consistency through successor kernels; derive an a.e. `2*horizon` envelope; transport it to common coordinates; integrate the measurable good/bad split; apply the real failure budget; squeeze both bound terms to zero | finite measurable nonempty state/action with equality/singletons; probability initial law; positive horizon/base floor; deterministic absolute reward bound one; path support/full-exploration floor; indexed Standard Borel batch/trajectory witnesses; no cross-window dependence premise | exact expected-absolute/common-space/integrability no-hit; compiled common-space parent; Mathlib measure/integral/kernel/asymptotic cards; RL/UCB-VI scenario evidence only; tail weapon inspiration only | `leanCompiled`; 17 declarations; focused module and external Tests canaries compile; deterministic envelope, integrability, finite-bound, and terminal consumers; declaration/axiom/index/full-gate audits refreshed | independent-coordinate finite-window product only; no natural nested stream, pathwise/a.s./anytime, stochastic rewards, minimax, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-COMMON-SPACE-IN-PROBABILITY-CONSISTENCY` | construct a dependent infinite-product probability space with measurable realized-regret coordinates, every scheduled adaptive trajectory law as an exact marginal, and prove the process tends to zero in Mathlib `TendstoInMeasure` | compiled episodewise all-window route; finite-return-sum measurability; expected-regret nonnegativity; realized/expected/deviation identity; `Measure.infinitePi`; coordinate measure preservation; convergence-in-measure and ENNReal neighborhood APIs | prove finite-window realized regret measurable; compose with product evaluations; strengthen the good side to absolute regret; define scheduled source/law coordinates; take their infinite product; pull back the count/return event; use exact marginals; squeeze every positive-distance event by the vanishing doubled budget once the deterministic bound is below the tolerance | finite measurable nonempty state/action with equality/singletons; probability initial law; positive horizon/base floor; deterministic reward bound one; path support/full-exploration floor; indexed Standard Borel batch/trajectory witnesses; no cross-window dependence assumption | exact common-space memory no-hit; compiled episodewise local parent; Mathlib ProductMeasure/ConvergenceInMeasure source; sub-Gaussian/measure/kernel/asymptotics cards; UCB-VI/scenario evidence only; weapons not dependencies | `leanCompiled`; 17 registered declarations; focused 3043/root 3529/Tests 3531; probability-instance, marginal, process/measurability, absolute-window and full `TendstoInMeasure` canaries; clean placeholders/indexes; five baseline-only axiom audits; full gate with 17 CLI tests and one skip | independent-coordinate coupling, not a nested causal shared stream; no pathwise/a.s./anytime, stochastic rewards, minimax, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EPISODEWISE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY` | replace the coarse whole-batch proxy by `episodes*horizon^2`, transport it through the adaptive successor law, and expose sharper finite-window plus indexed decaying-exploration realized-consistency terminals | iid trajectory family/batch; complete episode row and episode return; Mathlib `iIndepFun`/product measure; bounded centered MGF; independent finite sum; compiled total-return `condExpKernel`, strong adaptation, regret decomposition, count event, and decaying parent | prove whole-episode coordinates independent under the mapped batch law; compose with episode return; center/bound each return; sum episode MGFs; identify centered total return; transport the sharp proxy through successor conditional MGF and cumulative tail; union events; normalize and package all windows | finite measurable nonempty state/action with equality/singletons; probability initial law; positive episodes/rounds/horizon/base floor as used; deterministic absolute reward bound one; fixed-window Standard Borel batch/trajectory; path support and indexed Borel witnesses at the concrete terminal | exact episode-return-subgaussian memory no-hit; local iid batch/episode-return/coarse realized/decaying routes; Mathlib sub-Gaussian/independence/product/integral/kernel/finite-sum APIs; UCB-VI/scenario evidence only; weapons not dependencies | `leanCompiled`; 33 declarations; focused/root/Tests; numeric sharp-proxy/radius, strict-violation, and indexed all-window canaries; clean placeholders; baseline axiom audit; declaration retrieval passes | episodes, not within-episode stages, are independent; preserve successor coordinates `1..rounds`, two confidence shares, and dependent sample spaces; do not claim stochastic rewards, common-space/pathwise/a.s./anytime convergence, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-REALIZED-BEHAVIOR-CONSISTENCY` | under the existing compatible schedule, the normalized successor-return radius is at most `2*horizon/(n+2)` and tends to zero; its sum with the expected behavior certificate and the doubled failure budget tend jointly to zero; every indexed finite window retains optimism and has a named realized violation set covered by the count/return union | exact batch/cumulative proxy casts; normalized radius and square identity; decaying schedule/expected bound; finite-window realized transport; Real log/sqrt/power; filters; `measure_mono` | identify proxies as `(episodes*H)^2` and `rounds*(episodes*H)^2`; cancel episodes by nonnegative square equality; bound `log(2q)<=2q` and compare powers; squeeze the radius; add expected and failure limits; include violations in the combined event; quantify indexed Borel windows | finite measurable nonempty state/action with equality/singletons; probability initial law; positive horizon/base floor; deterministic absolute reward bound one; full-exploration path support; indexed Standard Borel batch/trajectory witnesses; scalar identities use fewer contracts | exact memory no-hit; compiled realized and decaying-behavior parents; Mathlib sub-Gaussian/log/sqrt/asymptotic/order/measure/kernel/sum APIs; UCB-VI/textbook/scenario evidence only; weapons not dependencies | `leanCompiled`; 19 declarations; focused/root/Tests; exact-radius, nonzero-envelope, doubled-budget, strict-violation, and complete all-window canaries; clean placeholders; baseline axiom audit; independent review resolved; complete `letI` retrieval regression; indexes refreshed; full gate passes | dependent finite-window family only; preserve two delta shares, successor coordinates `1..rounds`, and the coarse whole-batch proxy; next common-space coupling or sharper episode concentration; no convergence in probability/pathwise/a.s., stochastic rewards, anytime, minimax, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-HIGH-PROBABILITY-REALIZED-BEHAVIOR-REGRET-TRANSPORT` | on one fixed adaptive batch-trajectory law, sum actual successor rewards at coordinates `1..rounds`, prove realized cumulative regret equals `episodes*expectedRegret-deviation`, and combine the return tail with the count event to retain optimism and bound realized average behavior regret | episode/batch total return; iid batch map/integral; selected-policy batch kernel; `trajectoryMeasure_condDistrib`; trimmed `condExpKernel`; conditional sub-Gaussian/strong adaptation; existing decaying expected-behavior terminal | identify generated returns and iid mean; apply whole-batch Hoeffding on `[-episodes*H,episodes*H]`; map each successor conditional law; apply the finite strongly-adapted sum tail; prove exact finite-sum regret algebra; union count/return events; align exploratory `policyAt` | finite measurable nonempty state/action with equality/singletons; probability initial law; positive episodes/rounds/horizon; deterministic absolute reward bound one; fixed-window Standard Borel batch/trajectory; path-support/base-floor contracts only for the concrete decaying consumer | exact local realized-regret no-hit; adaptive count martingale shape; local decaying behavior route; Mathlib sub-Gaussian/conditional-expectation/integral/kernel/finite-sum/order APIs; UCB-VI/scenario evidence only; weapons not dependencies | `leanCompiled`; 46 declarations; focused/root/Tests; explicit full-contract Unit terminal plus nonzero-return/coordinate-one canaries; baseline axiom audit; independent review findings resolved; indexes refreshed; full gate passes | finite windows only; two delta shares; coarse batch proxy, not sharp in episodes; normalized radius and dependent realized consistency now compile downstream; no common-space, anytime/pathwise/probability/a.s., stochastic rewards, minimax rate, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-DECAYING-EXPLORATION-HIGH-PROBABILITY-BEHAVIOR-CONSISTENCY` | from a full-exploration path floor, schedule `gamma_n=1/(n+2)`, `rounds_n=(n+2)^(H+4)`, `visitFloor_n=baseFloor*gamma_n^H`, and `delta_n=1/(n+2)`; prove the failure budget and average exploratory-behavior expected-regret certificate jointly tend to zero and expose the finite-window source event | exact action/state/visit path-floor scaling; parent scheduled recommendation endpoint; behavior expected-regret transport; Real sqrt/power and filter limits; `measure_mono` | induct on the selected path to extract `gamma^stage`; use antitonicity of powers on `[0,1]` for a horizon-uniform floor; prove `visitFloor_n*rounds_n=baseFloor*(n+2)^4`; rewrite the recommendation envelope; squeeze its sum with the behavior charge; reuse the parent bad event | finite measurable nonempty state/action with equality/singletons; probability; positive horizon/base floor; full-exploration uniform path floor; deterministic reward bound one; window-specific Standard Borel batch/trajectory spaces | exact memory no-hit; local scheduled/high-probability/behavior routes; `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS`, `MLIB-ORDER-ALGEBRA`, measure/kernel cards; UCB-VI/scenario route evidence only; weapons not dependencies | `leanCompiled`; 26 declarations; focused/root/Tests; Unit schedule/joint-limit/typed source and dependent `forall n` sample-space canaries; Bool/Bool horizon-two nondegenerate floor/mass canaries; placeholder/baseline axioms; independent review; indexes/full gate | this route remains expected-only; its finite-window realized transport and normalized-radius dependent realized consistency consumers now compile; common-process/pathwise/probability/a.s. claims remain open; no stochastic rewards, minimax rate, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-EXPLORATORY-BEHAVIOR-REGRET-TRANSPORT` | successor exploratory-policy expected regret is at most recommended-policy expected regret plus `explorationRate*rewardBound*horizon*(horizon+1)`; lift this to cumulative/average regret and the vanishing-delta finite-window source event | exact exploratory PMF/integral; source `policyAt` alignment; bounded Bellman values; recommendation source terminal; finite sums and measure monotonicity | expand the exploratory PMF mixture; prove the remaining-horizon value envelope; align source coordinates `1..rounds`; propagate and sum stage discrepancies; divide cumulative transport by positive rounds; include behavior violations in the parent bad event | finite measurable nonempty state/action with equality/singletons; probability; exploration at most one; deterministic bounded rewards; positive rounds for average; source inherits path support/floor and dependent Standard Borel spaces; initial coordinate zero excluded | exact no-hit memory search; local exploratory/source and scheduled-average APIs; Mathlib PMF/integral/kernel/sum/asymptotic/order cards; Slivkins/UCB-VI/scenario evidence; weapons inspiration only | `leanCompiled`; 20 declarations; focused/root/Tests; Unit charge/alignment, two-action nonzero gap, typed transport/violation/good-side canaries; placeholder/baseline axioms; review/index/full gate | fixed positive exploration leaves a nonzero residual charge in this theorem; the downstream compatible decaying-exploration consumer now supplies a zero-limit dependent finite-window route; no violation measurability, common process, realized regret, stochastic rewards, minimax rate, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-VANISHING-DELTA-HIGH-PROBABILITY-AVERAGE-CONSISTENCY` | set `delta_n=1/(n+2)`, schedule `n+1` recommendation rounds and the parent batch size, prove the `ENNReal` failure budget and average certificate jointly tend to zero, and bound a named regret-violation set at every dependent finite window | compiled scheduled-average route; real/ENNReal continuity; product filters; measure monotonicity; parent source terminal | specialize positivity and unit upper bound; squeeze the varying certificate under the delta-independent envelope; compose `ENNReal.ofReal`; include violation in the bad event; package explicit per-window Borel witnesses | finite measurable nonempty state/action with equality/singletons; probability; positive horizon/floor; path support/common floor; bounded deterministic rewards; dependent Standard Borel batch/trajectory family; no common sample space | scheduled/average/normalized local cards; Slivkins/UCB-VI/scenario evidence; Mathlib asymptotics/order/measure/kernel APIs; exact local declaration lookup and no memory hit; weapons inspiration only | `leanCompiled`; 14 declarations; focused/root/Tests; Unit delta/joint-limit/window/family canaries; placeholder/baseline axioms; review/index/full gate | dependent finite-window high-probability certificates only; fixed-rate and compatible decaying-rate behavior consumers compile, but fixed-process/common-space coupling, violation measurability, realized regret, stochastic rewards, minimax rate, and complete UCB-VI remain open |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-SCHEDULED-AVERAGE-CONSISTENCY` | choose `episodes=ceil(max(T,2L/visitFloor))+1`, prove calibration and `L<episodes*visitFloor/2`, bound the average recommendation guarantee by `16*card(State)*H^2/(sqrt(visitFloor)*sqrt(rounds))`, prove scalar Tendsto zero, and instantiate the same-event source terminal per finite window | compiled average/normalized route; scheduled threshold/episodes/envelope; Nat ceil; Real log/sqrt; at-top division; squeeze; parent terminal | strict ceil domination; positive-floor cross multiplication; square-root ratio bound; inverse-root envelope; scalar squeeze; finite-window source specialization | finite measurable nonempty state/action with equality/singletons; probability; Standard Borel scheduled batch/trajectory; positive horizon/rounds/floor and valid delta; path support; bounded deterministic rewards; no common trajectory type across changing schedules | average/normalized/explicit local cards; Slivkins/UCB-VI/scenario evidence; Mathlib log/sqrt/asymptotics/order/ceil/kernel/integral APIs; weapons inspiration only; exact memory search no hit | `leanCompiled`; 14 declarations; focused/root/Tests; Unit strict schedule/log-mass/exact envelope/Tendsto/full terminal; placeholder/baseline axioms; review/index/full gate | scalar bound convergence and per-window terminal only; vanishing-delta, fixed-rate behavior, and compatible decaying-rate behavior consumers compile downstream; next common-space or realized-regret transport; no one-process pathwise/probability/a.s. consistency, stochastic rewards, minimax rate, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-AVERAGE-RECOMMENDATION-RATE` | divide the normalized cumulative recommendation sum by positive rounds and expose `2*H*min(1,8*card(State)*H*sqrt(L)/sqrt(visitFloor)/sqrt((episodes*rounds)*visitFloor/2))` on the same event | average regret/bound definitions; cumulative exploratory episode count; compiled normalized terminal; `Real.sqrt_mul`, `Real.sq_sqrt`, `min_div_div_right`, cast/division algebra | rewrite the divided minimum; combine round and per-batch square roots into total exploratory mass; divide the parent inequality by positive rounds while retaining event/tail/optimism | parent finite measurable nonempty state/action, probability, Standard Borel, path-support, normalized reward, delta/floor/threshold contracts; positive rounds and episodes; no new law or behavior-regret premise | normalized/explicit local cards; Slivkins and Azar-Osband-Munos route evidence; `SCN-RL-MDP`; Mathlib sqrt/order/sum/kernel/integral cards; optimism/tail weapons inspiration only; exact memory search no hit | `leanCompiled`; focused/root/Tests; 5 checks; Unit `1000*3=3000`, exact average expansion, nontrivial-delta full terminal; placeholder/baseline axioms; review/index/full gate | next construct an integer batch-size schedule satisfying calibration and yielding vanishing average recommendation error; no stochastic rewards, behavior/realized regret, minimax claim, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-NORMALIZED-RATE` | normalized deterministic rewards, budget one, and `scale=4*card(State)*H*sqrt(L)/sqrt(visitFloor)` reduce the parent calibration to `32*card(State)^2*H^2*L/visitFloor^2<episodes` and yield the same-event explicit recommendation-regret sum | normalized scale/threshold/count-radius/bound; compiled explicit-rate constructor and terminal; Real sqrt/square/division | prove the scale-cover equality; dominate the old max threshold branches; construct calibration; expand the closed form; invoke the unchanged source event | finite measurable nonempty state/action with equality/singletons; probability initial law; Standard Borel batch/trajectory; positive horizon/rounds/episodes/visit floor/delta; delta at most one; path support/common floor; deterministic absolute reward bound one | compiled explicit/capped routes; Slivkins and Azar-Osband-Munos route evidence; `SCN-RL-MDP`; Mathlib sqrt/order/sum/kernel/integral cards; optimism/tail weapons inspiration only | `leanCompiled`; focused/root/Tests; 11 checks; Unit rounds three, delta one half, local delta one twelfth, log/threshold/calibration/bound/full-terminal canaries; placeholder/baseline axioms; review/index/full gate | downstream average total-episode route now compiles; next integer batch schedule and vanishing average recommendation error; no stochastic rewards, behavior/realized regret, minimax claim, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-EXPLICIT-CALIBRATION-RATE` | the max episode threshold and independent scale-square inequality construct the complete capped two-scale calibration and yield the same-event optimism/recommended-regret terminal with bound `2*H*min(R*budget,2*scale*sqrt(R)/sqrt(E*visitFloor/2))` | `FiniteHorizonAdaptiveCumulativeInverseSqrtExplicitRate`; exact cumulative radius square; parent calibration/terminal; shifted inverse-sqrt finite sum | write `L=log(2/localDelta)` and `C=2*card(State)*H*(rewardBound+budget)`; prove `r_k^2=k*E*L/2`; derive half-floor margins; compare squares for budget/scale covers; construct calibration; sum cap and inverse-root bounds; compose terminal | finite measurable nonempty state/action with equality/singletons; probability initial law; Standard Borel batch/trajectory; positive horizon/rounds/episodes/visit floor/budget and valid delta; nonnegative scale; path support; known reward bound; `max(2L/v^2,2C^2L/(B^2v^2))<E`; `C^2L<=scale^2v` | compiled capped path-support/martingale routes; local Tsallis shifted inverse-root sum; Mathlib sqrt/order/finite-sum/kernel/integral APIs; UCB-VI evidence only; weapons inspiration only | `leanCompiled`; focused/root/Tests; Unit log/scale/threshold/calibration/sum/full-terminal composition plus exact `Fin 3` shifted-index canary; `delta=1` witness limited to satisfiability; placeholder/baseline axiom audit; independent review; indexes/full gate | downstream normalized and average routes now compile; next integer batch schedule and vanishing average recommendation error; no stochastic rewards, behavior/realized regret, minimax claim, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-INVERSE-SQRT-PATH-SUPPORT-REGRET` | the capped count radius `budget` at zero and `min budget (scale/sqrt(count))` afterward, exploratory path-support floors, and one roundwise two-scale calibration construct the cumulative martingale cover, selected-radius envelope, optimism, and recommended expected-regret finite sum | `FiniteHorizonAdaptiveCumulativeInverseSqrtCalibration`; `TransitionCountRadius.cappedInverseSqrt`; path-support expected-count floor; cumulative mean/deviation/raw-count identities; `CumulativeInverseSqrtPathCalibration`; existing martingale terminal | prove capped-radius antitonicity; transport initial/successor path floors and sum; subtract the global-event radius to lower realized visits; exclude zero counts; use separate cap and inverse-sqrt covers; bound the selected row radius; invoke the existing terminal | finite measurable nonempty state/action with equality/singletons; probability initial law; Standard Borel batch/trajectory; positive horizon/rounds/episodes and valid delta; path support/common floor; nonnegative known reward bound, budget, and scale; positive roundwise lower margins; separate `coverBudget` and `coverScale` | compiled cumulative martingale, cumulative planner, and path-support routes; Mathlib sqrt/min/order/finite-sum/kernel/integral APIs; UCB-VI route evidence only; weapons inspiration only | `leanCompiled`; focused/root/Tests; capped zero/positive radius and positive Unit full-terminal canaries; placeholder/baseline axiom audits; independent local review; indexes/full gate | one-scale radius rejected by the zero-reward Unit no-go; the downstream explicit-rate route now constructs the two-scale calibration and closes the capped inverse-sqrt finite sum; no stochastic rewards, behavior/realized regret, minimax rates, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-MARTINGALE-CONFIDENCE-REGRET` | kernel-centered adaptive batch-count increments give square-root cumulative prefix tails; one round-coordinate event produces cumulative empirical-transition `CoordinateConfidence`, the global contract, optimism, and recommended expected regret | exact adaptive iid batch condDistrib; raw count/map law; kernel integral; `Filtration.piLE`; conditional sub-Gaussian sum; cumulative summary/factorization; coordinate-confidence terminal | prove within-batch Bernoulli MGF; map the next-batch law through raw count; center by the measurable kernel integral; sum conditional MGFs over prefixes; union all finite coordinates; split zero/positive realized visit counts; construct confidence/contract and invoke the terminal | finite measurable nonempty state/action with equality/singletons; probability initial law; Standard Borel batch/trajectory; positive horizon/rounds/episodes; valid delta; known rewards; explicit deterministic planner-radius/value-envelope cover and selected-radius envelope | compiled adaptive-law/cumulative-contract/conditional-expectation/concentration routes; Mathlib filtration/kernel/measure/finite-sum APIs; RL/UCB-VI evidence only; weapon inspiration only | `leanCompiled`; twenty-plus declarations; focused/root/Tests; positive-visit radius and concrete exploratory terminal canaries; clean placeholders; eight baseline-only axiom audits; full gate | downstream capped, explicit, normalized, and average routes compile; next integer batch schedule and vanishing average recommendation error; no stochastic rewards, behavior/realized regret, minimax rates, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-RADIUS-CONTRACT-REGRET` | all observed transition counts form a measurable cumulative empirical planner/source; nonnegative antitone count radii shrink with visits; one explicit cumulative confidence contract yields optimism and recommendation regret `<= sum round, horizon*(2*radiusEnvelope round)` | cumulative prefix summary/successor identity; count-radius plan, selected radius and zero-count value envelope; measurable cumulative exploratory source; coordinate confidence; occupancy monotonicity/constant evaluation | sum finite prefix coordinates; normalize the cumulative kernel; prove visit monotonicity and radius antitonicity; comap the exploratory iid batch kernel; consume global coordinate confidence; dominate occupancy by a round envelope and sum | finite measurable state/action with equality/singletons; nonempty state/action; probability initial law; nonnegative antitone radius; measurable bad event/global tail; cumulative confidence and selected-radius envelope; known rewards | no exact cumulative-summary hit; compiled latest-batch/confidence/occupancy routes; finite-sum/integral/kernel/conditional-expectation/martingale cards; textbook/RL/UCB-VI route evidence; weapon inspiration only | `leanCompiled`; twenty-plus declarations; focused/root/Tests; Unit horizon one gives counts `1,2`, radii `3,2`; external source/terminal canaries; empty placeholders; eight baseline-only axiom audits | its probability, capped, explicit, normalized, and average consumers now compile; next integer batch schedule and vanishing average recommendation error; no stochastic rewards, behavior/realized regret, minimax rate, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-OCCUPANCY-RADIUS-ENVELOPE` | the current fixed-bonus adaptive radius sum is exactly `rounds*(horizon*(2*transitionBonus))`; the path-support episode-threshold event therefore gives recommended expected regret at most `rounds*(horizon*(2*rewardBound))` | recursive occupancy sum/successor equation; concrete selected radius; fixed-radius optimistic plan; finite `Fin rounds` sum; probability constant integral | induct on remaining horizon with probability-preserving induced state kernels; reduce selected radius to `0+transitionBonus`; evaluate every round and the finite sum; compose with the existing terminal | finite measurable state/action with equality/singletons; nonempty Action/default State; probability initial law; terminal inherits positive horizon/rounds/episodes/visit floor, valid delta, exploration/path-support/reward contracts | no exact constant-occupancy route hit; local successor/monotonicity APIs; `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA`; textbook/RL/UCB-VI evidence only; optimism inspiration only | `leanCompiled`; five declarations; focused/root/Tests; Bool horizon two, two rounds, bonus one gives exact sum `8` and terminal `<=8`; clean placeholders/baseline axioms; independent review P0-P3 none | exact fixed-bonus linear envelope only; next add accumulated cross-round counts and shrinking count-dependent radii; no statistical/minimax rate, stochastic rewards, behavior/realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EPISODE-THRESHOLD-CALIBRATION` | the closed-form threshold `q^2*log(2/localCoordinateDelta)/(2*visitFloor^2) < episodes`, with `q=4*card(State)*horizon+1`, automatically gives the strict count margin and half contraction, then constructs positive cover, calibration, and the global confidence/optimism/recommended-regret terminal | explicit path-support calibration; exact sub-Gaussian radius square; iid Bernoulli variance proxy; local and coordinate delta allocation; Real square/order/division | rewrite radius squared as `episodes/2*log`; multiply the threshold by the positive episode count; transport strict squares to `q*radius<episodes*visitFloor`; derive margin and cross-multiplied half contraction; invoke prior source wrappers | finite measurable state/action with equality/singletons; nonempty Action/default State; probability initial law; positive horizon/rounds/episodes/visit floor; valid delta; path support/common floor; exploration at most one; deterministic reward bound | no exact route hit; compiled explicit calibration; `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`; textbook/RL/UCB-VI evidence only; optimism inspiration only | `leanCompiled`; eight declarations; focused/root/Tests; Bool `q=17`, coordinate delta `1/96`, threshold `9248*log 192<2^22`, margin/contraction, positive bonus-one cover, calibration and terminal; clean placeholders/baseline axioms; independent review P0-P3 none | fixed-batch sufficient threshold only; no accumulated statistics, occupancy-radius rate, stochastic rewards, arbitrary support, behavior/realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EXPLICIT-COUNT-BONUS-CALIBRATION` | one uniform path-support state-action floor, a strict scalar count inequality, and a finite-state/horizon half contraction automatically construct the source count margin and positive cover with `transitionBonus=rewardBound`, then recover the global confidence/optimism/recommended-regret terminal | path-support reachability; exploratory expected counts; deterministic coordinate radius; linear value envelope; finite sums/order division | define `2*r/(episodes*visitFloor-r)`; bound each policy radius; sum over next states; bound remaining by horizon; apply half contraction; instantiate initial/successor tables; construct calibration and invoke terminal | finite measurable state/action with equality/singletons; nonempty Action/default State; probability initial law; exploration rate at most one; valid path support; common visit floor; strict positive denominator; half contraction; reward bound; positive rounds/episodes and valid delta | compiled path/reachability/all-coordinate routes; finite-sum/order/integral/kernel Mathlib cards; textbook/RL/UCB-VI evidence only; optimism inspiration only | `leanCompiled`; ten declarations; focused/root/Tests; Bool horizon two, floor `1/8`, `2^22` episodes, radius `<30000`, uniform radius `<=1/8`, positive bonus-one cover, calibration and terminal; clean placeholders/baseline axioms; independent review P0-P3 none; indexes/full gate | downstream episode threshold now closes the scalar premises; arbitrary support, accumulated statistics, occupancy-rate bound, stochastic rewards, behavior/realized regret, and complete UCB-VI remain |
| `RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-REACHABILITY-CALIBRATION` | explicit initial/transition singleton path support recursively supplies one common state envelope for every exploratory source policy, constructs calibration, and recovers the global confidence/optimism/recommended-regret terminal | stage-zero initial marginal; successor transition-event inclusion; exact visit/transition factorizations; exploratory floor; prior reachability terminal | define selected predecessor support; recurse over stages; propagate nonnegative products through exact population laws; instantiate all source tables; invoke calibration and terminal | finite measurable state/action with decidable equality/singletons; nonempty Action and explicit default State; probability initial law; exploration rate at most one; nonnegative valid initial/transition floors; predecessor choice per positive-stage target; strict local count margin; unchanged cover; terminal positivity/reward contracts | compiled transition/visit/calibration routes; kernel/integral/order Mathlib cards and exact APIs; RL/UCB-VI evidence only; optimism inspiration only | `leanCompiled`; focused/root/Tests; Bool-state/action horizon-two floors `1/2` then `1/4`, direct chronology/table checks, 24-coordinate/16384-episode margin, source reachability, zero cover, calibration and full terminal; clean placeholder/baseline axioms; local review P3 resolved; indexes and full gate | selected-path support closes reachability only under the certificate; no arbitrary-MDP positivity, full marginal sum, automatic count/bonus rate, accumulated data, behavior/realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-EXPLORATORY-STATE-REACHABILITY-CALIBRATION` | state-only reachability times the exploratory action floor supplies every source-policy expected-count margin, constructs `SourceCalibration`, and directly recovers the global confidence/optimism/recommended-regret terminal | stage-visit factorization; exploratory PMF/kernel/source; expected counts; ENNReal-to-Real; existing calibration and terminal | convert PMF floor; multiply state and action masses; multiply by episodes; package initial/successor reachability and cover; invoke terminal | finite measurable state/action with decidable equality/singletons; nonempty Action, explicit default State, probability initial law; exploration rate at most one; shared state envelope; strict local count margin; unchanged cover; terminal reward/budget/delta positivity contracts | compiled stage-visit/adaptive routes; kernel/integral/order Mathlib cards and exact APIs; RL/UCB-VI evidence; optimism inspiration only | `leanCompiled`; focused/root/Tests; Bool half floor and distinct initial `1/4`/successor `3/4` source; concrete Unit two-round local-delta/radius/reachability/cover/calibration/terminal; baseline axioms, review/re-review, indexes and full gate | state-action margin interface is reduced to state-only reachability and exploration, not automatically proved; state support, rates, accumulated data, behavior/realized regret and complete UCB-VI remain |
| `RL-FINITE-HORIZON-STAGE-VISIT-FACTORIZATION` | generated stage/state/action visit probability equals generated stage-state probability times policy action singleton mass | chronological remaining-coordinate map; recursive trajectory kernel; `Kernel.compProd_apply`; initial-law `Measure.compProd_apply`; `ENNReal.toReal_mul` | prove the head event from the action/state kernel; induct under recursive compProd for successors; integrate the initial state and rewrite public events | stage arithmetic is contract-free; event laws use finite measurable state/action, singleton measurability and state decidable equality; named Real endpoint inherits both decidable equalities and a probability initial law; no support or reachability | compiled transition factorization; kernel/integral Mathlib cards and exact APIs; RL/UCB-VI evidence only; weapons inspiration only | `leanCompiled`; focused/root/Tests; stage-dependent zero/half visit canaries and direct successor-coordinate kernel instantiation; baseline axioms, review/re-review, indexes and full gate | exact factorization includes zero state mass; next combine a separately proved state lower bound with exploratory action support; no automatic calibration, behavior/realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-EXPLORATORY-EMPIRICAL-OPTIMISTIC-ALL-COORDINATE-CONFIDENCE-RECOMMENDED-REGRET` | exploratory latest-batch data yields coordinate confidence and optimism off one global event; recommended optimistic-policy expected regrets sum below selected-radius occupancies | exploratory PMF/source; global count terminal; summary/raw bridges; `CoordinateConfidence`; finite sums | prove uniform action floor; construct exact exploratory iid source; derive every roundwise witness under calibration; sum recommended-plan one-episode bounds | finite measurable nonempty state/action; probability initial law; exploration rate at most one; positive rounds/batches and valid delta; fallback, reward bound, nonnegative bonus; state-reachability margins and coordinate bonus cover | parent adaptive/count/all-coordinate/optimism routes; Mathlib PMF/kernel/integral/finite sums; RL/UCB-VI evidence; weapons inspiration only | `leanCompiled`; focused/root/Tests; exact Bool half-mass and terminal canaries; review defect repaired; baseline axioms/indexes; full gate root 3508, Tests 3510, CLI 15/skip 1 | action support is closed, but reachability/bonus calibration is assumed; recommendation regret is not behavior or realized regret, an explicit rate, accumulated UCB-VI, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-SOURCE-COUNT-CONFIDENCE` | every observed batch measurably selects a known-reward empirical-transition optimistic deterministic policy; table-indexed iid laws produce an exact adaptive source with the selected next-batch conditional law and a global-delta count-confidence terminal | parent adaptive/count/empirical routes; transition-count summary; `PMF.ofFintype`; countable measurability; `Kernel.ofFunOfCountable`; `Kernel.comap`; finite table-event union | extract measurable counts; normalize empirical rows with fallback; build optimistic plan/table; construct and comap the table batch kernel; discharge selected event measurability; consume parent condDistrib/count terminal | finite measurable state/action with decidable equality, measurable singletons and nonempty types; probability initial law; initial table, fallback, fixed Real bonus; positive rounds/batch size and valid delta; Standard Borel batch only for condDistrib | parent local cards; kernel/integral/finite-sum Mathlib cards and exact countable/PMF/comap APIs; RL/UCB-VI evidence; tail/optimism inspiration only | `leanCompiled`; focused/root/Tests; source/law/condDistrib/nontrivial terminal plus Bool horizon-two `3/4`/`1/4`, zero-fallback, opposite-action semantic canaries; baseline axioms; review P3 resolved; indexes and full gate pass (root 3507, Tests 3509, CLI 15 with one skip); calibrated confidence/regret consumer compiles downstream | known rewards, latest batch only, fixed bonus; downstream confidence assumes calibration; no accumulated data, automatic occupancy coverage, explicit bonus rate, realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-ADAPTIVE-EPISODE-BATCH-COUNT-CONFIDENCE` | a history-dependent Ionescu--Tulcea batch trajectory has the selected policy's generated iid batch law as every next-batch conditional distribution; measurable adapted local count events at `delta/rounds` form one global-delta event, outside which all selected-policy count deviations hold | parent iid/simultaneous/offline-multibatch routes; `Kernel.trajMeasure`; `condDistrib_trajMeasure`; prefix `compProd`; `Measure.compProd_apply`; `lintegral_mono`; finite equal-share union | package exact selected-policy batch kernels; identify initial and successor laws; integrate history-fiber tails; union local shares; instantiate selected-policy simultaneous count events | finite measurable state/action; probability initial law; positive rounds/batch size; valid delta; Markov source kernels exactly equal selected-policy iid laws; measurable in-horizon successor count events; Standard Borel batch only for condDistrib | parent local cards; kernel/integral/independence/finite-sum/order Mathlib cards; exact Ionescu--Tulcea APIs; RL/UCB-VI evidence; tail/optimism inspiration only | `leanCompiled`; focused/root/Tests; constant and genuinely history-sensitive piecewise sources; both branches, nontrivial `delta=1/2` terminal, placeholder/baseline axioms; both review P3 findings resolved; indexes and full gate pass (root 3506, Tests 3508, CLI 15 with one skip) | source is supplied, not constructed from a concrete optimistic update; no adaptive reward/model confidence, bonus control, realized regret, or complete UCB-VI |
| `RL-FINITE-HORIZON-IID-MULTIBATCH-CUMULATIVE-CONFIDENCE-REGRET` | a finite `Measure.pi` family of fixed-policy iid batches has one global-delta union event; off it every batch-specific empirical model is optimistic and the sum of optimistic-policy expected regrets is bounded by the sum of selected-radius occupancy terms | parent all-coordinate confidence; `Measure.pi`; `measurePreserving_eval`; `measure_preimage`; `ae_of_ae_map`; equal-share finite union; `Finset.sum_le_sum` | allocate `delta/rounds`; identify product marginals; union pulled-back local events; pull reward consistency through every coordinate; construct all confidence witnesses; sum one-episode bounds | finite measurable state/action; fixed data policy and probability initial law; positive rounds/batch size; valid delta; reward bound; nonnegative transition budget; full coordinate margin and cover at local delta; batch-derived optimistic policies may vary | parent local cards; independence/kernel/integral/finite-sum/order Mathlib cards; exact local product/union APIs; RL/UCB-VI evidence; optimism inspiration only | `leanCompiled`; focused/root/Tests and strengthened two-batch marginal/local-tail/global-tail/reward/confidence/full-terminal/nonzero-budget canaries pass; review found no production issue; placeholder/baseline-axiom audits, indexes, and full gate pass | independent offline product only; no adaptive history law, dependence on earlier optimistic policies, realized cumulative regret, bonus-rate bound, or complete UCB-VI |
| `RL-FINITE-HORIZON-IID-ALL-COORDINATE-FINITE-BATCH-CONFIDENCE` | canonical generated empirical model has reward radius zero, fixed transition budget, a full `FiniteBatchModel.Confidence` a.e. off the shared count event, and therefore optimism plus the existing one-episode expected-regret bound | generated reward support; simultaneous count/transition consumers; `FiniteBatchModel.Confidence`; finite-kernel integral bound; ordered-field denominator monotonicity | use `expectedCount-radius` as a genuine positive deterministic denominator; prove exact all-coordinate rewards; inductively bound upper values by `remaining*(rewardBound+transitionBudget)`; apply the explicit finite coordinate cover; transport through the mapped iid law | finite measurable state/action with decidable equality, measurable singletons and nonempty action; fixed policy/probability initial law; all-coordinate strict margins; reward absolute bound; nonnegative fixed transition budget; explicit cover; positive episodes/valid delta for tail only | parent local cards; finite-sum/order/integral/kernel Mathlib cards; RL/UCB-VI evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests; direct/mapped/full-terminal and horizon-two nonzero-envelope canaries; baseline axioms; review findings resolved; indexes and full gate pass | partial eligibility is insufficient; preserve denominator direction and explicit cover; no stochastic reward, adaptive episodes, cumulative bonus/regret, anytime, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-IID-GENERATED-EMPIRICAL-REWARD-EXACTNESS` | reward-consistent batches satisfy `rewardSum = visitCount * mdp.reward` and positive-count empirical reward equals `mdp.reward`; generated batches are consistent pointwise and mapped iid batches a.e.; eligible good-event coordinates expose exact reward plus every transition singleton bound a.e. | iid trajectory extraction; measurable consistency set; `ae_map_iff`; empirical reward/count APIs; eligible positivity/transition confidence; finite-sum and denominator algebra | prove generated consistency, transport it through the mapped law, factor the reward sum, cancel positive counts, then combine a.e. support with the unchanged simultaneous event | finite measurable state/action; decidable equality for statistics; measurable singletons for mapped support/good-event; fixed policy/probability initial law, fallback and eligible margin; deterministic reward; no range/sub-Gaussian/integrability/extra delta/Nonempty | four parent local cards; finite-sum/order/measure Mathlib cards; RL/UCB-VI evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests; nonzero/zero/a.e.-support/generated/bundled canaries; baseline axioms; independent review P2/P3 repaired; indexes and full gate pass | arbitrary raw batches may be inconsistent; zero-count empirical reward remains zero; no stochastic reward or full `FiniteBatchModel.Confidence`; next require all-coordinate eligibility and a noncircular value-envelope/radius assembly |
| `RL-FINITE-HORIZON-IID-ELIGIBLE-EMPIRICAL-TRANSITION-CONFIDENCE` | under one global-delta simultaneous-count event, every eligible positive-margin stage/state/action and every next state have empirical singleton transition error strictly below `2*radius/visitCount` | empirical transition count ratio; simultaneous visit/joint deviations; eligible denominator positivity; generated joint-law factorization; `abs_div`; positive ordered-field division | rewrite `P-hat` as joint/visit counts; replace joint mean by visit mean times true kernel mass; combine both count errors using transition mass in `[0,1]`; divide by the positive realized count; quantify under the unchanged simultaneous event | finite measurable state/action; fixed policy and probability initial law; positive episodes; `0<delta<=1`; finite eligible set and per-coordinate expected-count margin; explicit fallback state; reward unused; no Nonempty typeclass; zero horizon/empty eligible allowed | four parent local cards; order/measure/kernel Mathlib cards and exact source; RL/UCB-VI evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests; direct/bundled/zero-horizon and concrete Bool nonzero-error canaries; baseline axioms; independent review findings resolved; full gate before handoff | preserve the random positive denominator and existing global event; do not replace it by an unproved deterministic occupancy lower bound or claim reward/adaptive/anytime/cumulative UCB-VI confidence |
| `RL-FINITE-HORIZON-STAGE-TRANSITION-JOINT-FACTORIZATION` | generated stage joint probability equals visit probability times the true transition-kernel singleton mass | recursive trajectory kernel; extracted stage record; `Measure.compProd_apply`; `Kernel.compProd_apply`; `Kernel.fst_compProd`; singleton rectangles; `ENNReal.toReal_mul` | induct through the remaining trace, factor at the selected action/next-state draw, carry the constant transition mass through earlier layers and the initial law, then rewrite named Real event masses | finite measurable state/action with decidable equality and measurable singletons; fixed MDP/policy; probability initial law; no positivity, episodes, delta, concentration, reward bound, division, or adaptivity | parent generated-trajectory/count cards; exact kernel/integral Mathlib source; RL scenario and UCB-VI route evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests; reachable-one and unreachable-zero canaries; baseline axioms and independent review; empirical transition consumer compiled | population factorization is closed and consumed by eligible empirical transition confidence; no reward/adaptive/anytime/cumulative UCB-VI claim |
| `RL-FINITE-HORIZON-IID-ELIGIBLE-VISIT-COUNT-POSITIVITY` | any finite eligible visit-coordinate set with expected count strictly above the simultaneous radius has positive realized counts off the simultaneous event; its exact zero-count union has the same global-delta mapped-batch tail and a positive-count complement | `FiniteHorizonIIDEligibleVisitCountPositivity`; parent simultaneous endpoint; finite union/equality measurability; order algebra; measure monotonicity | owned visit coordinate/count/expected count/zero event; strict-deviation contradiction; zero-union subset; inherited tail; exact-complement and simultaneous-good consumers; bundle | finite measurable state/action; fixed MDP/policy; probability initial law; finite eligible set; positive episodes; `0<delta<=1`; per-eligible strict margin; zero horizon/empty eligible allowed; no global full support | parent local card; order/fintype/measure Mathlib cards; RL scenario/UCB-VI route evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests; concrete nontrivial margin and `delta=1/2` tail; Nat-zero/singleton/horizon-zero canaries; baseline axioms; review findings resolved; empirical transition consumer compiled | positive denominators are closed and consumed downstream; unreachable/low-margin coordinates remain excluded; no reward/adaptive/anytime/cumulative UCB-VI claim |
| `RL-FINITE-HORIZON-IID-SIMULTANEOUS-COUNT-CONFIDENCE` | the union of all finite visit and joint-transition count bad events at equal delta shares has mapped-batch measure at most global delta, with coordinatewise strict bounds outside the union | `FiniteHorizonIIDSimultaneousCountConfidence`; explicit coordinate equivalence/cardinality; parent marginal tails; `measure_biUnion_finset_le_of_uniform`; `MeasurableSet.iUnion` | dispatch the two coordinate constructors; split empty/nonempty index; apply the equal-share union wrapper; expose generic and specialized good-side consumers | finite measurable state/action; fixed MDP/policy; probability initial law; positive episodes; `0<delta<=1`; zero horizon allowed; reward unused; no adaptive policy/ratios | parent count card; union/Hoeffding/sub-Gaussian/integral/finite cards and exact Mathlib source; RL/UCB-VI evidence; tail/optimism weapons inspiration only | `leanCompiled`; focused/root/Tests; direct visit/transition dispatcher and horizon-two/zero-horizon canaries; baseline axioms; independent review P3s resolved; positivity and ratio consumers compiled | simultaneous count route is closed and consumed downstream; no reward, adaptive, anytime, cumulative-regret, or complete-UCB-VI claim |
| `RL-FINITE-HORIZON-IID-COUNT-CONFIDENCE` | fixed visit and joint-transition counts under the mapped iid batch law have two-sided delta tails around episodes times their genuine single-trajectory means | `FiniteHorizonIIDCountConcentration`; mapped-batch marginal/statistic independence; bounded-centered Hoeffding; finite measurable sums/events; delta-calibrated independent sum | measurable `{0,1}` indicators; event-mass means and joint-to-visit domination; common integral transport; exact cast centered-count identities; proxy `episodes/4`; measurable bad events; invoke tails separately | finite measurable state/action with decidable equality/singletons; fixed MDP/policy; probability initial law; positive episodes; `0<delta<=1`; no reward contract | parent iid-batch card; bounded/sub-Gaussian concentration cards; exact Mathlib measureReal/Hoeffding/sum APIs; RL scenario/UCB-VI evidence only | `leanCompiled`; focused/root/Tests/CLI/full gate; direct range/integral/count/independence/measurability/tail canaries; baseline axioms; review no P0-P2 and P3 resolved; indexes refreshed | fixed-coordinate tails closed; next simultaneous finite coordinate union budget, then denominator positivity and ratio confidence; joint center is not conditional and bundled conjunction is not a joint delta event |
| `RL-FINITE-HORIZON-IID-TRAJECTORY-BATCH-LAW` | fixed-policy iid generated trajectories map measurably to empirical episode records; each episode/stage marginal is the genuine trajectory-law pushforward; mapped batch records/statistics and source contributions are independent; aggregates are exact contribution sums | `FiniteHorizonIIDTrajectoryBatch`; owned `EpisodeStep` measurable projections; `Measure.pi`; `measurePreserving_eval`; `Measure.map_map`; `iIndepFun_pi`; `iIndepFun_iff_map_fun_eq_pi_map`; compiled parents | reconstruct stage state; map trajectories to records; identify coordinate marginals; transport product independence to mapped batch law; compose statistics; expose exact source-contribution sums | finite measurable state/action spaces with inherited decidable/singleton/nonempty contracts; fixed MDP and one fixed policy; probability initial law; finite episodes; deterministic MDP rewards; no adaptive cross-episode policy | parent local cards; iid reward family; exact Mathlib product/evaluation/independence APIs; probability kernel/integral/finite cards; RL scenario/UCB-VI route evidence only | `leanCompiled`; focused/root/Tests/full gate; public and horizon-two semantic canaries; baseline axiom audit; independent review P2/P3 resolved; indexes refreshed | generated batch law and fixed-policy iid mapped/source independence closed; next center fixed-stage visit/transition indicators and prove bounded finite-sum deviations; no ratio confidence, filtration, cumulative regret, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-FINITE-BATCH-EMPIRICAL-MODEL-CONFIDENCE-REGRET` | finite episode-stage records define visit counts, empirical rewards and transition frequencies, an explicit zero-count fallback Markov kernel, and an empirical model whose raw coordinate confidence implies optimism and selected-radius single-episode expected regret | `FiniteHorizonEmpiricalModel`; `PMF.ofFintype`; `PMF.pure`; `PMF.toMeasure`; `Kernel.ofFunOfCountable`; `ENNReal.add_div`; compiled coordinate endpoint | prove transition counts partition visits; normalize positive counts by finite induction and use fallback Dirac at zero; build Markov kernel and empirical plan; transport reward/frequency errors through `CoordinateConfidence`; invoke endpoint | finite state/action with decidable equality, measurable singletons and nonempty types; finite records; explicit default state; empirical error contracts; generated-tail envelope and radius coverage; probability initial law only for regret; records not yet generated by the MDP law | parent local cards; exact Mathlib PMF/kernel/finite-sum APIs; kernel/integral/finite/order cards; RL scenario/UCB-VI evidence; optimism/tail weapons inspiration only | `leanCompiled`; focused/root/Tests/full gate; zero and positive-count canaries; complete nonzero-error confidence/endpoint canary; baseline axioms and independent review | deterministic empirical-model producer closed; next identify a random episode batch and prove simultaneous reward/transition concentration; no filtration, confidence probability, cumulative regret, or complete UCB-VI claim |
| `RL-FINITE-HORIZON-COORDINATE-MODEL-CONFIDENCE-REGRET` | singleton estimated/true transition-mass errors and a generated-tail value envelope imply the recursive transition confidence, global optimism, and selected-radius single-episode expected-regret bound | `FiniteHorizonCoordinateModelConfidence`; `integral_fintype`; `integrable_of_fintype`; `Finset.abs_sum_le_sum_abs`; parent estimated-model endpoint | expand finite expectations into atomic sums; rewrite coordinatewise; apply triangle/product bounds; cover by transition radius; package `Confidence`; invoke compiled endpoint | finite state/action measurable spaces; parent estimated plan; nonempty actions; singleton-measurable states; coordinate radii/errors; generated-tail absolute envelope; finite-sum radius coverage; probability initial law only for regret; no empirical counts/events | parent local cards; exact Mathlib atomic-integral and finite-sum APIs; kernel/integral/finite/order cards; scenario/UCB-VI evidence; optimism/tail weapons inspiration only | `leanCompiled`; focused/root/Tests and full gate; generic consumers, nonzero atomic and complete horizon-two coordinate canaries; baseline axioms only; independent review no P0-P2 and both P3s resolved; indexes refreshed | coordinate-to-Bellman transport closed; next produce empirical reward and singleton transition events from episode history; preserve envelope and finite-state atomic semantics; no confidence-probability or complete-UCB-VI claim |
| `RL-FINITE-HORIZON-ESTIMATED-MODEL-OPTIMISTIC-REGRET` | two-sided estimated reward and recursive-tail transition confidence constructs a true optimistic certificate and bounds estimated-greedy single-episode expected regret by the true occupancy sum of twice the selected radii | `FiniteHorizonEstimatedModelCertificate`; compiled certificate/occupancy route; finite argmax; deterministic kernel and Dirac integral | recurse optimistic estimated backups; lower error sides prove true-Q upper confidence; align chronological and remaining selectors; upper error sides prove factor-two residual; consume existing occupancy theorem | finite state/action measurable spaces; parent contracts; nonempty actions; singleton-measurable states; measurable estimates/radii; stagewise estimated Markov kernels; transition error only on generated tail upper values; probability initial law for regret; no random confidence event/episode process | all parent local RL cards; exact finite-max/kernel/certificate declarations; kernel/integral/finite cards; scenario/UCB-VI evidence; optimism weapon inspiration only | `leanCompiled`; focused/root/Tests, 20 checks, concrete nonzero-error and direct bridge canaries, zero endpoint, axiom audit, independent review, indexes and full gate pass | deterministic model-confidence transport and single-episode bound closed; next produce the confidence inequalities from empirical episode history and concentration, then sum episodes; no complete UCB-VI claim |
| `RL-FINITE-HORIZON-OPTIMISTIC-BELLMAN-CERTIFICATE` | true-Bellman upper plan implies global optimism and bounds one episode's expected regret by any pointwise-dominating residual bonus summed under true occupancy | `FiniteHorizonOptimisticCertificate`; compiled optimality/occupancy routes; Bellman monotonicity; occupancy-sum monotonicity | backward induction; residual telescope; canonical compatibility; pointwise bonus transport | finite state/action measurable spaces; parent contracts; `Nonempty Action`; `MeasurableSingletonClass State`; probability initial law; zero terminal upper and local true Bellman upper inequalities; no estimated model/confidence/episode process/high-probability rate | all parent local RL cards; exact local Bellman/occupancy APIs; kernel/integral/finite cards; scenario and UCB-VI/literature evidence only | `leanCompiled`; focused/root/Tests, public checks, global-optimism/canonical/final canaries, zero boundary and axiom audit; full gate required | deterministic certificate-to-single-episode-regret route closed; next estimated-model confidence producer and episode assembly; no complete UCB-VI claim |
| `RL-FINITE-HORIZON-OCCUPANCY-REGRET` | chronological state occupancies and exact expected trajectory regret as the recursive finite policy Bellman-gap sum; nonnegative for all policies and zero for the greedy optimum | `FiniteHorizonOccupancyRegret`; compiled trajectory and optimality routes; `MeasureComp`; `snd_compProd`; map/compProd integrals | compose state laws; push continuation differences through induced kernels; reindex chronological gaps; recurse/telescope; rewrite trajectory reward as policy value | finite state/action measurable spaces; parent contracts; `Nonempty Action`; `MeasurableSingletonClass State`; probability initial law; no bounds/caller integrability/optimism/confidence/repeated episodes/high-probability regret | all parent local RL cards; exact Mathlib measure-kernel composition/integral APIs; kernel/integral/finite cards; scenario/literature evidence only | `leanCompiled`; focused/root/Tests, public checks, probability/equality/endpoint canaries; full gate required | occupancy/performance-difference/expected-regret bridge closed; optimistic certificate now compiles downstream; no UCB-VI confidence or complete-RL claim |
| `RL-FINITE-HORIZON-BELLMAN-OPTIMALITY` | backward finite-action Bellman value dominates every Markov policy and is attained by a measurable deterministic greedy policy | `FiniteHorizonOptimality`; `Finite.exists_max`; `measurable_of_finite`; deterministic kernels; monotone/Dirac integrals; `Nat.decreasingInduction` | choose Bellman-Q argmax; prove finite-discrete selector measurable; establish operator monotonicity; recurse optimal value; dominate all policies; evaluate greedy Dirac kernels and prove all-stage attainment | finite state/action measurable spaces; parent MDP contracts; `Nonempty Action`; `MeasurableSingletonClass State`; no initial law/bounds/caller integrability/occupancy/optimism/regret | all parent local RL cards; exact Mathlib finite-max/measurability/kernel/integral APIs; kernel/integral/finite cards; scenario/literature evidence only | `leanCompiled`; focused/root/Tests, public checks, selector/Markov/dominance/attainment canaries; full gate required | finite Bellman optimality closed; occupancy/value-difference/regret now compiles downstream; no UCB-VI or complete-RL claim |
| `RL-FINITE-HORIZON-POLICY-TRAJECTORY-VALUE-IDENTITY` | the generated finite policy trajectory has expected cumulative reward equal to the initial-law integral of `valueAt 0` | `FiniteHorizonTrajectory`; `StepTrace`; `Kernel.map/comap/compProd`; `Measure.compProd`; `integral_map`; both `integral_compProd` APIs; `Integrable.of_bound` | recursively generate `(action,nextState)` head and tail; prove return measurability and finite-type integrability; expand head/tail then action/transition integrals; apply the statewise induction and initial-law Fubini identity | finite state/action measurable spaces; compiled MDP and stagewise Markov policy; probability initial law for the final theorem; no reward bound, caller integrability, infinite suffix, optimality, occupancy, or regret | both parent local RL cards; Mathlib kernel/integral/finite cards and exact source; RL scenario; literature as evidence only | `leanCompiled`; focused/root/Tests, declaration and typed endpoint canaries; full gate required before handoff | finite policy trajectory/value identity closed; next finite-action Bellman optimality; no occupancy, optimism, UCB-VI, episode-regret, or complete-RL claim |

## Latest Conditional-Law Leaf

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ARM-STREAM-NEXT-UNUSED-COORDINATE-COMPLEMENT-INDEPENDENCE` | fixed arm-stream coordinates have law `nu arm`; histories depend only on consumed coordinates; measurable next-coordinate fibers assemble the adaptive successor `(history,action,reward)` joint law and selected reward `condDistrib` | `UCBArmStreamConditionalReward`; complement reconstruction/product law; Mathlib `Measure.restrict_iUnion`, `restrict_map`, `map_sum`, product restriction, `compProd_sum_left/congr/const`, and `condDistrib_ae_eq_iff_measure_eq_compProd` | flatten coordinates; prove causality and reconstruction; partition both measures into countable disjoint fibers; prove each restricted product law; reassemble the full joint `compProd`; invoke disintegration uniqueness | `0<K`; Markov `nu : Kernel (Fin K) Real`; standard product/Borel instances; no bounds/means/MGF/filtration/integrability/horizon/delta/caller law | exact local and Mathlib source retrieval; independence/kernel/posterior/measure cards; Auer/LML are evidence only | `leanCompiled`; root import; declaration checks; typed independence/product/initial/generated successor canaries; focused/Tests builds; baseline axioms; no placeholders; consumed by the generated terminal route | preserve full history/action conditioning, reward-coordinate product order, and marginal-a.e. semantics; no action-only, moment, global-null-history, or assumed-law fallback |
| `UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-SELECTED-REWARD-LAW-EXPECTED-AVERAGE-CONSISTENCY` | on the fresh canonical pair trajectory, identify initial and successor reward conditional laws with the stationary law of the actual selected arm, then combine them with the explicit UCB policy event and expected-average convergence | `UCBRealStationarySelectedRewardConsistency`; arm-stream successor law; complete trajectory `IdentDistrib.comp`; `RealStationaryUCBSequence` feedback fields; explicit-policy/expected-average terminal | project the full trace law through the exact history/action condition; rewrite condition marginals; compose generated split-law equality with packaged stationary selected laws; bundle with the existing same-process terminal | positive finite arms and Markov Real kernel; finite terminal uses per-arm probability laws and armwise a.s. intervals; exact `c*sigma2`, `c=4`; no caller selected law/common interval/horizon/delta | exact local/Mathlib retrieval; measure/independence/kernel/posterior/asymptotic cards; Auer/textbooks/LML evidence only | `leanCompiled`; root import; public checks; generated successor and terminal external canaries; focused/Tests builds; no placeholders | exact condition-marginal a.e. law only; one fixed process and expected convergence; no global kernel equality, pathwise/probability/a.s. consistency, minimax, complete-UCB, or literal-LML claim |
| `UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-EXPLICIT-POLICY-EXPECTED-AVERAGE-CONSISTENCY` | identify the fresh canonical trajectory's successor action conditional law with `Kernel.deterministic (realHistoryNextArm hK (c*sigma2) n)` on its history marginal, obtain one all-time selector event, and retain the armwise-bounded expected-average terminal | `UCBRealStationaryExplicitPolicy`; `realHistoryNextArm`; `measurable_realHistoryNextArm`; `condDistrib_comp_self`; `IdentDistrib.comp`; `IdentDistrib.ae_mem_snd`; finite pair history; `eventuallyEq_const_of_map_eq_dirac`; prior canonical-kernel terminal | identify the canonical arm-stream kernel a.e.; project complete trajectory law to history marginals; transport the conditional kernel and measurable policy graph; combine initialization with `ae_all_iff`; pair the event with the `c=4` Tendsto theorem | `[NeZero K]`, `0<K`; generic Markov Real reward kernel; concrete per-arm probability and a.s. interval; no horizon/delta/caller bundle/mean/MGF/filtration/conditional expectation/integrability/common interval | exact local declaration search; Mathlib `CondDistrib` source; probability-kernel/posterior/independence/integral/asymptotic cards; pinned LML/Auer/textbooks as evidence only | `leanCompiled`; root import; thirteen checks; conditional-kernel and terminal canaries; focused/Tests builds; baseline axioms; no placeholders; independent review recorded separately | preserve history-marginal a.e. semantics, exact `c*sigma2`, one fixed process, all-time action graph, `c=4`, armwise proxies, and expected scope; no global equality on null histories or stronger convergence; selected-`nu` reward law and literal import remain |
| `UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-ARMWISE-BOUNDED-EXPECTED-AVERAGE-CONSISTENCY` | independently regenerate the canonical UCB observable pair process from its split conditional kernels and prove armwise-bounded logarithmic expected regret with vanishing `n+1` average | `UCBRealStationaryCanonicalKernelTrajectory`; `Thompson.HistoryAlgorithm`; `Thompson.HistoryEnvironment`; `canonicalHistoryTrajectoryMeasure`; `canonicalHistoryAlgorithmEnvironmentSplitSource`; prior external pointwise/Tendsto consumers | package canonical initial/successor action and reward `condDistrib`s; invoke Mathlib `Kernel.trajMeasure`; project generated coordinates; unfold the canonical split source into all four bundle fields; invoke armwise pointwise and terminal parents | `[NeZero K]`, `0<K`; generic Markov reward kernel; concrete per-arm probability and a.s. interval; no caller sample space/bundle/action/reward/split laws/mean/MGF/proxy ceiling/trajectory law/integrability/common bound | exact local declarations; Mathlib `condDistrib_trajMeasure`; Thompson canonical split producer; probability/integral/sub-Gaussian/asymptotic cards; pinned LML/Auer/textbooks | `leanCompiled`; root import; nine checks; producer/pointwise/terminal canaries; focused/Tests builds; baseline axioms; no placeholders; independent review recorded separately | preserve fresh `trajMeasure`, canonical filters, fixed process, `c=4`, armwise proxies, and expected scope; no source-map fallback, caller bundle, moment weakening, or stronger convergence; explicit action policy compiles downstream, while selected-`nu` identification and literal import remain |
| `UCB-REAL-STATIONARY-MEASURE-PRESERVING-SOURCE-ARMWISE-BOUNDED-EXPECTED-AVERAGE-CONSISTENCY` | a canonical UCB process pulled to an external measure-preserving source, concretely `ArmRewardStream K x Aux` with arbitrary probability noise, has the armwise-bounded logarithmic expected-regret envelope and vanishing `n+1` average | `UCBRealStationaryMeasurePreservingSource`; `Measure.map_map`; `MeasurePreserving.map_eq`; `compProd_map_condDistrib`; conditional-law uniqueness; `measurePreserving_fst`; prior external pointwise/Tendsto consumers | transport conditioning and joint pair maps; identify each external conditional law by uniqueness; construct all four bundle fields; specialize to product-first projection; invoke armwise pointwise and terminal parents | `[NeZero K]`, `0<K`; generic finite source measure and measure-preserving map; concrete auxiliary measurable probability space; per-arm probability and a.s. interval; no caller bundle/action/reward/split laws/mean/MGF/proxy ceiling/trajectory law/integrability/common bound | exact local declarations; Mathlib CondDistrib and Measure.Prod APIs; compiled external consumer; probability/integral/sub-Gaussian/asymptotic cards; pinned LML/Auer/textbook evidence | `leanCompiled`; root import; ten checks; generic/product/field-orientation/pointwise/terminal canaries; focused/Tests builds; baseline axioms; no placeholders; independent review no P0-P2 and two P3s integrated | preserve exact measure-preserving law transport, external a.e. filters, fixed product process, `c=4`, armwise proxies, and expected scope; no direct bundle fallback, moment weakening, regret reproof, arbitrary external-policy claim, or stronger convergence; fresh canonical-kernel generator now compiles downstream |
| `UCB-REAL-STATIONARY-ARMWISE-BOUNDED-FINITE-ARM-LAWS-EXPECTED-AVERAGE-CONSISTENCY` | a fixed external `RealStationaryUCBSequence` over armwise-bounded Real laws has exact expected regret bounded logarithmically and vanishing `n+1` average | `UCBRealLMLCompat`; armwise canonical one-policy route; complete trajectory/action projection; measurable regret; Mathlib `IdentDistrib.integral_eq` | project bundled trajectory law to action law; identify each external/canonical regret integral; transport pointwise and Tendsto parents | `[NeZero K]`, `0<K`; fixed finite `mu`; fixed action/reward; field bundle at `c=4`; per-arm probability and a.s. interval; no horizon-indexed process/common bound/caller mean/MGF/ceiling/positivity/trajectory law/integrability | exact local bundle, projection, integral transport, and asymptotic declarations; probability/integral/asymptotic cards; pinned LML and Auer/textbook evidence | `leanCompiled`; root import; nine checks; exact equality, generic/final Tendsto, and pointwise applications; complete statement retrieval; focused/Tests builds; baseline axioms; no placeholders; two review passes no P0-P2 and metadata P3s integrated; consumed by measure-preserving product source | preserve fixed external process, exact law transport, armwise proxies, padded maximum, coefficient, and expected scope; no equivalent bundle, unused-arm reconstruction, sampled fallback, or stronger convergence claim; non-reparameterized generator/literal import remains |
| `UCB-ARM-STREAM-ARMWISE-BOUNDED-FINITE-ARM-LAWS-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY` | arm-dependent bounded Real arm laws directly induce one fixed canonical arm-stream process whose exact expected regret has a logarithmic envelope and vanishing `n+1` average | direct-subGaussian one-policy consumer; armwise interval proxy; padded finite maximum; bounded centered MGF; fixed kernel/action/measure parents | derive each MGF from that arm's own support and identity integral; retain the proxy family; instantiate direct pointwise and Tendsto endpoints | `0<K`; per-arm Real probability laws; arm-dependent a.s. intervals; no common bound, caller mean/MGF/ceiling/positivity/default action/horizon/delta/measurability/integrability/nondegeneracy; zero width valid, inverted support inconsistent | compiled practical parent; exact local declarations; kernel/sub-Gaussian/integral/finite-sum/asymptotic cards; Auer/textbook/scenario; LML/weapons evidence only | `leanCompiled`; focused/root/Tests builds; four checks and full pointwise/terminal applications; baseline axioms; no placeholders; independent review no P0-P2 and metadata P3 integrated | preserve armwise support/proxies, identity means, padded maximum, fixed policy/measure, and expected scope; no common-range collapse, Rat/sampled fallback, or stronger convergence claim; external producer remains |
| `UCB-ARM-STREAM-BOUNDED-FINITE-ARM-LAWS-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY` | common-bounded Real arm probability laws directly induce one fixed canonical arm-stream process whose exact expected regret has a logarithmic envelope and vanishing `n+1` average | `UCBArmStreamFiniteArmRewardLaws`; `Kernel.ofFunOfCountable`; `IsMarkovKernel`; positive padded finite-arm proxy; bounded centered MGF and proxy-monotonicity helpers; canonical one-policy parent | package arm laws as a Markov kernel; rewrite kernel means to identity integrals; derive genuine Hoeffding MGFs; lift to the padded common proxy; instantiate pointwise and terminal parent theorems | `0<K`; per-arm Real probability laws; common a.s. `Set.Icc lo hi` support; no caller mean/MGF/ceiling/positivity/default action/horizon/delta/measurability/integrability/`lo<hi`; zero width is valid and inverted support is inconsistent | exact parent/helper retrieval; kernel/sub-Gaussian/integral/finite-sum/asymptotic cards; Auer/textbook/scenario; LML/weapons evidence only | `leanCompiled`; focused/root/Tests builds; eleven checks and full pointwise/terminal applications; baseline axioms; no placeholders; independent review no P0-P2 with both P3s integrated | preserve Real laws, identity-integral means, fixed policy/measure, padded proxy, and expected scope; no Rat/horizon-indexed fallback or pathwise/probability/a.s./Hannan/minimax/complete-UCB/literal-LML claim; armwise consumer now compiles and the external producer remains downstream |
| `UCB-ARM-STREAM-ONE-POLICY-EXPECTED-AVERAGE-CONSISTENCY` | for one fixed canonical recursive `armStreamAction` and one fixed `armStreamMeasure`, prove exact expected `realKernelRegret` is `O(log(n+1))`, `o(n+1)`, and its `n+1` normalization tends to zero | `UCBArmStreamExpectedPullCount`; exact arm-stream LML-shaped regret theorem; `Mathlib.Analysis.PSeries`; NNReal/ENNReal finite-sum and `toReal` APIs; local log asymptotic bridges | set `c=4`; identify the tail with a cubic NNReal p-series; uniformly dominate `constSum`; assemble a fixed nonnegative kernel coefficient including zero-gap branches; compose Big-O, little-o, and quotient convergence | `0<K`; Markov Real arm kernel; nonzero common NNReal proxy; centered per-arm MGF; no horizon-indexed delta/policy/measure, bounded support, all-positive-gap, filtration, conditional expectation, or caller integrability premise | exact local parent; `NNReal.summable_one_div_rpow`; local asymptotic declarations; Auer/textbook/scenario cards; LML theorem card and weapons as evidence only | `leanCompiled`; root import; focused and `Tests.Basic` builds; public checks plus pointwise/terminal canaries; baseline axioms; no placeholders; common- and armwise-bounded Real laws consume it downstream | preserve one action and measure, `c=4` cubic tail, exact regret, and common proxy; do not regress to horizon-indexed sampled families or claim pathwise/probability/a.s./Hannan/minimax/complete-UCB/literal-LML results; a concrete external producer remains |
| `UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPLICIT-EXPECTED-PSEUDOREGRET` | prove nonnegativity and the explicit fixed-model coefficient times `1+log(T+1)` envelope for the exact armwise-bounded sampled expected pseudo-regret | direct and armwise sampled-asymptotic modules; canonical sampled `nonneg_and_le`; padded finite-arm proxy; armwise centered law; selected-measure simplification; `omega` | derive `0<T` from `model.hK` and `2*K<=T+1`; rebuild the direct practical pair/kernel law; apply the canonical endpoint; extract armwise Hoeffding MGFs and specialize | finite model; per-arm probability; armwise real bounds; a.e. measurable reward casts; per-arm a.s. support; exact means; default arm; `2*K<=T+1`; no separate `hT`, pointwise `lo arm<hi arm`, direct MGF, pair/kernel law, positivity, integrability, or delta; bounded MGF admits zero-width support and padding separately supplies UCB positivity | canonical sampled endpoint; direct/armwise consistency and older fixed-horizon cards; exact declaration retrieval; probability/integral/finite-sum/log/order cards; Auer/textbook/scenario; LML/weapons as evidence only | `leanCompiled`; focused direct/armwise and Tests.Basic builds; two public checks and full armwise application; baseline axioms; no placeholders; independent review no P0-P2 and documentation P3 integrated | preserve explicit coefficient, sampled `t+1`, padded proxy, `delta_T`, horizon-indexed measure, and horizon condition; inverted intervals make the support premise inconsistent; do not weaken to Big-O or claim one-policy anytime/pathwise/probability/a.s./minimax/complete UCB |
| `UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY` | from stationary finite-arm probability laws with arm-dependent a.s. bounded support and exact model means, prove the exact sampled-pair expected pseudo-regret is `O(log(T+1))` and its `T+1` normalization tends to zero | new armwise sampled-asymptotic module; direct-subGaussian parent; armwise bounded centered-law producer and `hasSubgaussianMGF`; selected-measure simplification; asymptotic APIs | define the exact family at each arm's interval proxy; extract direct MGFs from the Unit-context centered law; apply parent Big-O and compose with log little-o and division convergence | finite model; per-arm probability; armwise real bounds; a.e. measurable rewards; per-arm a.s. support; exact means; default arm; no common interval/direct MGF/pair law/centered law/ceiling/positivity/integrability/horizon/delta; no pointwise `lo arm < hi arm` | direct practical parent; older armwise fixed-horizon and common sampled cards; exact declaration retrieval; probability/integral/asymptotics cards; theorem-card/weapons only as evidence | `leanCompiled`; root import; focused/root/Tests.Basic builds; five checks, exact-family canary, full terminal application; baseline axioms and no placeholders; independent review no P0-P3 | preserve armwise interval semantics, sampled `t+1`, padded proxy, `delta_T`, and horizon-indexed measures; no common-bound collapse, reward-only fallback, or one-policy anytime/pathwise/probability/a.s./minimax/complete-UCB claim |
| `UCB-BOUNDED-FINITE-ARM-LAWS-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY` | from stationary finite-arm probability laws with common a.s. bounded support and exact model means, prove the exact sampled-pair expected pseudo-regret is `O(log(T+1))` and its `T+1` normalization tends to zero | bounded sampled-asymptotic module; direct-subGaussian practical parent; `Concentration.intervalVarianceProxy`; bounded centered Hoeffding MGF constructor; `Rat.cast_sub`; asymptotic APIs | derive each arm's centered MGF from a.e. measurability, `Set.Icc lo hi` support, and exact integral; specialize the exact parent family; compose Big-O with `log=o(T+1)` and division convergence | finite model; per-arm probability; common real bounds; a.e. measurable rewards; a.s. support; exact means; default arm; no direct MGF/pair law/centered law/ceiling/positivity/integrability/horizon/delta; no `lo<hi` | direct practical parent and older bounded fixed-horizon cards; exact declaration retrieval; probability/integral/asymptotics cards; theorem-card and weapon evidence only | `leanCompiled`; root import; focused/root/Tests.Basic builds; five checks, exact-family canary, full terminal application; baseline axioms and no placeholders; independent review found no P0-P3 | preserve common-interval Hoeffding semantics, sampled `t+1`, padded proxy, `delta_T`, and horizon-indexed measures; no reward-only fallback or one-policy anytime/pathwise/probability/a.s./minimax/complete-UCB claim |
| `UCB-FINITE-ARM-SUBGAUSSIAN-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY` | from stationary finite-arm probability laws, exact model means, and direct centered sub-Gaussian MGF witnesses, prove the exact sampled-pair expected pseudo-regret is `O(log(T+1))` and its normalization tends to zero | new sampled-asymptotic practical module; `Measure.map`; `Measure.isProbabilityMeasure_map`; `measurable_prodMk_left`; context-independent reward kernel and centered-law constructor; padded finite-arm proxy; generic Big-O/little-o/Tendsto endpoints | push the default arm reward law to `(defaultAction,reward)`; use `Context=Unit`; package the centered kernel; dominate every arm proxy by the padded finite maximum; instantiate generic sampled-pair Big-O; compose with `log=o(T+1)` and division convergence | finite model; per-arm probability laws; exact Real integrals equal `model.mean`; direct centered `HasSubgaussianMGF` at arbitrary NNReal proxies; default arm; no caller pair law/kernel/context/common ceiling/positivity/integrability/horizon/delta | generic sampled consistency and positive-padded finite-arm cards; exact declaration retrieval; `MLIB-MEASURE-INTEGRAL`; `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-FINSET-SUMS`; `MLIB-ASYMPTOTICS`; Auer/textbook/scenario cards; theorem-card and weapon material only as evidence | `leanCompiled`; root import; focused/root/Tests.Basic builds; seven checks, three definitional canaries, and a full terminal application; baseline-only axioms; no placeholders; independent review found no P0-P2 and both P3s are integrated; reviewer full gate passed | preserve initial fixed-action pushforward, sampled `t+1` observable, padded proxy, `delta_T`, and horizon-indexed measures; no reward-only fallback, caller common proxy, one-policy anytime, pathwise/probability/almost-sure/Hannan, minimax, or complete-UCB claim |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-SAMPLED-SUCCESSOR-EXPECTED-AVERAGE-CONSISTENCY` | for the horizon-indexed canonical pair UCB family at `delta_T=1/(T+1)`, prove the exact sampled-successor expected pseudo-regret is `O(log(T+1))` and its normalization by `T+1` tends to zero | sampled-successor Real parent; scheduled delta and log-budget algebra; fixed positive-gap model coefficient; `Asymptotics.isBigO_iff`; `Real.isLittleO_log_id_atTop`; `IsLittleO.tendsto_div_nhds_zero`; new asymptotics module | rewrite the peeling argument to `2*K*T*T*(T+1)`; eventually bound it by `(T+1)^4`; absorb each 32/4/2 plus failure term; sum over positive gaps; sandwich the exact expected integral; compose Big-O, little-o, and division convergence | fixed model/probability initial pair law; measurable context/mean; centered kernel law; stationary means; positive sigma2; uniform `forall i history arm` variance ceiling for all horizons; no caller delta/integrability/ranges/selected law/trajectory law/all-arm positive gaps | sampled Real parent card; exact local retrieval; `MLIB-ASYMPTOTICS`; log, finite-sum, order, integral cards; Auer and finite-bandit textbook/scenario cards; LML route evidence; weapon inspiration only | `leanCompiled`; root import, focused and Tests.Basic builds, ten public checks, full terminal application, and baseline axiom audits pass; independent review found no P0-P2, both wording/status P3s are integrated, and reviewer full gate passed | preserve `delta_T`, exact horizon-indexed pair measures, sampled `t+1` actions, positive-gap filter, fixed-model constants, and uniform variance contract; no one-policy anytime, pathwise/probability/almost-sure/Hannan, minimax, or complete-UCB claim |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-SAMPLED-SUCCESSOR-REAL-TEXTBOOK-GAP-SUM-PSEUDOREGRET` | on the canonical pair `trajMeasure`, bound the Real integral of pseudo-regret for sampled successor action trace `t ↦ (trajectory (t+1)).1` by the explicit positive-gap `32/4/2 + gap*(T*delta)` sum | new sampled-successor trace definition; canonical per-time successor action law; generated UCB regret action; `ae_all_iff`; `funext`; `integral_congr_ae`; parent pair Real theorem | prove each generated regret-action coordinate equals sampled pair coordinate `t+1` ae; package all times as ae complete-trace equality; transport pseudo-regret integral sampled-to-generated; invoke parent theorem | helper needs canonical pair policy/kernel measurability; final inherits `K,T>0`, probability initial pair law, measurable context/mean, centered kernel law, stationary means, variance only for `i<T-1`, positive sigma2/delta; no pointwise equality, coordinate-zero alignment, caller integrability, ranges, selected law, all-time variance, all-arm positivity, event measurability, or delta upper bound | parent pair Real card; canonical sampled-action law and prior ae transport card; exact source/declaration inspection; integral/finite-sum Mathlib cards; Auer/scenario/LML cards; weapon inspiration only | `leanCompiled`; root import, focused and Tests.Basic builds, three external checks, full final application, and baseline axiom audits pass; independent review found no P0-P2, its sole stale-status P3 is integrated, and reviewer full gate passed; fixed-model expected-average consumer compiles downstream | preserve `(t+1)` indexing, same-measure ae equality, explicit Real RHS, and parent contracts; do not claim pointwise/coordinate-zero equality or push through reward-only measure; anytime and complete-UCB routes remain separate |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-REAL-TEXTBOOK-GAP-SUM-PSEUDOREGRET` | on the concrete generated-UCB canonical pair `trajMeasure`, bound the Real/Bochner integral of pseudo-regret by the positive-gap Real sum of `32*sigma2*logBudget/gap + 4*logBudget + 2*gap + gap*(T*delta)` with no public `toReal` | canonical pair ENNReal textbook theorem; generic generated-UCB pseudo-regret integrability; gap nonnegativity; `ofReal_integral_eq_lintegral_ofReal`; ENNReal finite-sum `toReal` APIs; new pair-Real module importing the pair and reward-only Real modules | preserve the exact pair lets; derive reward-coordinate measurability and finite-horizon integrability; prove regret nonnegative; rewrite `ofReal(integral)` as lintegral; consume the pair theorem; prove finite RHS and normalize it termwise to Real | inherited pair contracts: `K,T>0`, probability initial pair law, measurable context/mean, centered kernel law with bundled integrability/MGF, stationary means, variance only for `i<T-1`, positive sigma2/delta; no caller integrability, selected law/ranges, all-arm positivity, all-time variance, event measurability, or delta upper bound | pair ENNReal card; distinct reward-only Real card as proof-shape evidence; expectation/pull-count and measurable-cast leaves; exact declaration/source inspection; Mathlib integral and finite-sum cards; Auer/scenario/LML cards; weapon inspiration only | `leanCompiled`; root import, focused and Tests.Basic builds, full external application, and baseline axiom audit pass; independent review found no P0-P2 and its stale-obligation P3 is integrated; reviewer full gate passed; sampled-successor consumer compiles downstream | preserve direct pair measure, finite explicit Real RHS, internal integrability, exact 32/4/2 and failure terms, and horizon-local variance; do not weaken to a `toReal` RHS or transport through reward-only measure; asymptotic, anytime, and complete-UCB routes remain separate |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET` | on the concrete generated-UCB canonical pair `trajMeasure`, bound the ENNReal lower integral of pseudo-regret by the positive-gap sum of `ofReal(32*sigma2*logBudget/gap + 4*logBudget + 2*gap) + ofReal(gap)*(T*ofReal delta)` | preceding canonical explicit-threshold endpoint; `sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum`; named textbook budget and one-arm threshold/cast lemmas; existing regret import; finite filter/sum and ENNReal order APIs | preserve the canonical measure/action lets; invoke the explicit theorem; compose with the generic finite-arm threshold simplification; filter zero gaps and preserve failure terms exactly | inherited canonical pair contracts: `K,T>0`, probability initial pair law, measurable context/mean, centered kernel law with bundled integrability/MGF, stationary model means, variance only for `i<T-1`, positive sigma2/delta; no all-arm positivity, caller selected-law/ranges, separate ambient integrability, all-time variance, event measurability, or delta upper bound | preceding canonical explicit card; selected-law textbook card; exact declaration/source inspection; finite-sum/order/integral Mathlib cards; Auer/scenario/LML UCB theorem card; weapon inspiration only | `leanCompiled`; focused and Tests.Basic builds; full external canary; baseline axioms only; independent review found no P0-P2, both P3 metadata findings integrated, and reviewer full gate passed; direct pair Real and sampled-successor consumers compile downstream | preserve positive-gap filter, exact 32/4/2 constants, unchanged `gap*T*ofReal(delta)`, canonical T/T+1 alignment, horizon-local variance, and ENNReal output; instantiated-model, asymptotic normalization, anytime/final UCB remain separate |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET` | under the concrete generated-UCB canonical pair `trajMeasure`, bound the ENNReal lower integral of `ofReal (pseudoRegret model regretAction T)` by the all-arm sum of `ofReal(gap)*threshold(gap) + ofReal(gap)*(T*ofReal delta)` | new `UCBConditionalRewardLawRegret` import; generic positive-gap pull-count-to-pseudo-regret consumer; shifted regret action/count identity; model-gap bridge; preceding canonical expected-count endpoint; finite-sum and lintegral APIs | reconstruct the exact canonical measure/reward/action; apply the generic assembly; for each positive-gap arm rewrite to the model best-arm mean gap and invoke the canonical expected-count theorem; rewrite `pullCount` at `T` to successor count at `T+1`; distribute gap over the bound | finite model with `K>0`; probability initial pair law; measurable context/joint mean; centered kernel law (including its pointwise integrability/sub-Gaussian fields); stationary model means; variance only for `i<T-1`; positive `T`, sigma2, delta; no all-arm positivity, caller source/law/ranges, separate ambient/process integrability, all-time variance, event measurability, or delta upper bound | preceding canonical count card; compiled generic selected-policy pseudo-regret assembly; exact source/declaration inspection; Mathlib finite sums, lintegrals, and order APIs; Auer/scenario; weapon inspiration only | `leanCompiled`; focused and Tests.Basic builds; full external canary; baseline axioms only; independent review found no correctness defect and its P2/P3 documentation findings are integrated; reviewer full gate passed; textbook, direct pair Real, and sampled-successor Real consumers compile downstream | preserve successor `T+1` versus shifted pseudo-regret/count horizon `T`, positive-gap-only armwise use, zero-gap elimination, exact integer thresholds, horizon-local variance, and ENNReal output; instantiated-model APIs, anytime confidence, asymptotic normalization, and complete UCB remain separate |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-EXPLICIT-THRESHOLD-EXPECTED-PULLCOUNT` | for one positive-gap arm under the concrete generated-UCB canonical pair `trajMeasure`, bound the explicit-threshold successor pull-count tail by `ofReal delta` and its ENNReal expected count by `threshold + T*ofReal delta` | preceding concrete generated large-gap theorem; generic explicit-threshold tail/lintegral consumers; `selectedPolicySuccessorPullThreshold_contracts`; generated-action/count measurability; pair reward projection measurability; count bound and lower-integral tail split | reconstruct the exact canonical measure/reward coordinate; obtain the generated large-gap tail; feed it to the explicit-threshold tail; prove reward coordinates measurable and feed the same tail to the ENNReal expected-count consumer | preceding centered-kernel contracts with variance only for `i<T-1`; `K,T>0`; explicit default/best/chosen; positive best-to-chosen stationary gap; no caller source/law/ranges/integrability/all-time variance/event measurability/delta upper bound | preceding canonical large-gap card; compiled arbitrary-ambient random-width/explicit-threshold count cards; exact declaration/source inspection; Mathlib measure/integral/finite-sum/order APIs; Auer/scenario; weapon inspiration only | `leanCompiled`; focused/root/Tests.Basic builds; both declarations fully externally canaried; baseline axioms only; independent review found no P0-P2, its P3 module-summary/canary findings were integrated, and all gates passed | preserve `T+1` observable versus `T` charged count, strict positive gap, explicit integer threshold, horizon-local variance, and ENNReal integral; one arm/fixed horizon only, not all-arm sum, Real expectation, anytime, or regret; instantiated `T>K` model and sampled-coordinate count corollary remain optional separate work |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-GENERATED-RANDOM-WIDTH-LARGE-GAP-EVENT` | on the canonical pair `trajMeasure` for the concrete finite-history generated UCB policy, bound its initialized strict random-width large-gap event by `ENNReal.ofReal delta` without a caller source | canonical simultaneous empirical-mean theorem; canonical sampled successor-action a.e. law; generated UCB action/source; `ae_all_iff`; shifted pull-count/reward-sum/empirical-mean definitions; deterministic confidence algebra; `measure_mono_ae`; `Algorithms.UCBConditionalRewardLawPolicy` | get the sampled bad-event tail; assemble sampled/generated successor equality a.e. over all times; identify shifted action traces and transport the generated bad event; include the concrete source large-gap event by contradiction; compose the a.e. inclusions | `K,T>0`; probability initial `Fin K x Rat` law; measurable context/joint mean; centered kernel law; selected generated-history variance only for `i<T-1`; stationary all-arm means; positive sigma2/delta; explicit default/best arms | preceding canonical simultaneous and sampled-source cards; exact generated-policy/source inspection; Mathlib a.e./measure/order APIs; Auer/scenario; weapon inspiration only | `leanCompiled`; focused/root/Tests.Basic builds and full external canary; baseline axioms only; independent review found no P0-P3 and rebuilt both targets | preserve a.e. successor alignment and coordinate shift; do not assume pointwise action equality or identify coordinate zero; no caller source/law/ranges/all-time variance/event measurability/delta upper bound; fixed finite-time probability only, not anytime, expected count, or regret |
| `UCB-CANONICAL-ACTION-REWARD-TRAJMEASURE-RANDOM-WIDTH-LARGE-GAP-EVENT` | on the canonical pair `trajMeasure`, an initialized sampled-coordinate score-max source has random-width strict large-gap event mass at most `ENNReal.ofReal delta` | canonical simultaneous empirical-mean theorem; `SelectedPolicySuccessorInitializedScoreMaxSource.meanGap_le_two_radius_of_not_badEvent`; `selectedPolicySuccessorLargeGapEvent`; `measure_mono`; new algorithm bridge module | invoke the canonical simultaneous tail; show every strict large-gap source trajectory lies in the named confidence bad event by contradiction with `meanGap<=2*radius`; apply measure monotonicity | probability initial pair law; universe-0 nonempty countable standard-Borel measurable-singleton actions with `DecidableEq`; nonempty arms; `T>0`; measurable context/state/mean; centered kernel law; variance only for `i<T-1`; stationary candidate-arm means; positive sigma2/delta; initialized score-max source | preceding canonical simultaneous card; existing practical score consumer and confidence algebra; exact source inspection; Mathlib measure/order APIs; Auer/scenario; weapon inspiration only | `leanCompiled`; focused/root/external canary builds and baseline axiom audit; independent review found no P0-P3 and independently rebuilt both targets | no caller law, raw/mean ranges, all-time variance, event measurability, `Fintype Action`, or `delta<=1`; source API fixes `Action : Type`; fixed finite-time event only, not source construction, anytime, expected count, or regret |
| `COND-EXPECT-REWARD-CANONICAL-ACTION-REWARD-TRAJMEASURE-SIMULTANEOUS-FINITEARM-TIME-EMPIRICAL-MEAN-TAIL` | the named simultaneous empirical-mean bad event over `arms.product (Finset.range T)` has canonical pair-`trajMeasure` mass at most `ENNReal.ofReal delta` | canonical random-count empirical-mean theorem; named finite-arm/time share, radius, and event; finite product/range/card APIs; `ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform`; no new import | prove the product family nonempty; restrict `i<T-1` variance to each `t+1`; apply the random-count theorem with `delta/family.card`; simplify to the named radius; close the finite union | probability initial pair law; nonempty countable standard-Borel measurable-singleton actions with `DecidableEq`; nonempty finite arms; `T>0`; measurable context/state/mean; centered reward-kernel law; variance ceiling for `i<T-1`; stationary means for candidate arms; positive real `sigma2` and delta | preceding canonical random-count card; exact named local APIs; finite-union/Mathlib probability, sub-Gaussian, martingale, and sum cards; Auer UCB1/scenario; weapons inspiration only | `leanCompiled`; focused and external `Tests.Basic` builds; baseline axiom audit; independent review found no P0-P3 and independently rebuilt both targets | fixed finite family with outer equal shares and inner count peeling; coordinate zero uncharged; no raw/mean range, caller law, all-time variance, or event measurability; adjacent canonical UCB row closes the large-gap score event; anytime confidence, concrete source construction, expected count, and regret remain separate |
| `COND-EXPECT-REWARD-CANONICAL-ACTION-REWARD-TRAJMEASURE-RANDOM-PULLCOUNT-EMPIRICAL-MEAN-TAIL` | the canonical pair `trajMeasure` satisfies a fixed-arm empirical-mean deviation tail at the positive realized successor pull count | canonical sampled-arm actual-count tail; sampled/policy action a.e. law; masked-centered-sum identity; exact/peeling radii; finite random-count union helper | specialize the joint tail to budget `sigma2*k`; rewrite and divide on `count=k`; use `measure_mono_ae`; allocate `delta/n` and peel positive fibers with `count<=n` | probability initial pair law; nonempty countable standard-Borel measurable-singleton actions with `DecidableEq`; measurable context/state/mean; centered reward-kernel law; selected-history variance ceiling for `i<n-1`; stationary fixed-arm mean; positive `k`, real `sigma2`, horizon, and delta as appropriate | preceding canonical actual-count card; exact local identities/radii/count-union helper; Mathlib probability/sub-Gaussian/martingale/sum cards; Auer UCB1/scenario; weapons inspiration only | `leanCompiled`; focused/root and both external declaration builds; baseline axiom audit; independent review found no P0-P2 and its P3 status finding is integrated; dedicated `n=1/2` regression canaries remain documented | coordinate zero uncharged; radius pays `delta/n`; no raw/mean ranges or caller conditional law; adjacent canonical rows close the fixed arm/time union and large-gap score event; anytime confidence, concrete source construction, expected count, and regret remain separate |
| `COND-EXPECT-REWARD-CANONICAL-ACTION-REWARD-TRAJMEASURE-SAMPLED-ARM-MASKED-ACTUAL-PULLCOUNT-TAIL` | the canonical pair `trajMeasure` satisfies a two-sided fixed-sampled-arm centered-sum tail jointly with `sigma2 * successorArmPullCount <= varianceBudget` | canonical prefix/next `compProd`; action marginal Dirac law; ambient a.e. map transport; prior policy-mask tail; exact masked-proxy/pull-count identity | prove sampled successor action equals policy action a.e.; combine indices with `ae_all_iff`; transport both finite sums; apply the policy-mask tail and `measure_congr`; rewrite the proxy exactly as the actual successor pull count | probability initial pair law; nonempty countable standard-Borel measurable-singleton actions; `DecidableEq Action`; measurable context/state/mean; centered reward-kernel law; selected-history `varianceProxy <= sigma2` for `i<n-1`; positive budget/delta | preceding policy-mask card; exact local action-map and pull-count declarations; Mathlib `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, `ae_compProd_of_ae_ae`, and `ae_map_iff`; UCB source/scenario; weapons inspiration only | `leanCompiled`; focused/root and external endpoint `Tests.Basic` builds; baseline axiom audit; independent review found no P0-P2 and both P3 metadata findings are integrated; supporting-law full-call and edge canaries remain documented gaps | equality is only a.e. under this canonical pair measure; coordinate zero is arbitrary; `k` increments use `n=k+1`; no positive count, stationary mean, empirical-mean normalization, exact-count peeling, arm/time union, anytime, UCB, or regret claim |
| `COND-EXPECT-REWARD-CANONICAL-ACTION-REWARD-TRAJMEASURE-POLICY-ARM-MASKED-PREDICTABLE-VARIANCE-TAIL` | the canonical pair `trajMeasure` satisfies a two-sided fixed-policy-arm centered-sum tail under a random masked `sigma2` budget | canonical pair `condDistrib_trajMeasure`; pair-history reward projection; policy-mask measurability; masked `StronglyAdapted`; generic predictable-variance tail | build canonical measure; prove the history-policy arm event is `F_i`-measurable; mask centered rewards and proxy; derive horizon MGFs from canonical pair laws; apply the generic delta tail | probability initial pair law; countable standard-Borel measurable-singleton actions; measurable context/state/mean; centered reward-kernel law; selected-history `varianceProxy <= sigma2` for `i<n-1`; positive budget/delta | preceding canonical aggregate-tail card; conditional predictable-variance card; Mathlib kernel/conditional-expectation/sub-Gaussian/martingale cards; UCB source/scenario; weapons inspiration only | `leanCompiled`; focused/root and external `Tests.Basic` builds; baseline axiom audit; independent review found no P0-P2 and both P3 metadata findings are integrated | mask is policy-selected, not sampled-action; `k` increments use `n=k+1`; actual pull-count transport, peeling, finite unions, uniform-time, UCB, and regret remain separate |
| `COND-EXPECT-REWARD-CANONICAL-ACTION-REWARD-TRAJMEASURE-CENTERED-SUM-TAIL` | the canonical action/reward history-step `trajMeasure` satisfies the finite-horizon ENNReal Azuma-Hoeffding upper tail without a caller pair-law premise | canonical pair `condDistrib_trajMeasure`; pair-history reward projection; coordinate measurability; horizon-local arbitrary-action tail | lift context/state to pair histories; build canonical pair `trajMeasure`; simplify projected finite-pair prefix to `frestrictLe`; discharge pointwise variance as trim-a.e.; apply horizon tail | probability initial pair law; countable standard-Borel measurable-singleton actions; measurable context/state/mean; centered reward-kernel law; selected-history variance ceilings for `i<n-1` | policy/reward trajMeasure condDistrib card; preceding horizon pair-law tail; Mathlib kernel/conditional-expectation/sub-Gaussian/martingale/sum cards; stochastic-bandit texts/scenario; weapons inspiration only | `leanCompiled`; focused module and exact external `Tests.Basic` builds; baseline axiom audit | external processes need an explicit pair-law transport; no marginal-only substitution, armwise/sample-count, uniform-time, UCB, or regret claim |
| `COND-EXPECT-REWARD-ARBITRARY-ACTION-HORIZON-PAIR-CONDDISTRIB-AE-VARIANCE-CENTERED-SUM-TAIL` | horizon-local successor joint pair `condDistrib` laws and trim-a.e. selected variance ceilings imply the finite-sum ENNReal Azuma-Hoeffding upper tail | arbitrary-action pair-law/full-prefix route; `Prod.snd` reward projection; native a.e.-variance conditional-MGF consumer; generic strong adaptedness; Mathlib-backed finite-sum wrapper | refactor fixed-time MGF core to accept `ae (mu.trim F_i)` variance; preserve pointwise wrapper; consume law and variance only under `i < n - 1`; apply finite-sum tail | standard-Borel nonempty probability space; countable measurable-singleton actions; measurable traces/context/state/mean; centered reward-kernel law; horizon-local pair laws and trim-a.e. variance | preceding all-time pair-law tail card; conditional-MGF/concentration cards; Mathlib conditional expectation/sub-Gaussian/martingale/sum cards; stochastic-bandit texts/scenario; weapons inspiration only | `leanCompiled`; focused module and exact external `Tests.Basic` builds; three-declaration baseline axiom audit | concrete pair-law and a.e. variance production remain model-facing; do not restore all-time/pointwise premises or claim armwise, uniform-time, UCB, or regret results |
| `COND-EXPECT-REWARD-ARBITRARY-ACTION-PAIR-CONDDISTRIB-CENTERED-SUM-TAIL` | every successor joint pair `condDistrib` law for an arbitrary measurable action/reward process implies the ENNReal Azuma-Hoeffding upper tail for the zero-initialized finite sum of policy-centered successor rewards | arbitrary-action full-prefix theorem; full-prefix-to-next-pair adapter; `Prod.snd` reward projection; integrated history-step conditional-MGF consumer; generic strong adaptedness; Mathlib-backed finite-sum tail wrapper | compile each pair law into a conditional MGF witness, prove arbitrary-action strong adaptedness, align zero and successor slots, apply conditional sub-Gaussian sum tail | standard-Borel nonempty probability space; standard-Borel nonempty countable actions with measurable singletons; measurable traces/context/state/mean; centered reward-kernel law; all-time pair laws; selected-history variance ceilings | preceding arbitrary-action pair-law card; conditional-MGF and concentration local cards; `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MARTINGALE-STOCHASTIC`, stochastic-bandit texts/scenario; weapons inspiration only | `leanCompiled`; focused and exact external `Tests.Basic` builds; three-declaration baseline axiom audit | joint pair-law production remains model-facing; no source-free law, armwise/sample-count confidence, uniform-time theorem, UCB, or regret claim |

## Latest OFUL Leaf

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `EXP3-DOUBLE-VARIANCE-SPARSE-BEST-ARM-EVENTUAL-REFINED-TAIL` | prove fixed parameters eventually force the exact double-variance sparse best-arm threshold into its `16*gamma_T*T` branch and transport the parent off-bad/residual/practical tails | exact best-arm all-horizon and explicit-tuning parents; `Filter.atTop`; Nat/Real casts and powers | close eventual linear/cubic domination; package four conditions at `delta/K`; rewrite the deterministic threshold; reuse identical generated measures and events | parent tail contracts; fixed positive sparsity and confidence; same-measure bad-event bound only for practical endpoint | direct local parent cards; Mathlib asymptotic/order/measure cards; EXP3 source/scenario; weapons inspiration only | `leanCompiled`; focused/root and `Tests.Basic` builds; eight checks, five exact canaries; baseline axiom audit; independent review found no mathematics error and its two evidence findings are integrated; full repository gate passes | keep the horizon-indexed measures explicit; no anytime single-policy, expected, convergence, first-order, Freedman, or ideal EXP3.P claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-ALL-TIME-CONFIDENCE-TAIL` | fix initial action `Fin.mk 0 hK`, construct a generic measurable successor-selector predictable residual law, prove the forced policy's all-time confidence failure measure is at most `ENNReal.ofReal delta`, and close the all-horizon fixed-best pseudo-regret tail with deterministic forced charge plus explicit telescoping rate | forced decomposition; generic canonical reward condExpKernel transports; `HasCondSubgaussianMGF`; all-time confidence; pathwise width budget; explicit rate | parameterize feature/residual over measurable successor selector; prove strict-past regularity and actual-feature a.e. equality; derive cond-MGF from the environment law; specialize forced selector; combine decomposition and deterministic budgets | terminal theorem: `0<K`, finite decidable nonempty features, `0<lambda`, `0<R`, `0<delta<=1`, `0<=S`, `0<=L2`, action norm bound, `L2<=lambda`, optimal best arm, linear sub-Gaussian environment; arbitrary forced action/window | completed decomposition, history-environment, scheduled confidence, and explicit-rate cards; kernel/conditional-expectation/martingale/integral/sum/order Mathlib cards; Abbasi-Yadkori and Lattimore-Szepesvari | `leanCompiled`; focused/root/Tests pass; twelve checks, five canaries; independent review found no P0-P2; baseline axiom/index/trial/CLI checks and full gate pass | preserve the changed measure; forced rounds remain nonoptimistic and their deterministic charge remains explicit; no expected/stopping/BwK/minimax claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-FORCED-ACTION-CHARGE-BOUND` | bound `blockStartForcedActionSuccessorPseudoRegret` by `(horizon/window+1)*forcedGapBound`, instantiate `forcedGapBound=2*S*sqrt(L2)`, and expose the resulting scalar all-horizon violation budget | forced-policy terminal; filtered Finset cardinality/image/sum APIs; Nat modulo/division; linear gap envelope | contain divisible indices in the quotient-block-multiple image; reconstruct by division; bound image cardinality; sum a pointwise gap ceiling; specialize and compose the event inclusion | count theorem accepts every Nat window; nonnegative gap ceiling; per-forced-arm gap bound; linear specialization uses theta/action norm bounds; terminal inherits the linear sub-Gaussian contracts | completed forced-policy card; finite-sum/finite/order Mathlib cards | `leanCompiled`; focused/root/full Tests; eight checks, five canaries; review no P0-P2 with P3s integrated; baseline axiom audit; trial/index/JSON/Python/diff/CLI/full gates pass | fixed-positive-window charge is linear up to `1/window`; no sublinear claim without a horizon-dependent family, zero-gap forced arms, or another schedule |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-HORIZON-WINDOW-FINITE-HORIZON-TAIL` | for `0<horizon`, instantiate `window=horizon`, prove exactly one forced successor index, and expose a fixed-horizon violation budget with one `2*S*sqrt(L2)` charge | exact forced-policy terminal; Finset singleton/range/filter; Nat modulo facts; linear gap envelope | identify `blockStartForcedIndexSet horizon horizon={0}`; simplify the forced sum; include the fixed-horizon event in the exact forced-charge all-horizon event | positive horizon; inherited linear sub-Gaussian OFUL contracts; policy window equals horizon | completed exact/scalar forced-charge cards; finite-sum/finite/order Mathlib cards | `leanCompiled`; focused/root/full Tests; six checks and five canaries; review no Lean P0/P1/P3 with stale-index P2 closed; baseline axiom audit; index/trial/JSON/Python/diff/CLI/full gates pass | the scalar event's conservative two-envelope threshold has the wrong monotonicity for this sharpening; use the exact event. Horizon changes the policy and measure, so this is not one-policy anytime |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-HORIZON-INDEXED-HIGH-PROBABILITY-PSEUDOREGRET-RATE` | package the one-envelope theorem for a family `forcedActionAtHorizon` and prove the delta tail independently for every positive horizon | compiled horizon-window theorem; named family definitions | expose measure/event apply lemmas; specialize the compiled theorem at each outer horizon | shared model contracts; positive horizon; horizon-dependent forced action schedule | completed horizon-window card; finite-sum/order Mathlib cards | `leanCompiled`; focused/root/Tests pass; five checks and three canaries; review no Lean P0/P1/P3 with stale-index P2 closed; baseline axiom, index/trial/JSON/Python/diff/CLI/full gates pass | distinct horizons have distinct policies/measures; do not union events or claim one-policy anytime control |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-INDEX-COUNT` | define the decidable one-policy forcing predicate and prefix, prove `n+1=2^k` semantics and `card<=Nat.log2 horizon+1` | `Mathlib.Data.Nat.Log`; Finset range/filter/image/card; `Nat.le_log2`; `omega` | use `2^(log2(n+1))=n+1`; embed prefix members in the bounded exponent image; compare cards | deterministic Nat/Finset only | `MLIB-NAT-LOG-POW`; finite/order Mathlib cards | `leanCompiled`; focused/root/Tests pass; seven checks and eight canaries; review fixes and baseline axiom, index/trial/JSON/Python/diff/CLI/full checks pass | preserve successor indexing and logarithmic count; selector, measure transport, decomposition, and final regret remain separate |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-HISTORY-ALGORITHM` | define one history selector forcing `forcedAction (log2(n+1))`, package its deterministic policy, and prove generated action `2^k` equals `forcedAction k` a.e. | parent predicate/count; generic deterministic selector graph; telescoping optimistic selector | measurable if split; Dirac policy; simplify at `2^k-1`; canonical graph transport | `0<K`; finite decidable features; arbitrary deterministic forced arms and history environment | parent local cards; Nat log/power and kernel/integral cards | `leanCompiled`; focused/root Tests pass; seven checks, eight canaries; review P1 closed/P3 integrated; baseline axiom, build/review trials, index/JSON/Python/diff/CLI/full gates pass | preserve one policy/measure; no confidence or regret claim in this leaf |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-PSEUDOREGRET-DECOMPOSITION` | split complete pseudo-regret into initial, forced, and nonforced successor terms and identify the forced term over `powerOfTwoForcedIndexSet` | compiled power-of-two algorithm/count; block-start finite-sum patterns; Finset filter/sum | prove selector branches, transport generated actions, partition successor indices, identify deterministic forced gaps | finite features; generated laws additionally use `0<K`, decidable features, forced arms, arbitrary environment | parent local cards; finite-sum/order/measure cards | `leanCompiled`; focused/root Tests pass; ten checks, eleven canaries; review no P0-P2/P3 integrated; baseline axiom, index, CLI, and full gates pass | keep the exact same-measure decomposition; confidence and scalar tail compile downstream |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-ALL-TIME-CONFIDENCE-TAIL` | prove one-policy all-time confidence and complete all-horizon pseudo-regret tail with deterministic power-of-two forced charge explicit | exact decomposition; generic deterministic-selector residual/confidence; width and initial-gap bounds | specialize source/tail; bound nonforced charge; combine same-measure decomposition; define and bound violation event | full linear sub-Gaussian OFUL contracts; arbitrary forced arms | parent local cards; probability/concentration/sum/order cards | `leanCompiled`; focused/root Tests pass; thirteen checks, seven canaries; review no P0-P2 and two P3s integrated; baseline axiom, index, CLI, and full gates pass | keep forced charge explicit; scalar logarithmic charge is compiled downstream |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-SCALAR-CHARGE-BOUND` | bound the prescribed-arm charge by `(Nat.log2 horizon+1)*forcedGapBound`, specialize to `2*S*sqrt(L2)`, and expose the scalar one-policy all-horizon delta tail | compiled count and explicit-charge terminal; Finset sum/card; linear gap envelope | card-times-ceiling; log2 cast; linear specialization; scalar-event subset; measure monotonicity | generic nonnegative gap ceiling; linear envelope; terminal inherits full linear sub-Gaussian contracts | parent local cards; finite-sum/Nat-log/order/integral cards | `leanCompiled`; focused/root Tests pass; six checks, seven canaries; review no P0-P2 and P3s integrated; baseline axiom, index, CLI, and full gates pass | preserve count, successor indexing, event direction, and same measure; asymptotic rate remains next |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-ASYMPTOTIC-HIGH-PROBABILITY-PSEUDOREGRET-RATE` | name the exact scalar all-horizon budget, prove fixed-model `O(sqrt(T+1)*log(T+1))` growth, and retain the same one-policy event tail | scalar terminal; scheduled expected-rate asymptotics; `Real.log2_le_logb`; Real log/sqrt and Big-O APIs | confidence-log anti-delta; eventual fixed-delta comparison with `1/(T+1)`; telescoping-budget Big-O; log2 cast bridge; additive assembly; definitional event equality | analytic wrappers use finite nonempty features, `0<lambda`, `0<delta`, `0<=L2`; terminal inherits the full one-policy linear sub-Gaussian contracts | parent scalar and expected-asymptotic cards; `MLIB-ASYMPTOTICS`; `MLIB-REAL-LOG-SQRT`; `MLIB-NAT-LOG-POW`; `MLIB-ORDER-ALGEBRA` | `leanCompiled`; focused/root Tests pass; nine checks, eight canaries; review no P0-P2 and both P3s integrated; baseline axiom audit; full gate recorded with leaf evidence | exact finite theorem remains the probability source; no expectation, a.s., minimax, varying-delta, or horizon-dependent-policy claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-VANISHING-AVERAGE-HIGH-PROBABILITY-PSEUDOREGRET-BUDGET` | prove the exact scalar budget is `o(T+1)`, define its quotient, prove it tends to zero, and package normalized regret with the unchanged fixed-delta envelope tail | compiled scalar Big-O terminal; `sqrt_mul_log_succ_isLittleO_natCast_succ`; little-o/Tendsto and positive-division APIs | compose Big-O with the sublinear scale; derive quotient convergence; divide the good-event regret bound by positive `T+1`; reuse nonnegativity and the same named event | analytic wrappers use finite nonempty features, `0<delta`, `0<lambda`, `0<=L2`; terminal inherits the full one-policy linear sub-Gaussian contracts | parent asymptotic and expected-consistency cards; `MLIB-ASYMPTOTICS`; `MLIB-REAL-LOG-SQRT`; `MLIB-ORDER-ALGEBRA` | `leanCompiled`; focused/root/full Tests pass; six checks, six canaries; baseline axiom audit; independent review found no P0-P2 or actionable P3; indexes/CLI/full repository gate pass | fixed delta does not yield convergence in probability; no expected, a.s./Hannan, minimax, varying-delta, or horizon-indexed-policy claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-HIGH-PROBABILITY-AVERAGE-PSEUDOREGRET-CONSISTENCY` | prove pathwise average pseudo-regret convergence outside the existing violation event, name the exact failure set, and bound its outer measure by the same fixed delta | `OFULScheduledPowerOfTwoForcedHighProbabilityAverageRegret`; quotient Tendsto/envelope; fixed-comparator nonnegativity; Mathlib squeeze and outer-measure monotonicity | squeeze normalized regret between zero and the parent budget; include the negated-Tendsto failure set in the violation set; inherit its tail with `measure_mono` and no new union bound | minimal pathwise finite/nonempty-feature and positivity contracts; terminal inherits the full fixed linear sub-Gaussian contracts, fixed `0<delta<=1`, and one horizon-independent forced-arm sequence | parent local card; exact local nonnegativity declaration; Mathlib `squeeze_zero`/`measure_mono`; `MLIB-ASYMPTOTICS`; `MLIB-MEASURE-INTEGRAL`; `MLIB-ORDER-ALGEBRA` | `leanCompiled`; focused/root/Tests pass; four checks/canaries; baseline axiom audit; review P3 outer-measure wording integrated; final gate evidence in obligation/trials | fixed-confidence outer-measure tail only; no convergence-in-probability, probability-one/a.s./Hannan, expected, varying-delta, or horizon-indexed-policy claim; later ordinary-probability use requires failure-set measurability |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-PSEUDOREGRET-DECOMPOSITION` | off forced indices identify the modified selector and generated successor with telescoping OFUL; split complete pseudo-regret into initial, forced, and nonforced sums; identify the forced sum a.e. with deterministic `forcedAction (n/window)` gaps; on the all-time confidence event bound complete regret by forced and nonforced scheduled charges under the modified measure | concrete forced-policy parent; `finiteHistoryScalarRidgeOptimisticAction_gap_le`; finite-history/trajectory alignment; confidence failure sets; `ae_all_iff`; `Finset.sum_range_succ'`; filtered-sum partition and monotonicity | unfold both branches; transport the canonical selector graph; split action zero; filter successors by modulo; identify forced actions by finite sum congruence; prove a policy-parametric pathwise confidence-gap lemma; sum over nonforced indices; recombine | exact split needs finite features only; confidence consumer uses `0<K`, finite decidable nonempty features, `0<lambda`, arbitrary forced action/window/environment, and exclusion from the named failure event; no positive window/delta/R/S contract for the split | parent concrete-policy and scheduled-confidence local cards; finite-sum/order/measure/kernel Mathlib cards; Abbasi-Yadkori and Lattimore-Szepesvari | `leanCompiled`; focused/root/Tests pass; thirteen checks, five typed canaries, review fixes, baseline axiom, route/index/trial/CLI checks, and full repository gate pass | consumed downstream by the changed-policy confidence and all-horizon tail; forced charge remains explicit |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-HISTORY-ALGORITHM-ACTION-COST-PRODUCER` | define the concrete fully specified selector that forces `forcedAction (n/window)` at divisible history indices, prove its deterministic policy and canonical successor-action graph, and produce aligned positive action costs under its own trajectory law | prior conditional selector leaf; `HistoryAlgorithm`; deterministic kernels; canonical process/condDistrib-to-compProd APIs; `ae_compProd_of_ae_ae`; `ae_map_iff`; Nat modulo/division and interval arithmetic | compile generic deterministic selector algorithm and graph; branch measurably on `n%window`; simplify at `block*window`; transport generated forced actions; choose witness `block*window+1` | `0<K`; finite decidable features; generic graph uses Standard Borel and `MeasurableEq` (which supplies singleton measurability); deterministic forced arms/costs; `2<=window`; positive forced costs; arbitrary history environment | prior forced-selector and measurable-recursive-selection cards; kernel/integral/finite/order cards; OFUL sources locate selector only | `leanCompiled`; focused/root/full Tests, eleven checks, eleven typed canaries; review no P0-P2 with three P3 fixes integrated; baseline axiom audit; route/global retrieval, Python/JSON/trial/CLI/placeholder/diff/full gates pass | changed policy measure invalidates direct reuse of ordinary OFUL regret; next prove off-forced optimistic equality and a finite-horizon regret split with explicit forced-round charge; no full BwK/primal-dual claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BLOCK-START-FORCED-POSITIVE-ACTION-COST-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | expose the exact telescoping strict-fold selector, identify generated successor actions with it a.e., and conditionally derive the aligned positive-action-cost contract and full budget-exhaustion OFUL terminal from block-start forced arms | a.e. aligned-action-cost parent; finite-history scheduled selector; deterministic optimistic-policy Dirac law; canonical selector graph; `Preorder.frestrictLe`; `Finset.mem_Ico`; `Nat.add_mul`; `omega` | name selector; expose Dirac section; transport generated action `n+1`; use witness `block*window+1`; rewrite selector to forced arm; feed parent terminal unchanged | inherited canonical OFUL contracts; deterministic Nat action costs; `2<=window`; selector equals `forcedAction block` for every block-start finite history; positive forced-arm costs | parent local card; measurable recursive selection; kernel/integral/sum/order cards; OFUL sources; resource/BwK adjacent only | `leanCompiled`; focused/root/full Tests; six checks and six typed canaries; review no P0-P2 and stale-index-status P3 corrected; baseline axiom audit; memory/index/retrieval/Python/JSON/trial/CLI/placeholder/full gates pass | forced equality is not implied by ordinary OFUL argmax; executable forced exploration needs a modified scheduled algorithm and separate forced-round regret charge; no full BwK/sliding/stochastic-cost claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-AE-ALIGNED-WINDOW-POSITIVE-ACTION-COST-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | under the canonical measure, turn an a.e. deterministic reach bound into square-integrable budget exhaustion and a numerical OFUL terminal; specialize to deterministic action costs when almost every trajectory contains one positive-cost selected action in every aligned block | positive-action-cost and aligned-window parents; `MemLp.of_bound`; `integral_mono_ae`; `hittingAfter_le_of_mem`; `ae_all_iff`; `Finset.single_le_sum`; exact-second-moment OFUL terminal | construct a.e. finite/L2 stopping contract; integrate the a.e. square bound; transport a.e. resource reach; convert per-block a.e. evidence to one all-block set; derive positive block sums; apply aligned-window growth to each fixed good trajectory; specialize at `budget*window` | inherited canonical OFUL contracts; deterministic Nat action costs; `forallᵐ trajectory, forall block, exists` positive selected cost, equivalent to per-block a.e. evidence; no off-support bound, per-round positivity, independence, upper bound, or reward-cost coupling | both parent local cards; measure/stochastic/variance, finite-sum, and order Mathlib cards; OFUL sources; resource/BwK adjacent only | `leanCompiled`; root imported; focused/root/full Tests; eleven checks and eleven typed canaries; review no P0-P2 and zero-edge P3 corrected; baseline axiom audit; memory/index/retrieval/Python/trial/CLI/placeholder/full gates pass | preserve `budget*window`; use the countable-intersection adapter for per-block producers; ordinary OFUL does not produce the schedule; no sliding/expected-cost inference or full BwK/optional-stopping/asymptotic claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-CUMULATIVE-ALIGNED-WINDOW-POSITIVE-COST-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | separate threshold `budget` from `reachHorizon`, compile the generic stopping/moment/OFUL consumer, prove `block<=cumulativeSpent cost (block*window)` from aligned-block cost at least one, and expose the terminal with reach horizon `budget*window` | parent cumulative-positive-cost route; `hittingAfter_le_of_mem`; bounded stopping/moment APIs; exact-second-moment OFUL terminal; `Finset.sum_range_add_sum_Ico`; Nat order/multiplication | exhibit arbitrary reach horizon in the hitting set; construct square integrability and moment bound; split cumulative prefixes by aligned `Ico` blocks and induct; specialize at budget; preserve parent terminal | inherited canonical OFUL contracts; adapted Nat per-round cost; pathwise cost at least one on every aligned half-open block; no per-round positivity, positive-window premise, caller reach/moment, independence, upper bound, or reward-cost coupling | parent local card; measure/stochastic/variance, finite-sum, and order Mathlib cards; OFUL sources; resource/BwK adjacent only | `leanCompiled`; root imported; focused/root/full Tests; seven checks and seven typed external canaries; review no P0-P2 with both P3s corrected; baseline axiom audit; indexes/CLI/placeholder/full gate pass | preserve aligned blocks and `budget*window`; no sliding-window or expected-cost inference; stochastic drift/tail, action-model, and BwK routes need separate contracts |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-POSITIVE-ACTION-COST-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | evaluate deterministic `actionCost : Fin K -> Nat` at the current canonical trajectory action, expose its half-open cumulative sum, and specialize the same scheduled OFUL budget-exhaustion expected-regret/tail theorem | parent cumulative-positive-cost terminal; canonical all-round coordinate theorem; `measurable_fst`; `measurable_of_countable` | compose current-coordinate measurability with first projection and finite-domain cost; lift arm positivity; reuse cumulative adaptedness, unit growth, and the parent terminal unchanged | inherited canonical OFUL contracts; action-only time-homogeneous Nat cost; armwise `1<=actionCost`; no caller adaptedness, reach, moment, cost upper bound, independence, or reward-cost coupling | parent local card; `MLIB-MEASURE-INTEGRAL`; `MLIB-MARTINGALE-STOCHASTIC`; `MLIB-FINTYPE-FIN`; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; OFUL sources; resource/BwK adjacent only | `leanCompiled`; root imported; focused/root/full Tests; eight checks and seven external canaries; review no P0-P2 with both P3s corrected; baseline axiom audit; indexes/CLI/placeholder/full gate pass | preserve current-action timing, half-open indexing, and strict positivity; zero-cost, time-varying, or history-dependent costs need separate routes; no general resource/BwK, optional-stopping, asymptotic, minimax, or changed event/measure claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-CUMULATIVE-POSITIVE-COST-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | define `cumulativeSpent cost t = sum s in range t, cost s`, prove its zero/successor semantics and adaptedness, derive unit growth from `1<=cost`, then expose the same canonical scheduled OFUL budget-exhaustion expected-regret/tail theorem | parent unit-growth terminal; `Finset.range`; `Finset.sum_range_succ`; `Finset.measurable_sum`; `Adapted.measurable_le`; `Nat.add_le_add_left` | lift each earlier cost from `F s` to `F t`, close the prefix sum, use positive successor cost for unit growth, and reuse the parent terminal unchanged | inherited canonical OFUL contracts; adapted Nat-valued per-round cost; pathwise `1<=cost`; half-open completed-round indexing; no cost upper bound, independence, or reward-cost coupling | parent unit-growth card; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; measure/stochastic cards; OFUL source placement; resource/BwK adjacent only; weapons inspiration only | `leanCompiled`; root imported; focused/root/full Tests; six checks and five external canaries; review no P0-P2 and stale-status P3 corrected; baseline axiom audit; indexes/CLI/placeholder/full gate pass | preserve half-open indexing and positive costs; nonnegative costs do not imply reach; zero-cost models need lower-rate/window-growth or probabilistic reach; no general resource/BwK, optional-stopping, asymptotic, minimax, or changed event/measure claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNIT-GROWTH-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | replace the explicit reach premise by pathwise `spent t omega+1<=spent (t+1) omega`, derive `t<=spent t omega`, then expose the same bounded hitting time, square-integrable contract, `(budget+1)^2` exact moment bound, and canonical scheduled OFUL expected-regret/tail theorem | prior budget-exhaustion terminal; `Nat.zero_le`; `Nat.succ_le_succ`; `le_trans` | Nat induction gives the index lower bound; specialize at budget; reuse the parent stopping/moment/terminal route unchanged | inherited canonical OFUL contracts; adapted Nat-valued `spent`; pathwise unit growth; no initial-value or separate reach premise | parent budget-exhaustion card; `MLIB-ORDER-ALGEBRA`; inherited measure/stochastic/variance cards; Abbasi-Yadkori and linear scenario; resource/BwK adjacent only; weapons inspiration only | `leanCompiled`; root imported; focused/root/full Tests; five checks and five external canaries; review no P0-P2 and both P3s corrected; pure producer axiom-free; indexes/CLI/full gate pass | preserve unit growth; ordinary monotonicity does not imply reach; if unavailable, use a lower-rate growth or tail/drift route; no BwK, primal-dual, optional stopping, asymptotic, minimax, or changed event/measure claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BUDGET-EXHAUSTION-EXPECTED-PSEUDOREGRET-RATE` | for `tau = Budget.budgetExhaustionTime spent budget`, prove `tau<=budget`, construct the square-integrable finite-stopping contract, bound its exact round second moment by `(budget+1)^2`, and specialize the canonical scheduled OFUL expected-regret/tail theorem | `BudgetStoppingTime`; exact-second-moment OFUL terminal; `hittingAfter_le_of_mem`; `IsStoppingTime.measurable'`; `Measurable.untopA`; `MemLp.of_bound`; `integral_mono`; `integral_const`; `Real.sqrt_sq` | use pathwise membership at index `budget` to bound the hitting time; derive finiteness/measurability/L2 from the deterministic bound; integrate the squared round bound; feed it to the prior canonical consumer | inherited canonical OFUL contracts; adapted Nat-valued `spent`; pointwise `budget<=spent budget trajectory`; no monotonicity needed after reach is supplied | exact-moment and budget-stopping local cards; Mathlib measure/stochastic/variance/order cards; Abbasi-Yadkori and linear-bandit sources; resource-constrained/BwK cards adjacent only; weapons inspiration only | `leanCompiled`; root imported; focused/root/full Tests; six checks and five external canaries; review no P0-P2 with all P3s corrected; baseline axiom audit; indexes/CLI/full gate pass | preserve reach as an explicit regularity contract; without it allow `tau=top` and open a separate tail/drift route; no BwK, primal-dual, optional stopping, third moment, asymptotic, minimax, or changed event/measure claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNBOUNDED-STOPPING-TIME-EXACT-SECOND-MOMENT-EXPECTED-PSEUDOREGRET-RATE` | under `SquareIntegrableFiniteStoppingTime`, name the actual integral of `(tau.untopA+1)^2` and state the canonical stopped expected-regret theorem directly with this exact second moment, without a separate moment parameter or upper-bound premise | prior explicit-second-moment theorem; `SquareIntegrableFiniteStoppingTime`; `integral_nonneg`; `sq_nonneg` | define the contract-qualified `stoppingTimeRoundSecondMoment`; prove nonnegativity; instantiate the prior theorem at the exact integral and discharge its upper-bound premise by reflexivity | exactly the inherited canonical OFUL and square-integrable stopping contracts; no caller-supplied numeric moment bound or budget-integrability premise | parent explicit-second-moment card; Mathlib measure/stochastic/log/order cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; three checks and two external canaries; review P2 corrected and follow-up found no P0-P2; baseline axiom audit; indexes/CLI/full gate | preserve the named exact moment and same event/measure; no generic non-integrable moment claim, reintroduced moment parameter, expected budget, third moment, bounded horizon, optional stopping, or numerical/asymptotic overclaim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNBOUNDED-STOPPING-TIME-EXPLICIT-SECOND-MOMENT-EXPECTED-PSEUDOREGRET-RATE` | replace the expected stopped explicit budget by `telescopingHighProbabilityPseudoRegretQuadraticCoefficient * roundSecondMoment`, yielding a fully explicit second-moment expected-regret bound with the same stopped-event tail | prior closed square-integrable theorem; quadratic pointwise budget envelope; automatic budget integrability; `MemLp.integrable_sq`; `integral_mono`; `integral_mul_const` | integrate both sides of the quadratic envelope; rewrite the dominating integral; multiply the supplied second-moment bound by the nonnegative coefficient; substitute into the canonical terminal theorem | exactly the inherited canonical OFUL and square-integrable stopping contracts; supplied second-moment upper bound; no budget-integrability premise | parent closed-budget card; Mathlib measure/stochastic/log/order cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; two checks and two external canaries; independent review; baseline axiom audit; indexes/CLI/full gate | preserve the explicit coefficient-times-moment target and same event/measure; no retreat to expected budget, third moment, bounded horizon, optional stopping, or unconditional arbitrary-stopping asymptotic |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNBOUNDED-STOPPING-TIME-SQUARE-INTEGRABLE-CLOSED-EXPECTED-PSEUDOREGRET-RATE` | under the existing square-integrable stopping contract, derive stopped explicit-budget integrability automatically and expose the same canonical expected-regret/tail theorem without a caller-supplied integrability premise | prior square-integrable terminal theorem; `standardScalarLogDetBudget`; stopped-budget measurability; `Real.log_le_sub_one_of_pos`; sqrt monotonicity/product identities; `MemLp.integrable_sq`; `Integrable.mul_const`; `Integrable.mono'` | prove linear log-det and quadratic telescoping-log bounds; assemble a parameter-only quadratic budget envelope; dominate the stopped budget by `rounds^2*coefficient`; reuse the prior terminal theorem | inherited OFUL contracts; stopping time; `tau!=top` a.e.; `MemLp 2` round count; supplied second-moment upper bound; no separate stopped-budget integrability premise | parent square-integrable rate card; Mathlib log/sqrt/order/measure/stochastic-process cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; seven checks and five external canaries; independent review; baseline axiom audit; indexes/CLI/full gate | preserve the quadratic envelope and same event/measure; no third moment, bounded horizon, optional stopping, or asymptotic substitution; audit log/sqrt orientation and absolute-value domination before changing assumptions |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNBOUNDED-STOPPING-TIME-SQUARE-INTEGRABLE-EXPECTED-PSEUDOREGRET-RATE` | under `L2` regularity and a supplied round-count second-moment bound, expected stopped pseudo-regret is nonnegative and at most expected stopped budget plus `standardScalarInitialGapBound*Sqrt(secondMoment)*sqrt(delta)`; the same stopped event keeps its `ENNReal.ofReal delta` tail | unbounded exact decomposition; `MemLp.integrable`; `integral_mul_le_Lp_mul_Lq_of_nonneg`; `memLp_indicator_const`; `integral_indicator_one`; `Real.sqrt_eq_rpow`; ENNReal-to-real tail conversion | derive the `L1` stopping contract; specialize Holder at `2,2`; rewrite the random envelope as round count times initial-gap bound; use second-moment and event-probability sqrt monotonicity; reuse exact decomposition and unchanged tail | inherited OFUL contracts; stopping time; `tau!=top` a.e.; `MemLp 2` round count; second-moment integral upper bound; separately integrable stopped explicit budget | parent unbounded decomposition card; Mathlib measure/stochastic-process cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; five checks and five external canaries; review found no P0-P2 and all P3s are corrected; baseline axiom audit; indexes/CLI/full gate | preserve same event and measure; no optional stopping, independence, or first-moment product shortcut; audit indicator/rpow/tail conversion before changing assumptions |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-UNBOUNDED-STOPPING-TIME-EXPECTED-PSEUDOREGRET-DECOMPOSITION` | for an arbitrary canonical stopping time, expected complete fixed-best stopped pseudo-regret is nonnegative and at most expected stopped explicit budget plus the expected random-horizon envelope on the stopped violation event; the same event has measure `<= ENNReal.ofReal delta` | bounded-stopping expectation definitions; arbitrary-`tau` stopped-event tail; Mathlib `measurable_stoppedValue`; `Integrable.mono'`; indicator and Bochner integral APIs | package a.e. finite/integrable round count; expose random-horizon envelope; lift stopped values to ambient measurability; prove stopped-regret integrability; split on the measurable bad event; integrate; reuse unchanged tail | inherited OFUL contracts; stopping time; `tau!=top` a.e.; integrable `tau.untopA+1`; separately integrable stopped explicit budget | local bounded-stopping and arbitrary-`tau` tail cards; Mathlib measure/stochastic-process cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; nine checks and eight external canaries; review P2 resolved; baseline axiom audit; indexes/CLI/full gate | preserve exact overflow integral; no optional stopping and no invalid `E[X 1_B] <= E[X]P(B)`; a delta-only overflow rate needs second moment/Holder or tail summability |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BOUNDED-STOPPING-TIME-EXPECTED-AVERAGE-PSEUDOREGRET-CONSISTENCY` | for fixed model parameters and a horizon-indexed canonical stopping family `tau_T<=T`, the exact named expected stopped pseudo-regret divided by `T+1` tends to zero | scheduled bounded-stopping asymptotics; fixed-window consistency module; `sqrt_mul_log_succ_isLittleO_natCast_succ`; `IsBigO.trans_isLittleO`; `IsLittleO.tendsto_div_nhds_zero` | compose the explicit-bound and named-family Big-O theorems with the compiled analytic little-o bridge; define the normalized integral; apply little-o division convergence | inherited fixed OFUL model contracts; optimal fixed arm; linear sub-Gaussian environment law; for every horizon, stopping time on canonical all-round filtration and pointwise `tau_T<=T` | scheduled asymptotic and fixed-window consistency local cards; exact declaration retrieval; Mathlib asymptotics/log cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; four checks; four external canaries; review no P0-P3; baseline axiom audit; indexes/CLI/full gate | preserve horizon-tuned `delta_T=1/(T+1)`, exact integral, denominator, and `tau T`; no pathwise/probability/almost-sure, one-policy anytime, unbounded-stopping, minimax, or complete-OFUL claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BOUNDED-STOPPING-TIME-ASYMPTOTIC-EXPECTED-PSEUDOREGRET-RATE` | for fixed model parameters and a horizon-indexed canonical stopping family `tau_T<=T`, the named expected stopped pseudo-regret is `O(sqrt(T+1)*log(T+1))` | scheduled explicit expected-rate module; fixed-window asymptotic APIs; `Asymptotics.isBigO_iff`; `IsBigO.add/mul/sqrt/trans`; `Real.log_mul/log_pow/log_le_log`; `Filter.atTop` | prove `T+2<=(T+1)^2` eventually; bound the scheduled confidence log by `log(T+1)`; add determinant budget; assemble explicit bound; transfer through pointwise nonnegativity | inherited fixed OFUL model contracts; optimal fixed arm; linear sub-Gaussian environment law; for every horizon, stopping time on canonical all-round filtration and pointwise `tau_T<=T` | scheduled explicit-rate and fixed-window asymptotic local cards; Mathlib asymptotics/log/order cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; four checks; four external canaries; review with both P3 gaps resolved; baseline axiom audit; indexes/CLI/full gate | preserve exact scheduled log and horizon-indexed policy family; no one-policy anytime, unbounded stopping, little-o, expected-average consistency, pathwise/probability convergence, minimax, or complete-OFUL claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BOUNDED-STOPPING-TIME-EXPLICIT-EXPECTED-PSEUDOREGRET-RATE` | with outer budget `delta_T=1/(T+1)`, expected complete fixed-best pseudo-regret stopped at any canonical `tau_T<=T` is nonnegative and bounded by `4*S*sqrt(L2)+2*(R*sqrt(B_T+2*log((T+1)^2*(T+2)))+sqrt(lambda)*S)*(sqrt(T+1)*sqrt(2*B_T))`; also expose a named horizon-indexed family | `OFULExpectedRegretRate`; scheduled bounded-stopping expectation; `standardExpectedRegretDelta`; exact envelope charge; `Real.log`; `Real.sqrt`; `field_simp`; `ring`; `stoppedValue` | normalize the scheduled confidence share exactly; identify endpoint plus one initial-gap charge with the explicit expression; instantiate the bounded-stopping expectation theorem; package the horizon family | inherited OFUL contracts; optimal fixed arm; linear sub-Gaussian environment law; for every horizon, stopping time on the canonical all-round filtration and pointwise `tau_T<=T` | bounded-stopping expectation and fixed-window expected-rate cards; targeted declaration search; Mathlib log/sqrt/order/measure cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; seven checks; five external canaries; review with both P3 test gaps resolved; baseline axiom audit; indexes/CLI/full gate | preserve horizon-tuned policy and exact `(T+1)^2*(T+2)` scale; no fixed-window substitution, optional stopping, new union bound, unbounded time, Big-O, consistency, minimax, or complete-OFUL claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BOUNDED-STOPPING-TIME-EXPECTED-PSEUDOREGRET-RATE` | on the same scheduled-policy measure, expected complete fixed-best pseudo-regret stopped at `tau<=maxHorizon` is nonnegative and at most `telescopingHighProbabilityPseudoRegretBound ... maxHorizon + standardScalarAllRoundGapEnvelope ... maxHorizon * delta` | `OFULExpectedRegret`; bounded stopped-event tail; explicit log/rate; envelope; `stoppedValue`; `stronglyMeasurable_stoppedValue_of_le`; `Integrable.of_bound`; indicator integration; `Measure.real` | prove explicit log/rate and envelope horizon-monotone; convert the finite `WithTop Nat` bound; bound absolute stopped regret; obtain integrability; split the integral on the stopped violation event; reuse its delta tail | inherited OFUL contracts; `IsOptimalLinearArm`; `CanonicalLinearSubgaussianEnvironmentLaw`; stopping time on the all-round filtration; deterministic pointwise bound `tau<=maxHorizon` | stopped high-probability and finite-window expected-regret local cards; stopping-time adjacency; Mathlib measure/log/sqrt/order cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; root imported; focused/root/full Tests; nine checks; six external canaries; review with resolved P3s; baseline axiom audit; indexes/CLI/full gate | preserve same policy/event and endpoint budget; no optional stopping, new union bound, finite supremum, unbounded stopping time, asymptotic, minimax, or complete-OFUL claim |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-BOUNDED-STOPPING-TIME-HIGH-PROBABILITY-PSEUDOREGRET-RATE` | for a canonical all-round stopping time `tau` bounded by `maxHorizon`, stopped complete fixed-best pseudo-regret is nonnegative, its explicit-rate violation event is measurable at `maxHorizon`, and its measure is at most `ENNReal.ofReal delta` on the same scheduled policy | explicit all-horizon rate; `Filtration.piLE`; `frestrictLe`; `StronglyAdapted`; `ProgMeasurable`; Mathlib `stoppedValue` and `stronglyMeasurable_stoppedValue_of_le`; `measure_mono` | prove finite-prefix pseudo-regret measurable and strongly adapted; prove deterministic budget adapted; obtain bounded stopped-value measurability; include the stopped event in the all-horizon event with witness `tau.untopA`; transport the parent tail | inherited OFUL model contracts; `IsStoppingTime` for the canonical all-round filtration; deterministic pointwise bound `tau<=maxHorizon` | explicit all-horizon and scheduled all-round local cards; local budget stopping-time card as adjacent evidence; Mathlib martingale/measure/finite-sum/order cards; Abbasi-Yadkori; linear scenario; weapon inspiration only | `leanCompiled`; focused/root/full Tests; thirteen checks; coordinate/stopped-value/finite-`untopA`/subset/measurability/terminal canaries; independent review; baseline axiom audit; indexes/CLI/full gate | same policy/exact budget/complete range; bound required for measurable stopped event; no optional stopping, new union bound, or unbounded-time claim; expected consumer compiles |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-EXPLICIT-ALL-HORIZON-HIGH-PROBABILITY-PSEUDOREGRET-RATE` | fixed-best pseudo-regret is nonnegative for every finite horizon, and the event `exists T, explicit scheduled bound T < complete pseudoRegret T` with confidence log `B_T+2*log(((T+1)*(T+2))/delta)` has measure at most `ENNReal.ofReal delta` for one telescoping-schedule policy | `OFULScheduledAllHorizonAllRoundGap`; finite-window explicit high-probability rate; telescoping delta identity; abstract scheduled event/tail | rewrite `allTimeTelescopingDelta`; use outer budget `delta/(T+2)` in the finite-window normalization; prove pointwise budget equality; identify explicit and abstract existential events; transport terminal tail | `0<K`; finite decidable nonempty Feature; `0<lambda`; `0<R`; `0<delta<=1`; `0<=S`; `0<=L2`; arm norm ceiling; `L2<=lambda`; `IsOptimalLinearArm`; `CanonicalLinearSubgaussianEnvironmentLaw` | scheduled all-round, finite-window explicit-rate, and scheduled cumulative local cards; Mathlib log/sqrt/finite-sum/order/measure cards; Abbasi-Yadkori paper; linear scenario; weapon inspiration only | `leanCompiled`; focused/root/full Tests; nine public checks; external exact-log, schedule, scalar-budget, event-equality, and terminal canaries; independent review; baseline axiom audit; indexes/CLI/full gate | preserve one policy and exact `(T+1)*(T+2)` factor; no retuning, horizon-indexed policy, extra cumulative-horizon union bound, or direct stopping-time/expectation/minimax claim; bounded tail and expected consumers compile |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-ALL-HORIZON-ALL-ROUND-PSEUDOREGRET-TAIL` | fixed-best pseudo-regret is nonnegative for every finite horizon, and the event `exists horizon, scheduled initial-plus-radius-width bound horizon < complete pseudo-regret horizon` has measure at most `ENNReal.ofReal delta` for one telescoping-schedule policy | `OFULScheduledAllHorizonCumulativeGap`; `OFULHighProbabilityRegretRate`; scheduled action-zero law; initial-gap Cauchy envelope; fixed-best nonnegativity; `Finset.sum_range_succ'`; `measure_mono_ae` | transport time-zero action on the same measure; charge `2*S*sqrt(L2)`; split the complete range into time zero plus successors; reuse the same-horizon successor event; specialize to a certified optimal arm | `0<K`; finite decidable nonempty Feature; `0<lambda`; `0<R`; `0<delta<=1`; `0<=S`; `0<=L2`; arm norm ceiling; `L2<=lambda`; `IsOptimalLinearArm`; `CanonicalLinearSubgaussianEnvironmentLaw` | scheduled successor, fixed-window all-round, fixed-window high-probability pseudo-regret, and scheduled environment-law local cards; Mathlib finite sums/order/convex-linear-algebra/measure cards; Abbasi-Yadkori paper; linear scenario; weapon inspiration only | `leanCompiled`; focused and Tests.Basic builds; root import; external scheduled-initial, generic inclusion, generic measure, event-rfl, and full-terminal canaries; repository gate passed | no horizon-dependent policy or extra cumulative-horizon union bound beyond the upstream telescoping time union; exact complete range required; explicit scheduled-rate, bounded stopping-time, and expected consumers compile |

| Problem id | Area | Target | Current status | Next leaf |
| --- | --- | --- | --- | --- |
| `BRL-OP-UCB-MATHLIB-001` | stochastic bandit | UCB regret bound compatible with LML | local faithful theorem, fresh canonical-kernel producer, explicit deterministic policy, stationary selected-reward laws, and expected-average terminal compiled | native Real index/history, tails/counts/exact regret, trajectory uniqueness, split-law composition, `Kernel.trajMeasure`, generated `realHistoryNextArm`, adaptive next-unused selected-reward identification, and same-process expected-average consistency compile. Remaining work is only an actual compatible imported-LML symbol if literal upstream consumption is required |
| `BRL-OP-ETC-SUBGAUSS-001` | stochastic bandit | ETC wrong-commit probability and regret route | local faithful theorem compiled | native Real exact concentration/counts/sum, selected feedback-law transport, least-encoded tie/action assembly, source-shaped `empMean'` mapping, and a faithful local `IsAlgEnvSeq`-field bundle theorem now compile. Remaining work is only a true cross-toolchain import over the actual LML symbols; the upstream declaration is not imported |
| `BRL-OP-TS-BAYES-001` | Bayesian bandit | Thompson sampling Bayesian regret | local stationary theorem compiled | canonical/reference samplers, recursive density, global prior-mixture probability matching, clipped-UCB decomposition, both concentration expectations, and the stationary final bound `(2*K+1)*(u-l)+8*sqrt(sigma2*K*n*log n)` compile. Remaining work is literal LML symbol import or an explicitly stated nonstationary/contextual adapter |
| `BRL-OP-EXP3-ADVERSARIAL-001` | adversarial bandit | EXP3 expected regret | the generated predictable-trajectory route compiles through adaptive moments, integrability, the unoptimized bound, deterministic tuning, realized selected-loss transport, and the all-horizon clipped-rate `min(T,4*sqrt(|A|*T*log|A|))` theorem | next choose one narrow extension such as high-probability regret, stochastic rewards, or a broader adversary contract without reopening the compiled expectation-law route |
| `BRL-OP-CONTEXTUAL-001` | contextual bandit | finite contextual bandit regret interface | planned | define context/action/reward model |
| `BRL-OP-OFUL-LINEAR-001` | linear bandit | OFUL confidence and regret route | deterministic elliptical potential, common-`R` vector self-normalized concentration, scalar-ridge confidence and optimism, one-process all-time telescoping confidence, a scheduled generated one-policy all-time confidence and concrete environment-law producer, scheduled all-horizon complete fixed-best pseudo-regret tail, measurable generated finite-window reward-law transport, normalized all-round cumulative-gap tail, explicit finite-window and all-horizon high-probability rates, finite-window expected pseudo-regret and asymptotics, bounded stopping-time event evaluation, generic bounded stopping-time expectation, its standard-delta explicit finite-horizon expected rate, fixed-model bounded-stopping family Big-O and expected-average convergence, the exact unbounded-stopping decomposition, square-integrable `sqrt(delta)` overflow control, automatic stopped-budget integrability, and the fully explicit second-moment unbounded-stopping rate compile | next select a concrete stopping rule/family and prove its round-second-moment contract; keep unconditional arbitrary-stopping, pathwise/probability/almost-sure, optional-stopping, and minimax claims separate |
| `BRL-OP-RL-BELLMAN-001` | finite-horizon RL | Bellman/value/regret interface | finite MDP, deterministic confidence/regret consumers, empirical model, fixed-policy iid batches, simultaneous/all-coordinate confidence, offline multibatch regret, adaptive Ionescu--Tulcea laws, a measurable known-reward empirical optimistic source, explicit selected-path reachability, accumulated cross-round count confidence, and a closed-form capped inverse-square-root recommendation-regret terminal compile | next instantiate/optimize the explicit budget/scale parameters, then separately connect behavior or recommendation regret to realized online regret; complete UCB-VI remains separate |
| `BRL-OP-CONCENTRATION-001` | concentration | reusable Hoeffding/sub-Gaussian/variance cards | partial compiled routes | `TAIL-HOEFFDING-BOUNDED`, `TAIL-SUBGAUSS-SUM`, `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`, `TAIL-COND-SUBGAUSS`, `TAIL-VARIANCE-ROBUST`, fixed-tilt predictable compensation, quadratic delta optimization, and a consumed finite-prefix maximal union route compile; next work is a new model's one-step MGF producer or a sharper Ville/mixture anytime theorem, not another import-only wrapper |
| `BRL-OP-TSALLIS-FTRL-001` | best-of-both-worlds bandit | Tsallis-INF/FTRL formalization route | generated regret, refined stability/penalty/tuning/window transport, square-root schedule, finite-arm IID stochastic rewards, history-adaptive corrupted log regret, a coefficient-aware model-level endpoint, all-regimes deterministic boost families, and arbitrary measurable predictable history-arm-gated boosts compile | strengthen beyond deterministic full-schedule envelope budgets, or formalize current-action/latent-law corruption, before claiming the broader paper theorem |

## Closed Theorem Route: OFUL Elliptical Potential

`LOCAL-LEAF-OFUL-STANDARD-LOG-ELLIPTICAL-POTENTIAL-FOUNDATION` packages the
terminal determinant bound and clipped inverse-quadratic finite-sum bound in
the standard logarithmic OFUL shape. Its contract is deterministic:
finite-dimensional real features, positive scalar regularization, and a
uniform squared-feature norm ceiling.

The vector self-normalized theorem, finite-horizon least-squares
confidence-ellipsoid consumer, scalar `V_0=lambda I` bias adapter, and
fixed-horizon finite-action optimism theorem now compile. The optimism route
contains the weighted dual-norm inequality, finite score argmax, one-step
gap certificate, and violation probability bound.

The next blocker is a measurable deterministic tie-breaker and recursive
selected-action/feature alignment, not more determinant, bias, or pointwise
optimism bookkeeping. Uniform-time confidence, selected-width summation, and
OFUL regret remain open.

## Compiled Leaf: OFUL Fixed-Direction Compensated MGF

`LOCAL-LEAF-OFUL-FIXED-DIRECTION-COMPENSATED-MGF` compiles the
deterministic-horizon fixed-direction precursor used by the method of
mixtures. For predictable projections `a_i = theta dot x_i` and
conditionally sub-Gaussian noise `eta_i`, it exposes a zero-budget
`HasMGFUpperBoundAt` certificate for
`sum_(i<n) (a_i*eta_i-c_i*a_i^2/2)`.
For the paper's common scale, instantiate `c_i=R^2` and
`a_i=(lambda dot x_i)/R` before mixing `lambda ~ N(0,V_0^{-1})`.

The proof freezes `a_i` in each conditional kernel using the local
`condExpKernel.map = dirac` API, derives exponential integrability from a
deterministic projection bound, and invokes the compiled finite conditional
MGF composition route.

`LOCAL-LEAF-OFUL-DIAGONAL-GAUSSIAN-QUADRATIC-EXPONENTIAL` now compiles the
diagonal-coordinate calculation intended for later eigenbasis transport. It
completes the scalar square under
`gaussianReal 0 1`, factors the finite product integral, and collects the
answer as the inverse square root of `det (diagonal (1+q))` times the
inverse-diagonal score quadratic exponential. Its contract is exactly
coordinatewise `0 <= q_i`; it does not assert that an arbitrary PSD matrix is
already diagonal.

`LOCAL-LEAF-OFUL-PSD-GAUSSIAN-QUADRATIC-EXPONENTIAL` now compiles that
orthonormal spectral transport for every real PSD `A`. It rewrites the
`stdGaussian` integral of `exp(<score,z>-<z,A z>/2)` as
`sqrt(det(1+A))^-1 * exp(score^T(1+A)^-1 score/2)`, with no caller
integrability or measurability premise.

`LOCAL-LEAF-OFUL-POSDEF-COVARIANCE-GAUSSIAN-QUADRATIC-EXPONENTIAL` now
transports that identity to `N(0,V_0^-1)` for arbitrary positive-definite
`V_0` and PSD `G`. Its paper-shaped endpoint is
`sqrt(det V_0 / det(V_0+G)) *
  exp(score^T(V_0+G)^-1 score/2)`.

`LOCAL-LEAF-OFUL-GAUSSIAN-MIXTURE-JOINT-MEASURABILITY-TONELLI` now compiles
the product-space layer for measurable random scores and coordinatewise
measurable random Gram matrices. Its `ENNReal` quadratic exponential is
jointly measurable, and its product lintegral equals the iterated lintegral
for every `SFinite` parameter law, including `N(0,V_0^-1)`.

`LOCAL-LEAF-OFUL-FINITE-HORIZON-SCORE-GRAM-EXPECTATION-TRANSPORT` now compiles
the random `S_n` and variance-weighted `G_n`, proves `G_n.PosSemidef`, matches
the fixed-direction exponent pointwise, derives the real expectation bound,
and averages it through arbitrary probability direction laws and
`N(0,V_0^-1)` to obtain a product `lintegral <= 1`.

`BanditRLProof.OFULGaussianEvaluatedMixture` now discharges samplewise
Gaussian evaluation under PSD/PosDef contracts and converts the product bound
to the determinant-ratio inverse-Gram exponential sample `lintegral <= 1`.
Fernique supplies the required integrability bridge.

Exact Markov event transport, the common-`R` paper-facing vector tail, and its
finite-horizon ridge confidence-ellipsoid consumer now compile. The scalar
`V_0=lambda I` bias adapter, optimism theorem, and OFUL regret theorem remain;
a coordinate union bound is not an acceptable replacement.

## Closed Leaf: COND-EXPECT-REWARD Canonical Foundation

`LOCAL-LEAF-COND-EXPECT-REWARD-CANONICAL-FOUNDATION` closes the umbrella row
for the canonical reward-only `historyStepKernelFamily` trajectory measure.
Its three compiled declarations provide the MGF-to-integrability bridge,
successor conditional mean zero without caller integrability, and one bundled
mean-zero/MGF/finite-sum-tail endpoint. The regularity contract is the
canonical probability initial law, measurable policy/context/state/mean,
countable singleton-measurable actions, centered reward-kernel law, and
deterministic selected-history variance ceilings.

Arbitrary ambient trajectory-law identification, uniform-time confidence,
observed detectors, arm-wise empirical means, and final bandit/RL routes are
not closed by this leaf.

## Current Notes

- `TSALLIS-HALF-MINIMIZER-INTERIORITY` now compiles in
  `BanditRLProof.TsallisFTRLInteriority`.  Assuming a supported zero
  coordinate, simplex sum one supplies a positive donor.  A sufficiently small
  one-sided pair shift gains `sqrt(t)` at the zero coordinate while the donor
  square-root loss and arbitrary finite linear slope are only order `t`, so
  the shifted point has strictly smaller objective and contradicts global
  minimality.  Therefore every concrete half-Tsallis simplex minimizer is
  strictly positive without an eta sign condition.  The public sampling-law
  stability consumer now derives current/update positivity and stationarity
  internally.  Existence and canonical discrete selection now compile in the
  next leaf.

- `TSALLIS-HALF-MINIMIZER-EXISTENCE-SELECTION` now compiles in
  `BanditRLProof.TsallisFTRLMinimizerExistence`.  It minimizes the continuous
  half-Tsallis objective on Mathlib's compact standard simplex over `↥arms`,
  transports the minimizer by zero-extension, and provides canonical
  noncomputable current and importance-weighted update selectors.  The public
  one-step theorem no longer accepts minimizer or positivity certificates.
  This existence module alone does not prove history-dependent measurability;
  the downstream canonical-selector leaf now proves it using uniqueness,
  compactness, and Borel composition. Deterministic finite-horizon
  instantiation also compiles downstream.

- `TSALLIS-HALF-CANONICAL-FINITE-HORIZON-DECOMPOSITION` now compiles in
  `BanditRLProof.TsallisFTRLFiniteHorizonSelection`.  It specializes the fixed
  selector to `FTRL.cumulativeLoss loss t`, proves every required minimizer
  certificate, aligns `t+1` with both appended loss and the canonical
  importance-weighted update, and instantiates the finite-horizon
  power-sum-penalty decomposition without a caller `p` or `hp`.  This closes
  deterministic horizon plumbing only.  The sampling-law one-step theorem is
  an action average, while the realized successor depends on that sampled
  action; it must be transported through conditional expectation rather than
  summed as a pathwise inequality. Conditional transport and canonical
  `Classical.choose` measurability now compile in downstream leaves.

- `TSALLIS-HALF-CONDITIONAL-ACTION-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLConditionalStability`. It transports an identified
  conditional action law through the existing finite-action condDistrib
  integral theorem, applies the half-Tsallis current/update minimizer bound at
  each history, and exposes both generated action-process and canonical
  history-selector endpoints. One-round conditional-law transport is closed.
  Coordinate measurability for the chosen current selector and
  measurable/integrable updated stability scores remain explicit contracts;
  the next leaf consumes those contracts in the finite-horizon assembly.

- `TSALLIS-HALF-EXPECTED-FINITE-HORIZON-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLExpectedStability`. Per-round conditional-law
  identities recover the realized history/action law, transport product-law
  integrability to the ambient process, and let the finite time sum commute
  with the Bochner integral. The exact score recursion identifies each
  sampled-action update with the next-round canonical selector, yielding the
  actual displayed successor stability sum. This closes expected assembly
  under explicit policy-law, regularity, and recursion contracts. It does not
  construct those contracts from a concrete Tsallis trajectory or prove
  environment regret, self-bounding, tuning, or final Tsallis-INF regret.

- `TSALLIS-HALF-MINIMIZER-STATIONARITY-TRANSPORT` now compiles in
  `BanditRLProof.TsallisFTRLStationarity`.  Pairwise zero-sum simplex shifts
  remain feasible in a strict interior neighborhood, and differentiating the
  exact objective `eta*<p,score>-2*sum sqrt(p)+2` at a minimizer gives equal
  supported-coordinate gradients and a common
  `HalfTsallisInteriorStationary` multiplier.  The square-root supporting-line
  inequality proves the converse, so stationarity and minimality are
  equivalent for a supplied positive simplex point.  A direct consumer now
  derives all current/update multipliers internally and proves the prior
  sampling-law stability bound from `IsRegularizedMinimizer` certificates.
  The bridge itself needs no sign assumption on `eta`; its compatibility
  consumer retains `eta>0`, positive current/update points, and `[0,1]` losses.
  The downstream interiority leaf now closes strict positivity and removes
  those caller positivity proofs from the public consumer.  The exact next
  blocker is constructing or selecting concrete minimizers/updates.

- `TSALLIS-HALF-INTERIOR-STATIONARITY-ONE-STEP-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLOneStepStability`.  It defines the explicit
  half-Tsallis interior stationarity contract, subtracts current/update KKT
  equations, traps the multiplier displacement by simplex normalization and
  strict antitonicity of `x^(-1/2)`, proves the scalar curvature inequality,
  and consumes the compiled IW power moment to obtain
  `sum_chosen p(chosen) * stability(chosen) <=
  2*eta*powerSum arms (1/2) p`.  Current and updated probabilities must be
  strictly positive simplex points and losses lie in `[0,1]`.  The downstream
  leaves now close minimizer existence, interiority, canonical selection, and
  deterministic horizon decomposition.  Conditional action-law/expectation
  transport, expected stability assembly, self-bounding, and final regret are
  not claimed.
  This local FTRL stability-term bound is deliberately recorded as looser than
  the paper's conjugate-potential Lemma 11/19 bound: with
  `eta_local=eta_paper/2`, its coefficient is twice the comparable paper term.
  Its minimizer-to-stationarity bridge, strict positivity, concrete
  minimizer/update existence, and canonical horizon instantiation now compile
  downstream.

- `TSALLIS-IMPORTANCE-WEIGHTED-POWER-MOMENT` now compiles in
  `BanditRLProof.TsallisImportanceWeightedMoment`.  It reuses the existing EXP3
  sampled-coordinate estimator, proves the exact pathwise
  `loss(chosen)^2 * p(chosen)^(-alpha)` inverse-Hessian moment, takes its
  sampling-mass-weighted finite sum to obtain
  `sum_a loss(a)^2 * p(a)^(1-alpha)`, and bounds this by
  `Tsallis.powerSum arms (1-alpha) p` under pointwise `[0,1]` losses.  The
  contracts are finite arms, decidable equality, and strictly positive
  supported weights; normalization is intentionally absent from this purely
  algebraic statement.  This closes the estimator power algebra inside Lemma
  11 of the Tsallis-INF route, not the preceding Hessian/conjugate-potential
  stability estimate or any conditional expectation.  The next leaf is now
  precisely that one-step analytic stability bridge for an interior
  minimizer/KKT or concrete conjugate update.

- `TSALLIS-FTRL-STABILITY-PENALTY-REGRET-DECOMPOSITION` now compiles in
  `BanditRLProof.TsallisFTRLRegret`.  Coordinatewise cumulative losses and
  explicit `IsRegularizedMinimizer` certificates produce a regularized
  be-the-leader inequality, then the full finite-horizon comparator regret
  splits into
  `sum_t (<p_t,l_t>-<p_(t+1),l_t>)` plus the regularizer penalty.  For negative
  Tsallis entropy the final Lean theorem rewrites that penalty exactly as
  `((powerSum p_0-powerSum q)/(1-alpha))/eta`.  Its public contracts are a
  finite action set, `eta>0`, `alpha!=1`, simplex comparator, and cumulative
  minimizer certificates through the horizon.  No probability, measurability,
  estimator unbiasedness, convexity, or hidden minimizer existence is assumed.
  The next route is the actual exponent-specific stability estimate; weapon
  material is route inspiration only and cannot discharge that theorem.

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
Its armwise-bounded fixed-process expected-average consumer now also compiles
through exact `IdentDistrib.integral_eq` transport. The next open item is
strictly a concrete upstream producer/toolchain import.

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
downstream route; context-dependent/nonstationary, anytime/Freedman,
cross-toolchain, and other algorithms remain open.

The downstream card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is now compiled. It uses `max 1 finiteArmVarianceProxy` to satisfy the canonical
strict-positive tuning contract without changing the original armwise MGF
assumptions. Consequently, direct stationary finite-arm all-zero proxy families
now have a canonical Real expected pseudo-regret endpoint with no positivity,
caller ceiling, selected-law, trajectory-law, or integrability premise.
Positive padding is conservative; a sharper zero-width theorem remains open.

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
inspire the route. The finite exact and positive-padded specializations below
close finite automatic ceilings and all-zero proxy families. Infinite compact
context ceilings, context-dependent means/nonstationary regret,
anytime/Freedman, literal LML import, and other algorithms remain separate.

## Finite-context automatic-ceiling direct sub-Gaussian canonical Real UCB

`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-AUTOMATIC-CEILING-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is compiled locally. `Concentration.finiteContextArmVarianceProxy` takes the
nested finite supremum over contexts and arms, its domination lemma uses two
applications of Mathlib `Finset.le_sup`, and positivity follows from one
positive context/action proxy.

The theorem consumes direct pointwise centered `HasSubgaussianMGF` laws and
exact stationary arm means, computes `sigma2` internally, and reuses the
arbitrary-context canonical Real theorem. This exact-maximum variant needs one
positive member; the padded theorem below handles all-zero proxies. Infinite
context spaces still need a supplied uniform bound or new compactness or
boundedness infrastructure.

## Finite-context all-zero direct sub-Gaussian canonical Real UCB

`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is compiled locally. Its tuning proxy is `max 1` of the finite context/action
maximum. `le_max_right` gives genuine-proxy domination and `le_max_left` gives
strict positivity, including when every genuine proxy is zero.

The theorem retains pointwise `HasSubgaussianMGF` at the original proxies and
uses padding only for UCB tuning. No positivity witness, caller ceiling, or
domination proof remains. The bound is intentionally conservative; sharper
zero-width analysis and automatic bounds over infinite contexts remain open.

## Generated pure half-Tsallis trajectory stability

`LOCAL-LEAF-TSALLIS-HALF-GENERATED-TRAJECTORY-STABILITY` is compiled locally.
It recursively constructs the pure half-Tsallis finite-history policy and
predictable-environment trajectory, proves the conditional successor-action
law and almost-sure importance-weighted score recursion, and instantiates the
finite-horizon actual-successor stability integral. This closes the former
caller-supplied policy-law, `condDistrib`, and score-recursion obligations.

`LOCAL-LEAF-TSALLIS-HALF-GENERATED-STABILITY-AUTOMATIC-INTEGRABILITY` is also
compiled locally. Sampling mass cancels the importance-weighted denominator,
so the conditional absolute stability moment is bounded by `1 + arms.card`;
the half-power budget is bounded by `2 * |eta| * arms.card`. The generated
horizon theorem now has no caller stability- or budget-integrability families.

`LOCAL-LEAF-TSALLIS-HALF-GENERATED-STABILITY-MEASURABILITY` is now compiled as
well. It derives scalar stability-score measurability from finite measurable
sums, predictable-loss coordinates, and one generated-selector coordinate
contract. The selector-only horizon theorem has no `hscore` or integrability
families.

`LOCAL-LEAF-TSALLIS-HALF-CANONICAL-SELECTOR-MEASURABILITY` is now compiled.
Strict square-root-sum concavity yields strict convexity and supported
minimizer uniqueness. Compactness plus ultrafilter cluster-point transport
proves continuity of the restricted canonical choice; Borel composition then
inhabits both finite-history and generated updated selector contracts. The
canonical generated horizon theorem has no selector, `hscore`, or integrability
argument.

`LOCAL-LEAF-TSALLIS-ESTIMATED-ENVIRONMENT-REGRET` is now compiled. Its final
Lean endpoint bounds expected predictable environment regret over
`horizon + 1` actual rounds by a separate initial half-power term, the
integrated successor half-power sum, and the finite-simplex comparator penalty.
The route combines the deterministic FTRL decomposition, generated successor
stability, observed-to-predictable reward laws, and conditional first-moment
transport. Finite sampling mass cancels importance-weight denominators, so no
uniform exploration floor is assumed; the final theorem instead records a
probability prior, finite nonempty arms, eta positivity, predictable `[0,1]`
losses, and a general finite-simplex comparator.

Status/retrieval: root and focused builds, `Tests.Basic`, external canaries,
placeholder scan, and independent `#print axioms` audit pass. Compiled local
Tsallis/Exp3 declarations and Mathlib compProd/condDistrib/integral APIs are
proof evidence; paper/scenario cards support the route and the weapon card is
inspiration-only. Failure policy: do not omit time zero, add a fictitious
EXP3-style floor, or claim the paper conjugate-potential/final theorem. The
downstream `SELF-BOUNDING-CONVERSION` consumer now compiles.

`LOCAL-LEAF-TSALLIS-SELF-BOUNDING-CONVERSION` identifies point-mass comparator
environment regret with finite gap mass under a fixed predictable gap law,
lifts it to an integrated `(Delta,C,T)` self-bound, specializes the actual
generated upper theorem, and proves the abstract finite completion-of-squares
consumer. Root/focused builds and an external canary pass. The point-mass
obstruction theorem proves the current all-arm `powerSum (1/2)` cannot be
uniformly reduced to the suboptimal-arm square-root budget.

Failure policy: no logarithmic Tsallis-INF regret has been proved. The direct
`TSALLIS-REFINED-AVERAGED-STABILITY-DIAGNOSTIC` is closed negatively: the
current fixed-eta `<p-p_next,hatLoss>` expression fails the desired sampled
average bound even under exact minimizer contracts. Its distinct deterministic
conjugate-potential replacement now compiles. A reduced-variance estimator
requires its own estimator and law transport.

`LOCAL-LEAF-TSALLIS-REFINED-ALLARM-TO-SUBOPTIMAL` is now compiled. It proves
the finite-simplex best-arm elimination for `sum sqrt(p)*(1-p)` and a finite
time-by-suboptimal-arm theorem that composes this bound with the existing
self-bounding completion of squares. Root/focused builds and a concrete `Fin 2`
external canary pass.

`LOCAL-LEAF-TSALLIS-REFINED-SHIFTED-IW-MOMENT` is now compiled in
`BanditRLProof.TsallisRefinedImportanceWeightedMoment`. With the sampled raw
loss as baseline, the inverse-half-Hessian quadratic moment averages to at most
`sum_a sqrt(p_a)*(1-p_a)` and the positive cubic Taylor remainder averages to at
most one. The generic and current-FTRL wrappers therefore produce the desired
`eta/2` refined term plus `eta^2/2` from the explicit deterministic hypothesis
`hshiftedTaylor`. Contracts are finite decidable arms, strictly positive
supported simplex probabilities, `[0,1]` losses, and nonnegative eta; there are
no hidden measure or trajectory premises. Root/focused builds and a concrete
`Fin 2` canary compile.

The pointwise replacement by a chosen-coordinate
`sqrt(p_chosen)*(1-p_chosen)` term is false; only the sampled-action aggregate
has the required cancellation. This numerical diagnostic is route evidence,
not a Lean proof. The moment layer closes baseline expansion and finite-sum
averaging, but its conditional current-FTRL wrapper is not a producer.

`LOCAL-LEAF-TSALLIS-REFINED-AVERAGED-STABILITY-OBSTRUCTION` now compiles in
`BanditRLProof.TsallisRefinedAveragedStabilityObstruction`. The theorem
`exists_minimizer_counterexample_to_refinedAveragedStability` supplies positive
eta, strict current and ordinary-IW-updated `Fin 2` simplex minimizers, and
`[0,1]` losses, while proving that the locally paper-scaled
`eta * sum sqrt(p)*(1-p) + 2*eta^2` is strictly below the sampled average of
the current symmetrized stability term. The proof is exact rational Lean
arithmetic, not numerical evidence. Root/focused builds and an external canary
pass.

`LOCAL-LEAF-TSALLIS-CONJUGATE-POTENTIAL-STABILITY` now compiles in
`BanditRLProof.TsallisConjugatePotentialStability`. It defines the constrained
potential expression and explicit conjugate coordinate upper, proves the exact
rational increment and translated quadratic/cubic bound, transports current
minimizer stationarity into the potential comparison, verifies the ordinary-IW
domain using the selected raw-loss baseline, and obtains the sampled-action
coefficient `eta * sum_a sqrt(p_a)*(1-p_a) + 2*eta^2`. The canonical theorem
uses the existing current/update minimizer selectors. Local `eta` lies in
`(0,1/2]`, corresponding to paper eta in `(0,1]`; losses are in `[0,1]`; no
measure/kernel/integrability premise is used. Root/focused/`Tests.Basic` builds
and external canaries compile; public-import axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Independent review confirmed the scalar signs, domain, and coefficients, and
caught the cross-eta constant: `halfTsallisPotentialValue` now includes the
paper-normalizing `+1/eta`. The generic feasible-next bridge is explicitly a
candidate-value theorem; the minimizer-level/canonical endpoints certify both
potential points.

The current fixed-eta `<p-p_next,hatLoss>` theorem is not this statement, and
its direct route remains formally ruled out at the desired coefficient, so
`hshiftedTaylor` must not be reintroduced under the same contracts. The
generated fixed-eta conditional-action/expectation transport and finite-horizon
potential telescope now compile in
`LOCAL-LEAF-TSALLIS-CONJUGATE-POTENTIAL-FINITE-HORIZON-DECOMPOSITION`, with each
`2*eta^2` local remainder kept in the base term. `TSALLIS-TIME-VARYING-PENALTY` must
retain the learning-rate-change and negative best-arm terms and first build
scheduled minimizers, measurability, kernel identities, and same-`eta_t`
auxiliary updates. Their assembly remains
`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY`. A complete scheduled route
also needs a coarse fallback for early rounds with local `eta_t > 1/2` and an
exact reusable Lemma 18 conjugate-value interface.

`LOCAL-LEAF-TSALLIS-CONJUGATE-POTENTIAL-FINITE-HORIZON-DECOMPOSITION` is
compiled in `BanditRLProof.TsallisConjugatePotentialFiniteHorizon`. The exact
deterministic theorem telescopes score updates into the cumulative linear loss
plus terminal-minus-initial paper-normalized potential. A generic theorem uses
identified condDistrib laws and finite Bochner sums to integrate the ordinary
IW refined bound. The generated canonical endpoint supplies selector
measurability, finite-action policy identity, trajectory condDistrib, a.e. score
recursion, and score/budget integrability without a probability floor.

Contracts are a finite prior, finite nonempty decidable arms, Standard Borel
environment/action with measurable action singletons, predictable `[0,1]`
losses, and fixed local `eta` in `(0,1/2]`. Focused/root/`Tests.Basic` builds
and root-level declaration canaries pass. Failure policy: this closes only the
fixed-eta successor-round route. Time zero, early local `eta > 1/2`, scheduled
eta and penalty changes, refined assembly, and final Tsallis-INF regret remain
open.

`LOCAL-LEAF-TSALLIS-TIME-VARYING-PENALTY` is now compiled in
`BanditRLProof.TsallisTimeVaryingPenalty`. It defines the paper-normalized
half-Tsallis potential mass, proves the cross-rate minimizer comparison, and
telescopes a positive nonincreasing schedule while preserving the negative
terminal comparator contribution. The generic theorem exposes current and
same-rate-next minimizer certificates; the canonical theorem constructs both
families from `halfTsallisMinimizer`, and the point-mass corollary exposes the
negative best-arm term `-1 / eta_n`. Its only algorithmic contracts are a
finite-simplex comparator and positive nonincreasing `eta_t`; it introduces no
measure, measurability, conditional-law, integrability, bounded-loss, or
`eta_t <= 1/2` assumption. Root/focused/`Tests.Basic` and the external canonical
canary compile. Retrieval evidence is Tsallis-INF Lemmas 12 and 20, the local
conjugate-potential/FTRL/minimizer surfaces, and Mathlib finite-sum/order APIs.

Failure policy: deterministic cross-eta penalty control is closed. The next
narrow leaf must connect a scheduled half-Tsallis selector and its same-rate
auxiliary minimizer to generated finite histories and conditional action laws.
Early large-step stability, refined assembly, harmonic/log tuning, and final
Tsallis-INF regret remain separate.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-RECURSIVE-TRAJECTORY`

This leaf is now compiled in
`BanditRLProof.TsallisScheduledRecursiveTrajectory`. The generated algorithm
uses `eta 0` for its initial action and `eta (n+1)` for the successor policy
after the visible prefix through `n`. The roundwise canonical selector
contract proves score-coordinate measurability, builds the finite-action
sources and Ionescu--Tulcea trajectory, and identifies both the history-only
and environment-retaining successor conditional action laws.

Contracts are finite nonempty decidable arms, measurable action singletons, a
deterministic real schedule, and Standard Borel spaces plus a finite prior for
the `condDistrib` wrappers. No rate positivity or monotonicity is required at
this structural layer. Retrieval evidence is the compiled fixed-rate
trajectory, canonical selector, deterministic scheduled penalty, and local
Mathlib kernel/conditional-distribution APIs.

Failure policy: generated scheduled selector and action-law transport are
closed. The downstream pathwise score/penalty alignment and expected successor
stability sum now compile. Its time-zero law consumer, early large-step
stability, refined expectation assembly, tuning, and final Tsallis-INF regret
remain separate.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-SCORE-PENALTY-ALIGNMENT`

This leaf is compiled in `BanditRLProof.TsallisScheduledScoreAlignment`.
The generated observed-IW score is identified with `FTRL.cumulativeLoss`, the
actual time-`t` probability is rewritten as the canonical scheduled minimizer,
and generated estimated regret is decomposed exactly into the same-rate
conjugate-potential stability sum and scheduled potential penalty. The
supported point-mass endpoint consumes the deterministic penalty theorem and
retains `-1/eta_n`.

Contracts are finite nonempty decidable arms, an arbitrary trajectory sample,
a supported best arm, positive schedule through the terminal index, and
nonincreasing schedule before it. No measure, measurability, kernel,
conditional law, integrability, bounded loss, probability floor, or eta upper
bound is used. Retrieval evidence is the compiled scheduled trajectory,
time-varying penalty, fixed-rate score alignment, conjugate-potential producer,
and local finite-sum/cumulative-loss declarations.

Failure policy: pathwise score and penalty assembly, the expected successor
same-rate stability sum, the separate time-zero consumer, and their exact
all-times finite-sum assembly now compile. Rounds with local `eta_t > 1/2`
still require a coarse fallback rather than the refined conjugate lemma; the
small-rate expected stability-plus-penalty integration also remains open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-SUCCESSOR-EXPECTED-STABILITY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledExpectedStability`. The endpoint bounds the
integral of the exact scheduled pathwise stability terms at actual times
`n+1` by the finite sum of local refined budgets
`eta (n+1) * sum_a sqrt(p_a) * (1-p_a) + 2 * eta (n+1)^2`.

The proof lifts each scheduled finite-action distribution to the retained
environment/prefix state, packages the same-rate updated minimizer and its
coordinate measurability, uses the generated successor `condDistrib`, obtains
automatic product-law score and history-law budget integrability, rewrites the
stored reward to its predictable loss coordinate almost surely, and sums the
one-round bounds with Mathlib-backed finite Bochner integration.

Contracts are a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable supported
`[0,1]` losses, and `0 < eta (n+1) <= 1/2` for every included successor. No
schedule monotonicity, probability floor, time-zero law, independence, or
concentration premise is used. Retrieval evidence is the scheduled trajectory
and score/penalty leaves, the fixed-rate conjugate finite-horizon theorem,
Mathlib kernel/integral/finite-sum routes, and Tsallis-INF Lemmas 18--19.
Focused/root/`Tests.Basic` builds and the external `Fin 2` endpoint canary pass;
the public-import axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Failure policy: successor expectation transport is closed, and time zero plus
the combined all-times finite-sum consumer now compile downstream. The early
`eta_t > 1/2` fallback, full integrated stability-plus-penalty assembly,
all-arm refinement, tuning, and final regret remain open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-INITIAL-EXPECTED-STABILITY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledInitialExpectedStability`. It proves
integrability of the exact scheduled pathwise stability term at actual time
zero and bounds its integral by the canonical initial refined budget.

The proof packages the zero-score initial history/action potential score and
refined budget, reuses the canonical initial finite-action source, transports
the initial action conditional law, rewrites the stored reward to the selected
predictable initial loss almost surely, identifies the same-rate updated
minimizer, and instantiates the generic one-round conjugate-potential bound.

Contracts are a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` initial
losses, and `0 < eta 0 <= 1/2`. No schedule monotonicity, successor-rate
premise, probability floor, independence, or concentration is used. Retrieval
evidence is the scheduled successor/score/trajectory leaves, canonical initial
action and reward laws, the generic potential-stability integral theorem, and
Mathlib kernel/integral APIs. Focused/root/`Tests.Basic` builds and the external
`Fin 2` canary pass; the source is placeholder-free and the public-import axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Failure
policy: time zero is closed; the combined
initial-plus-successor finite sum now compiles downstream. The early-rate
fallback, integrated regret assembly, tuning, and final Tsallis-INF regret
remain open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-ALL-TIMES-EXPECTED-STABILITY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledAllTimesExpectedStability`. It proves
integrability of the exact scheduled pathwise stability sum over
`Finset.range (horizon + 1)` and bounds its integral by the initial refined
budget plus the complete successor refined-budget sum.

The proof first makes the successor path/history-action equality a public a.e.
API, transports product-law integrability to every actual successor term, and
forms its finite sum. It combines that result with the distinct time-zero
endpoint, proves the two refined-budget functions integrable, and joins the
initial and successor inequalities using `integral_add` and
`Finset.sum_range_succ'`.

Contracts are a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` losses,
and `0 < eta t <= 1/2` for all `t <= horizon`. No monotonicity, probability
floor, comparator, independence, or concentration premise is used. Retrieval
evidence is the initial/successor scheduled expectation leaves, score/penalty
alignment, `IntegrabilitySums.integrable_finset_sum`, `Integrable.add`,
`integral_add`, and the Mathlib integral/finite-sum cards. Focused/root and
`Tests.Basic` builds plus the exact `Fin 2` canary pass; the source is
placeholder-free and the public-import axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Failure policy: all-times expected stability is closed under the small-rate
contract. The `eta_t > 1/2` fallback, integrated expected
stability-plus-penalty theorem, all-arm refinement, tuning, and final
Tsallis-INF regret remain open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-ALL-RATE-EXPECTED-STABILITY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledAllRateExpectedStability`. The final theorem
retains the exact generated pathwise sum over
`Finset.range (horizon + 1)` and selects the refined budget when
`eta t <= 1/2` or the coarse constant `1` otherwise.

The Lean surface includes the deterministic minimizer-to-linear-loss bridge,
pointwise and simplex-averaged ordinary-IW bounds, arbitrary-rate finite-action
product integrability, generic conditional-law transport, generated initial
and successor wrappers, per-time piecewise budgets, and exact finite-sum
integrability and expectation endpoints. The proof route uses old-objective
minimality, ordinary-IW cancellation, nonnegativity of the updated mixed loss,
finite-simplex averaging, `condDistrib` transport, and finite sum/integral
exchange.

Contracts are a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable supported
`[0,1]` losses, and `0 < eta t` for included times. No eta upper bound,
monotonicity, probability floor, comparator, independence, or concentration
is used. Retrieval evidence is Tsallis-INF Lemma 11's ordinary-IW
`min {refined, 1}` branch and early constant fallback, the compiled scheduled
expected-stability leaves, `FTRL.IsRegularizedMinimizer`,
`Exp3.mixedImportanceWeightedLoss_eq_selectedLoss`, and local finite-kernel,
integral, and finite-sum cards. Cards are evidence only; weapons are
inspiration-only.

Failure policy: arbitrary positive-rate expected stability is closed, and its
expected-regret consumer now compiles. Apply the all-arm conversion next;
tuning and final Tsallis-INF regret remain open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-EXPECTED-REGRET`

This leaf is compiled in `BanditRLProof.TsallisScheduledExpectedRegret`. The
Lean endpoint bounds generated predictable environment regret against a
point-mass best arm by the integrated per-time all-rate stability budget plus
the explicit scheduled initial-minus-terminal potential penalty.

Local APIs cover scheduled probability measurability/simplex membership,
predictable IW estimators, stored-reward a.e. transport, no-floor conditional
first moments, and finite-horizon integrability. The proof route reuses the
fixed-rate generic `condDistrib` moment lemmas, generated scheduled conditional
action laws, the pathwise point-mass penalty theorem, the all-rate expected
stability theorem, `integral_mono_ae`, and finite-sum integral exchange.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, `best ∈ arms`, positive rates through the inclusive
horizon, and schedule monotonicity between included rounds. There is no
probability floor, eta upper bound, independence, concentration, or gap-law
premise. Retrieval evidence is the fixed-rate estimated/environment leaf, the
scheduled score/penalty and all-rate stability leaves, Mathlib conditional-law,
integral, and finite-sum cards, and Tsallis-INF Lemma 11. Failure policy: do not
claim tuned rates or the full Tsallis-INF regret theorem; its small-rate
suboptimal-arm consumer now compiles.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-SUBOPTIMAL-EXPECTED-BOUND`

This leaf is compiled in
`BanditRLProof.TsallisScheduledSuboptimalExpectedBound`. Its Lean-facing
statements define the expected scheduled action law, prove finite-simplex
membership and square-root integrability, apply concave Jensen coordinatewise,
convert each small-rate all-arm stability budget into a sum over
`arms.erase best`, sum over the inclusive horizon, and combine the result with
the generated point-mass scheduled expected-regret theorem. The final consumer
uses the existing finite completion-of-squares theorem under an explicit
expected-probability self-bounding premise.

Local APIs/imports are `TsallisScheduledExpectedRegret`,
`TsallisRefinedSuboptimalStability`, Mathlib's convex integral and square-root
modules, `Real.strictConcaveOn_sqrt.concaveOn.le_map_integral`,
`sum_sqrt_mul_one_sub_le_two_mul_sum_erase_sqrt`, finite Bochner sum exchange,
and `regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption`. The proof route
is expected-simplex regularity, Jensen, pathwise best-arm elimination,
per-time integration, exact finite summation, scheduled penalty substitution,
and abstract self-bounding completion.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, positive nonincreasing rates
with `eta t <= 1/2` through the horizon, positive gaps on the erased arm set,
and an explicit self-bound with corruption for the last endpoint. No
probability floor, independence, concentration, or tuned rate is assumed.
Retrieval evidence is the four compiled upstream local leaves, Mathlib
measure-integral/finite-sum/square-root cards, the concave Jensen declaration,
and Tsallis-INF Lemma 11. Theorem cards are evidence only and weapon cards are
inspiration-only. Failure policy: the expected all-arm conversion and abstract
self-bounding assembly are closed; next derive the self-bound from an exact
predictable fixed-gap law, which now compiles downstream. Do not report tuned
rates or full Tsallis-INF regret yet.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-FIXED-GAP-SELF-BOUNDING`

This leaf is compiled in
`BanditRLProof.TsallisScheduledFixedGapSelfBounding`. Its Lean-facing
statements define pathwise scheduled suboptimal gap mass, identify it exactly
with predictable environment regret against the best-arm point mass, exchange
the finite horizon/arm sums with the trajectory integral, derive the
expected-probability self-bound for nonnegative corruption, and invoke the
compiled completion-of-squares endpoint automatically.

Local APIs/imports are `TsallisScheduledSuboptimalExpectedBound`,
`linearLoss_sub_pointMass_eq_gapMass`, scheduled finite-simplex laws,
`Finset.sum_erase_add`, `IntegrabilitySums.integrable_finset_sum`,
`ExpectationBochnerSums.integral_finset_sum`, `integral_mul_const`, and
`integral_congr_ae`. The proof route is pointwise point-mass gap expansion,
best-arm erasure, finite coordinate integrability, integral/sum exchange,
exact expected gap-mass equality, nonnegative-corruption weakening, and the
existing scheduled self-bounding consumer.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, exact samplewise predictable
loss differences equal to fixed gaps, positive gaps on `arms.erase best`,
nonnegative corruption, and positive nonincreasing rates bounded by `1/2`
through the inclusive horizon. No probability floor, independence,
concentration, caller self-bound, or tuned rate is assumed. Retrieval evidence
is the scheduled suboptimal expected-bound, generic self-bounding, and
scheduled expected-regret leaves, Mathlib finite-sum/measure-integral cards,
and the Tsallis-INF stochastic self-bounding route. Theorem cards are evidence
only and weapons are inspiration-only. Failure policy: this exact predictable
gap route is closed. A stochastic reward-kernel-to-gap-law transport and
schedule tuning remain open; do not report full Tsallis-INF regret.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-REFINED-EXPECTED-PENALTY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledRefinedExpectedPenalty`. Its Lean-facing mass
theorem proves
`halfTsallisPotentialMass(p)-1 <= 2*sum_{a!=best}(sqrt(p_a)-p_a/2)`.
The sampled pathwise theorem consumes the uncollapsed time-varying penalty and
cancels the point-mass baseline while retaining every reciprocal-rate
increment. The final endpoint transports those refined masses through
expectation and bounds generated predictable environment regret by the
all-rate stability integral plus the refined expected penalty, with no
terminal mass divided by `eta_horizon`.

Local APIs/imports are `TsallisScheduledSuboptimalExpectedBound`,
`sum_halfTsallisScheduledPotentialPenalty_le`,
`Exp3Potential.sum_range_forward_difference`, scheduled probability
simplex/measurability/integrability declarations, concave square-root Jensen,
finite Bochner sum exchange, and `integral_mono_ae`. The proof route is the
sqrt tangent inequality, finite-simplex best-arm elimination, pathwise
baseline cancellation, finite integrability, coordinatewise Jensen, and
observed-to-environment regret assembly.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, positive rates through the
inclusive horizon, and a nonincreasing schedule. No eta upper bound,
probability floor, fixed-gap law, independence, concentration, or tuned rate
is assumed. Retrieval evidence is Tsallis-INF Lemma 12 part 2, the local
time-varying penalty, score-alignment, expected-regret, and Jensen leaves, and
Mathlib finite-sum/measure-integral/square-root cards. Theorem cards are
evidence only and weapons are inspiration-only. Failure policy: reciprocal-
rate refinement and Jensen transport are closed. Next combine this penalty
with refined stability coefficients; that assembly now compiles downstream.
Do not revert to the coarse endpoint or report full Tsallis-INF regret.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-REFINED-STABILITY-PENALTY-ASSEMBLY`

This leaf is compiled in
`BanditRLProof.TsallisScheduledRefinedStabilityPenalty`. It defines the unified
coefficient `c_0=2*eta_0+2/eta_0` and
`c_(t+1)=2*eta_(t+1)+2*(1/eta_(t+1)-1/eta_t)`. The first Lean-facing endpoint
combines the small-rate expected stability and refined expected penalty into
`regret <= sum_t 2*eta_t^2 + sum_t c_t*sum_{a!=best} sqrt(E[p_t(a)])`.
The second consumes the exact fixed-gap self-bound and proves the automatic
`2*sum_t 2*eta_t^2 + sum_(t,a!=best)c_t^2/gap_a + corruption` theorem.

Local APIs/imports are `TsallisScheduledRefinedExpectedPenalty`,
`TsallisScheduledFixedGapSelfBounding`, expected-simplex/Jensen declarations,
the small-rate all-time stability conversion, `Finset.sum_range_succ'`,
`Finset.sum_product`, and the generic completion-of-squares theorem. The proof
route drops the nonpositive expected linear correction, uses reciprocal-rate
nonnegativity, isolates time zero, reindexes successor sums, rewrites the
time/arm product, and consumes the automatic exact-gap self-bound.

Contracts are a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty decidable arms, predictable
supported `[0,1]` losses, a supported best arm, positive nonincreasing rates
bounded by `1/2`, exact samplewise gaps, positive suboptimal gaps, and
nonnegative corruption. No probability floor, independence, concentration,
caller self-bound, or tuned schedule is assumed. Retrieval evidence is the
refined expected penalty, fixed-gap, Jensen, self-bounding, finite-sum,
measure-integral, and square-root routes. Theorem cards are evidence only and
weapons are inspiration-only. Failure policy: coefficient assembly is closed,
and the concrete square-root schedule now compiles downstream. Do not reopen
the coarse terminal penalty or report the broader stochastic/full theorem.

### `LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-FIXED-GAP`

Status: `leanCompiled` in `BanditRLProof.TsallisSqrtScheduleFixedGap`, root
imported, focused and `Tests.Basic` builds passing, with an external `Fin 2`
canary. The Lean-facing schedule is
`eta_t = 1 / (2 * sqrt (t + 1))`; it is positive, nonincreasing, and at most
`1/2`. The module proves `4 * eta_t^2 = 1/(t+1)` and the unified refined
coefficient bound `c_t^2 <= 25/(t+1)`. Its final theorem closes the exact
fixed-gap route as
`regret <= H_(T+1) * (1 + 25 * sum_(a != best) 1/gap(a)) + corruption`.

Local APIs/imports are the refined stability-penalty automatic fixed-gap
endpoint, `Real.sqrt_pos`, `Real.sqrt_le_sqrt`, `Real.sq_sqrt`, reciprocal
order, `Finset.sum_product`, and `Finset.mul_sum`. Contracts are a probability
prior, Standard Borel environment/action, measurable action singletons,
finite nonempty decidable arms, predictable supported `[0,1]` losses, a
supported best arm, exact samplewise predictable gaps, positive suboptimal
gaps, and nonnegative corruption. No caller schedule proof, probability floor,
independence, concentration premise, or caller self-bound remains.

Retrieval evidence is the compiled refined assembly and fixed-gap self-bound,
`MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, and the Tsallis-INF paper card;
cards are evidence only and weapons are inspiration-only. Failure policy: the
schedule contracts, coefficient finite sum, and harmonic fixed-gap theorem are
closed. Its Mathlib-backed logarithmic corollary now compiles downstream;
broader stochastic/corrupted-law transport remains separate.

### `LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-LOG-FIXED-GAP`

Status: `leanCompiled` in `BanditRLProof.TsallisSqrtScheduleFixedGap`, root
imported, focused and `Tests.Basic` builds passing, with an external `Fin 2`
canary. The Lean-facing bridge proves the local Real harmonic budget equals
the Real cast of Mathlib's rational `harmonic (T+1)`, applies
`harmonic_le_one_add_log`, and derives
`regret <= (1+log(T+1))*(1+25*sum_(a!=best)1/gap(a))+corruption`.

Local APIs/imports are `Mathlib.NumberTheory.Harmonic.Bounds`, `harmonic`,
`Rat.cast_sum`, `Rat.cast_inv`, `Rat.cast_natCast`,
`harmonic_le_one_add_log`, the compiled harmonic fixed-gap endpoint,
`Finset.sum_nonneg`, and `mul_le_mul_of_nonneg_right`. Contracts are unchanged:
probability prior, Standard Borel environment/action, measurable action
singletons, finite nonempty decidable arms, predictable supported `[0,1]`
losses, supported best arm, exact samplewise predictable gaps, positive
suboptimal gaps, and nonnegative corruption. No horizon positivity, caller
schedule proof, floor, independence, concentration, or caller self-bound is
added. Retrieval evidence is the local harmonic endpoint,
`MLIB-REAL-LOG-SQRT`, Mathlib harmonic bounds, and the Tsallis-INF paper card.
Failure policy: harmonic cast alignment and the explicit logarithmic exact-gap
theorem are closed. Broader stochastic/corrupted reward-law transport remains
open; do not report the full paper theorem.

### `LOCAL-LEAF-TSALLIS-FINITE-BANDIT-MEAN-LOSS`

Status: `leanCompiled` in `BanditRLProof.TsallisFiniteBanditMeanLoss`, root
imported, focused and `Tests.Basic` builds passing, with an external `Fin 2`
canary. The Lean-facing constructor maps bounded model means to the stationary
predictable losses `1-mean`; its time-index theorem removes history/sample
dependence, and its gap theorem identifies the loss difference against
`bestArm` with the Real cast of `FiniteBanditModel.gap`. The final endpoint
instantiates the logarithmic square-root-schedule theorem on `Finset.univ`.

Local APIs/imports are `FiniteBanditModelInvariants`,
`TsallisSqrtScheduleFixedGap`, `Exp3.PredictableLossVector`,
`Exp3.predictableLossAt`, `measurable_of_countable`, the finite-model
`bestArm`/`bestMean`/`gap` definitions, and `Finset.univ`/`erase`. Contracts are
a probability prior on a Standard Borel environment, all Real-cast model means
in `[0,1]`, positive gaps for every arm distinct from `bestArm`, and
nonnegative corruption. No caller loss, measurability proof, gap-law proof,
schedule proof, horizon positivity, floor, independence, concentration,
reward kernel, or conditional law is required. Retrieval evidence is the
compiled logarithmic fixed-gap leaf, finite-model invariant leaves,
`MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA`, local declaration search, and the
Tsallis-INF paper card. Failure policy: deterministic model-mean specialization
is closed. `PredictableLossVector.environment` still emits Dirac mean losses;
stochastic reward-kernel feedback and conditional-mean/self-bounding transport
remain open.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-EXPECTED-GAP-SELF-BOUNDING`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledExpectedGapSelfBounding`, root imported, focused,
root, and `Tests.Basic` builds passing, with an external `Fin 2` canary and a
public-import axiom audit limited to `propext`, `Classical.choice`, and
`Quot.sound`.

Lean statement: `HasScheduledExpectedGapLaw` records, separately for each
`t <= horizon` and `a in arms.erase best`, the identity
`integral p_t(a)*(loss_t(a)-loss_t(best)) = gap(a)*integral p_t(a)`. This law
implies the integrated self-bound and, through generic refined/square-root
consumers, the explicit logarithmic regret bound with corruption.

Local APIs/imports are `TsallisScheduledFixedGapSelfBounding`,
`TsallisScheduledRefinedStabilityPenalty`, `TsallisSqrtScheduleFixedGap`,
`linearLoss_sub_pointMass_eq_gapMass`, `Integrable.mul_bdd`, predictable-loss
measurability and unit-interval bounds, `ExpectationBochnerSums.integral_finset_sum`,
and `IntegrabilitySums.integrable_finset_sum`. The route is pathwise finite-sum
algebra, bounded-product integrability, coordinatewise expected-gap rewrite,
completion of squares, and the existing harmonic/log estimate.

Contracts are a probability trajectory law, measurable singleton actions,
finite nonempty decidable arms, predictable `[0,1]` losses, supported best arm,
positive suboptimal gaps, nonnegative corruption, and the expected-gap law;
the generated endpoint adds Standard Borel spaces and a probability prior. No
samplewise fixed-gap identity, floor, concentration result, or schedule proof
is required. Retrieval evidence is the local fixed-gap/refined/sqrt-log chain,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`,
`MLIB-CONDITIONAL-EXPECTATION`, and the Tsallis-INF paper card. Cards are
evidence only and weapons are inspiration-only. Failure policy: all consumers
of the first-moment law are closed. A producer from concrete stochastic
reward/loss conditional means or independence is the next open leaf.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-CONDITIONAL-MEAN-EXPECTED-GAP`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledConditionalMeanGap`, root imported, with focused,
root, and `Tests.Basic` builds and an external `Fin 2` canary passing.

Lean statement: `sampledScheduledHalfTsallisPastSigma` exposes the information
available before each scheduled action and
`measurable_sampledScheduledHalfTsallisProbabilityAtTime_pastSigma` proves the
corresponding probability coordinate measurable. Under
`HasScheduledConditionalMeanGapLaw`, theorem
`hasScheduledExpectedGapLaw_of_conditionalMeanGapLaw` returns the existing
coordinatewise expected-gap law.

Local APIs/imports are `TsallisScheduledExpectedGapSelfBounding`, Mathlib
conditional-expectation pull-out, `integral_condExp`, finite-prefix
measurability, and bounded predictable-loss integrability. The proof route is
past measurability, pull `p_t(a)` through `condExp`, replace the conditional
loss difference by the constant gap almost everywhere, then remove `condExp`
under the integral. Regularity is a probability trajectory law, measurable
singleton actions, finite nonempty decidable arms, predictable `[0,1]` losses,
and the coordinatewise conditional mean identity. Retrieval evidence is the
local expected-gap leaf, `MLIB-CONDITIONAL-EXPECTATION`,
`MLIB-MEASURE-INTEGRAL`, local independence wrappers, and the Tsallis-INF paper
card; theorem cards are evidence only and weapons are inspiration-only.
Failure policy: generic conditional-mean transport is closed and the abstract
independence producer now compiles downstream. A concrete reward/loss-kernel
producer remains open; do not claim the full stochastic/corrupted theorem.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-INDEPENDENT-MEAN-GAP-REGRET`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledIndependentMeanGap`, root imported, with focused,
root, and `Tests.Basic` builds passing and a final-endpoint `Fin 2` canary.

Lean statement: `HasScheduledIndependentMeanGapLaw` packages independence of
each predictable loss difference from `sampledScheduledHalfTsallisPastSigma`
and the identity `integral lossDiff = gap(a)`. The two producers return the
conditional-mean and expected-gap laws, and
`integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_independentMeanGap`
returns the explicit logarithmic regret bound.

Local APIs/imports are `TsallisScheduledConditionalMeanGap`,
`TsallisSqrtScheduleFixedGap`, Mathlib probability conditional expectation,
`ProbabilityTheory.Indep`, `MeasurableSpace.comap`, and
`MeasureTheory.condExp_indep_eq`. The proof route is comap measurability,
independence-to-constant conditional expectation, expected-gap conversion,
automatic self-bounding, and the compiled square-root/log consumer.

Regularity is a probability trajectory law, finite nonempty decidable arms,
predictable `[0,1]` losses, coordinatewise independence and exact global
means; measurable singleton actions enter the expected-gap producer. The
generated final theorem adds Standard Borel spaces, a probability prior,
positive suboptimal gaps, and nonnegative corruption. Retrieval evidence is
the local conditional/expected-gap chain, `MLIB-PROBABILITY-INDEPENDENCE`,
`MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`, the ETC independence
wrapper, and the Tsallis-INF paper card; cards are evidence only and weapons
are inspiration-only. Failure policy: this abstract independence theorem
route is closed. Its premises still need a concrete stochastic reward/loss
kernel proof; do not claim the full stochastic/corrupted theorem.
+
### `LOCAL-LEAF-TSALLIS-SCHEDULED-IID-MEAN-GAP-REGRET`

Status: `leanCompiled` end to end in
`BanditRLProof.TsallisScheduledIIDMeanGap`, root imported and externally
canaried.  `iidLossStatePredictableLossVector` reads one coordinate of an
infinite-product loss-state environment per round.
`KernelTrajectoryPrefix.partialTraj_zero_congr` and
`trajMeasure_map_frestrictLe_congr`, the measurable finite-prefix extension,
and `sampledScheduledHalfTsallisIIDPrefixKernel` construct the canonical
`HasScheduledIIDPrefixKernelFactorization` producer.  The final
`..._log_iidLossState` theorem consumes this producer internally.

Local APIs/imports: `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`,
`KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr`,
`IndepFun.comp_of_map`,
`indepFun_fst_snd_compProd_comap_of_indepFun`, `Measure.compProd_map`,
`Measure.fst_compProd`, `Measure.infinitePi_map_eval`, and the compiled
scheduled independent-mean theorem.  Regularity is Standard Borel loss states
and actions, measurable singleton actions, a probability coordinate law,
jointly measurable `[0,1]` losses, positive mean gaps, and nonnegative
corruption; no external trajectory/factorization premise remains.  Retrieval evidence is the local IID and
scheduled independence leaves, Mathlib independence/kernel/integral cards, and
the Tsallis-INF paper card; cards are not local proofs.

Failure policy: prefix factorization, IID independence and mean transport, and
the concrete IID logarithmic theorem are closed. Its finite-arm stochastic
reward-vector and model-gap consumer now compiles. Actual corruptions remain a
separate process-law route.

### `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-REWARD-LAW-REGRET`

Status: `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDRewardLaw`, root imported and externally
canaried. The Lean-facing theorem takes `armLaw : Fin K -> Measure Rat`, one
probability instance per arm, a.e. reward support in `[0,1]`, exact arm-law
integrals equal to `model.mean`, positive non-best `model.gap`, and a
nonnegative corruption allowance. It returns the generated scheduled
half-Tsallis logarithmic regret bound with reciprocal `model.gap` terms.

Local APIs/imports are `Mathlib.MeasureTheory.Integral.Pi`, `Measure.pi`,
`MeasureTheory.integral_comp_eval`, `Integrable.of_bound`,
`Tsallis.clippedUnitReward`, `finiteArmIIDRewardVectorLaw`, and the compiled
IID loss-state endpoint. The proof route clips samples pointwise to satisfy the
abstract evaluator's global bounds, removes clipping a.e. under each arm-law
integral, transports coordinate means through the finite product, and rewrites
`iidLossStateMeanGap` as `FiniteBanditModel.gap`.

Regularity is explicit: arm laws are probabilities, raw rewards lie in the
unit interval a.e., raw integrals equal the rational model means, non-best gaps
are positive, and corruption is nonnegative. The product construction also
imposes within-round arm independence and IID rounds. Retrieval evidence is
the local scheduled IID leaf, `MLIB-MEASURE-INTEGRAL`,
`MLIB-PROBABILITY-INDEPENDENCE`, Mathlib's Pi-integral API, and the two
Tsallis-INF paper cards; cards are evidence only and the Tsallis weapon is
inspiration-only.

Failure policy: product-law construction, clipping/mean preservation,
model-gap identification, and the stochastic IID logarithmic endpoint are
closed. Its stationary-oblivious corrupted-process consumer now compiles.

### `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-STATIONARY-CORRUPTED-REWARD-LAW-REGRET`

Status: `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDCorruptedRewardLaw`, root imported and
externally canaried at zero shift. The final theorem applies a fixed real shift
to each arm's fresh IID reward, clips the result to `[0,1]`, and returns the
baseline model-gap logarithmic regret bound plus the explicit budget
`(T+1) * sum_(a != best) (abs (shift a) + abs (shift best))`. There is no free
corruption scalar.

Local APIs/imports are `Mathlib.Topology.UnitInterval`, `Set.projIcc`,
`Set.abs_projIcc_sub_projIcc`, `norm_integral_le_of_norm_le_const`,
`scheduledGapDeviationBudget`, the scheduled expected-gap law, the existing
IID prefix-factorization/independence producers, and the square-root
self-bounding endpoint. The proof route first controls actual mean-gap drift,
then turns the actual IID expected-gap law into a baseline-gap self-bound, and
finally applies harmonic-to-log control.

Regularity is probability arm laws, raw rewards a.e. in `[0,1]`, exact means,
positive non-best baseline gaps, fixed real arm shifts, finite horizon,
within-round product independence, and IID rounds. Retrieval evidence is the
finite-arm IID and expected-gap leaves, Mathlib measure/integral/independence
cards and unit-interval contraction, and the Tsallis-INF/corrupted Tsallis-INF
paper cards. Cards are evidence only and the Tsallis weapon is inspiration-only.

Failure policy: stationary oblivious clipped corruption and its explicit
allowance are closed. Its deterministic time-indexed predictable extension now
compiles; history-adaptive adversarial corruption still requires a
past-measurable conditional reward-law transport before the full
corrupted-stochastic paper theorem can be claimed.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-TIME-VARYING-EXPECTED-GAP`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledTimeVaryingExpectedGap`. The law family now
accepts `gap : Nat -> Action -> Real`; independence is converted to a
time-varying conditional mean, conditional pull-out yields the weighted
expected-gap identity, and finite integration identifies generated regret
with the time-by-arm actual gap mass. A coordinatewise deviation from fixed
baseline gaps yields the exact accumulated self-bound.

Local APIs/imports are the scheduled past sigma-algebra, Mathlib
`condExp_indep_eq`, `condExp_mul_of_stronglyMeasurable_left`,
`integral_condExp`, finite Bochner-sum exchange, and expected-probability
simplex bounds. Regularity is a probability trajectory measure, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` losses,
and deterministic per-time conditional or independent means. Retrieval is the
compiled conditional/expected-gap chain, Mathlib conditional expectation,
integral, and independence cards, plus the corrupted Tsallis-INF paper card.
Failure policy: deterministic Nat-indexed gap transport is closed; random
history-dependent gaps need a stronger past-measurable law.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-IID-TIME-VARYING-MEAN-GAP`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap`. The predictable loss
evaluator may depend on `t` while reading the fresh IID coordinate `state_t`.
Finite-prefix congruence constructs the canonical prefix kernel; product
coordinate independence and marginal integral identities then produce the
time-varying independent and expected-gap laws.

Regularity is Standard Borel state/action spaces, measurable action
singletons, one probability coordinate law, per-time jointly measurable
`[0,1]` evaluators, and finite horizon. Retrieval is the stationary IID
producer, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-PROBABILITY-KERNEL`,
`MLIB-MEASURE-INTEGRAL`, and the local time-varying gap law. Failure policy:
deterministic time-indexed IID evaluators are closed; nonidentical state laws
compile in the next leaf, while history-dependent evaluators require another
process-law producer.

### `LOCAL-LEAF-TSALLIS-SCHEDULED-INDEPENDENT-NONIDENTICAL-MEAN-GAP`

Status: `leanCompiled` in
`BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap`, root imported directly
and externally canaried. The Lean-facing theorem takes
`law : Nat -> Measure LossState`, one probability instance per coordinate,
the existing time-varying bounded evaluator, and a finite-prefix trajectory
factorization; it proves `HasScheduledTimeVaryingIndependentMeanGapLaw` under
`Measure.infinitePi law` with each mean gap integrated against `law t`.

Local APIs/imports are `iIndepFun_rewardTrace_infinitePi`,
`iIndepFun.indepFun_finset`,
`indepFun_fst_snd_compProd_comap_of_indepFun`, `Measure.compProd_map`,
`Measure.fst_compProd`, `Measure.infinitePi_map_eval`, and `integral_map`.
The proof separates the current coordinate from the finite past, transports
independence through the trajectory prefix map, then computes the exact
coordinate marginal. Regularity is Standard Borel loss states/actions,
measurable action singletons, probability coordinate laws, jointly measurable
per-time `[0,1]` evaluators, a Markov trajectory kernel, and finite-prefix
factorization. Retrieval is the common-law producer, the time-varying
expected-gap leaf, and Mathlib independence/kernel/integral cards; theorem
cards are evidence only and the Tsallis weapon is inspiration-only. Failure
policy: nonidentical independent latent-state laws are closed; the concrete
finite-arm stationary-mean reward-law wrapper now compiles downstream, while
history-dependent laws, current-action corruption, and conditional kernels
remain open.

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `TSALLIS-SCHEDULED-INDEPENDENT-NONIDENTICAL-MEAN-GAP` | `Measure.infinitePi law` yields the scheduled independent mean-gap law with round `t` integrated against `law t` | prefix factorization; product-coordinate independence; compProd/comap transport; marginal map/integral APIs | separate current/past coordinates; transport through trajectory prefix; compute coordinate marginal | Standard Borel state/action; measurable singletons; `IsProbabilityMeasure (law t)` for every `t`; measurable bounded evaluator; Markov prefix factorization | common-law/time-varying leaves; Mathlib independence/kernel/integral cards | `leanCompiled` | concrete finite-arm stationary-mean law compiles downstream; history-dependent/current-action/conditional-kernel laws remain separate |

### `LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-TIME-VARYING-CORRUPTED-REWARD-LAW-REGRET`

Status: `leanCompiled` in
`BanditRLProof.TsallisFiniteArmIIDTimeVaryingCorruptedRewardLaw`, root imported
and externally canaried for zero and constant schedules. The final theorem
applies deterministic shifts `rewardShift t arm` to fresh finite-arm IID
reward vectors, clips to `[0,1]`, and proves baseline model-gap logarithmic
regret plus
`sum_(t<=T) sum_(a!=best) (abs (shift t a) + abs (shift t best))`.
No free corruption scalar remains.

Local APIs/imports are the two time-varying supporting leaves, stationary
projection contraction, finite-arm product reward laws, canonical prefix
factorization, and the square-root/harmonic/log self-bound endpoint.
Regularity is probability arm laws, a.e. unit-interval raw rewards, exact
baseline means, positive non-best gaps, a deterministic time-by-arm shift
schedule, finite horizon, within-round arm independence, and IID base rounds.
Retrieval is the stationary corruption route, Mathlib measure/integral and
independence cards, projection contraction, and both Tsallis-INF paper cards;
cards remain evidence only. Failure policy: deterministic time-indexed
oblivious/predictable corruption is closed. Its measurable pre-action-history
generalization now compiles downstream; current-action, latent-law, and
expectation-only-budget corruption still require stronger conditional laws.

## 2026-07-23 History-Adaptive Tsallis Corruption Route

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `TSALLIS-SCHEDULED-REFERENCE-GAP-SELF-BOUNDING` | reference expected-gap law plus pointwise actual/reference predictable gap deviation implies actual-regret self-bound | expected-gap law, simplex probabilities, integral monotonicity, finite sums | expand coordinates, weight pointwise bound, integrate, rewrite reference law, sum | probability trajectory; two bounded measurable predictable losses; finite arms/horizon; deterministic envelope | expected-gap leaves; Mathlib integral/kernel cards | `leanCompiled` | process-specific reference law still required |
| `TSALLIS-SCHEDULED-IID-HISTORY-ADAPTIVE-PREFIX` | state-coordinate-local pre-action-history loss yields canonical IID prefix factorization | predictable environment, trajectory-prefix congruence, prefix extension, kernel map/comap | equal feedback kernels from equal state prefixes; construct Markov prefix kernel | Standard Borel state/action; measurable singletons; bounded measurable loss; coordinate locality | stationary/time-varying IID leaves; Mathlib kernel/independence cards | `leanCompiled` | future-state and nonmeasurable dependence excluded |
| `TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-CORRUPTED-REWARD-LAW-REGRET` | baseline log regret plus explicit deterministic envelope budget for measurable pre-action-history clipped shifts | finite-arm IID law, projection contraction, both supporting leaves, sqrt-schedule endpoint | actual loss regularity; gap deviation; actual prefix law; reference model-gap law on actual measure; self-bound; log tuning | probability arm laws; a.e. bounded raw rewards; exact means; positive gaps; measurable shifts; deterministic envelope; IID base rounds | local corruption chain; Mathlib projection/integral/kernel/independence; Tsallis paper cards | `leanCompiled` | current-action, latent-law, and expectation-only-budget corruption remain open |
| `TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-WINDOW` | three natural horizon/corruption clauses plus `1<=k<=S` imply beta lower, threshold-one, corruption upper/lower, and `C>0` | refined scalar leaf; Mathlib real log/division/order | clear positive denominator; derive `k<=25*S^2`; scale corruption bound; prove log lower side positive | positive horizon/S; `1<=k<=S`; compact three-part window | refined tuning card; Mathlib order/log; Masoudian--Seldin route | `leanCompiled` | scalar conversion closed; one uniform process consumes it; complement and other envelopes remain open |
| `TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-REFINED-CORRUPTED-REWARD-LAW-REGRET` | expose the source envelope-budget self-bound and prove the model-level `sqrt(C*S)` endpoint through a compact window | history-adaptive corruption; refined tuning/window; IID-prefix/reference-gap; Mathlib finite sums/measure/kernel/independence | rebuild actual/reference laws; expose self-bound; prove `armCount<=S` from gaps in `(0,1]`; consume compact window | probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; measurable envelope source; compact window | three parent local leaves; Mathlib finite sums/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | law, scalar conversion, and model composition closed; one uniform family compiles downstream; zero/small corruption, other envelopes, stronger models, and final paper theorem remain open |
| `TSALLIS-FINITE-ARM-IID-UNIFORM-SUBOPTIMAL-BOOST-REFINED-REGRET` | boosting every non-best arm by nonnegative `epsilon` has exact `C=(T+1)*k*epsilon`; a named regime selects the refined endpoint and its complement selects the logarithmic `+C` endpoint | history-adaptive source/budget/log theorem; model `_of_window`; `measurable_of_countable`; Mathlib finite sums/order | define source; prove measurability and exact budget; transport named regime to compact window; split on regime; invoke refined or logarithmic parent theorem | probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; `epsilon>=0`; finite horizon; no caller window proof | two parent local leaves; Mathlib finite sum/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | all regimes closed for uniform family; arm-dependent stationary boosts compile downstream; history-varying envelopes, stronger models, and final paper theorem remain open |
| `TSALLIS-FINITE-ARM-IID-ARM-DEPENDENT-SUBOPTIMAL-BOOST-ALL-REGIMES` | pointwise nonnegative stationary `boost : Fin K -> Real`, with best-arm shift forced to zero, has exact `C=(T+1)*sum_(a!=best) boost(a)`; a named regime selects the refined endpoint and its complement selects logarithmic `+C` | history-adaptive source/budget/log theorem; model `_of_window`; uniform consumer pattern; `measurable_of_countable`; Mathlib finite sums/order | define the arm-dependent source; prove measurability and exact erased-arm/time sum; transport the named regime to the compact window; split on the regime; invoke the refined or logarithmic parent theorem | probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; pointwise nonnegative boost; finite horizon; no caller window proof | compiled parent leaves; uniform finite-sum route; Mathlib finite sums/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | stationary nonuniform boosts are closed; deterministic time-varying schedules compile downstream; random history-adaptive envelopes, stronger models, paper constants, and final paper theorem remain open |
| `TSALLIS-FINITE-ARM-IID-TIME-VARYING-SUBOPTIMAL-BOOST-ALL-REGIMES` | pointwise nonnegative deterministic `boost : Nat -> Fin K -> Real`, with best-arm shift forced to zero, has exact `C=sum_(t<T+1)sum_(a!=best) boost(t,a)`; a named regime selects refined `sqrt(C*S)` and its complement logarithmic `+C` | history-adaptive source/budget/log theorem; model `_of_window`; stationary arm-dependent consumer; `measurable_of_countable`; Mathlib finite sums/order | align initial with `t=0` and successor after history length `n` with `t=n+1`; prove countable measurability; collapse best-arm terms to the double finite sum; rewrite the named regime to the compact window; split and invoke refined/log parents | probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; pointwise nonnegative deterministic schedule; finite horizon; no caller window proof | compiled parent leaves; stationary nonuniform route; Mathlib finite sums/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | deterministic time-and-arm schedules are closed; random history-adaptive envelopes, stronger corruption models, paper constants, and final paper theorem remain open |
| `TSALLIS-FINITE-ARM-IID-PREVIOUS-ACTION-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES` | successor boost reads action `n` from finite pair history and activates `boost(n+1,a)` only when it equals fixed `triggerArm`; exact deterministic envelope budget and all-regimes bound are inherited from the time-varying schedule | history-adaptive source; finite-history coordinate evaluation; `measurable_pi_apply`; `measurableSet_eq_fun`; `Measurable.ite`; time-varying budget/regime/bound; refined/log parents | prove previous-action event measurable; combine best-arm and trigger branches; prove envelope domination; rewrite exact double finite sum; transport named window; split refined/log branches | fixed trigger arm; pointwise nonnegative deterministic schedule; probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; finite horizon | time-varying consumer; history-adaptive parent route; Mathlib finite-product measurability and finite sums/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | previous-action gate closed; general measurable history-arm gates compile downstream; current-action/latent-law corruption, expectation budgets, paper constants, and final theorem remain open |
| `TSALLIS-FINITE-ARM-IID-MEASURABLE-HISTORY-ARM-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES` | an arbitrary initial arm set gates `boost(0,a)`, and every measurable `gate n` on complete finite pair history times candidate arm may gate `boost(n+1,a)`; the full deterministic schedule remains the exact envelope budget and the final theorem covers refined/log regimes | history-adaptive source; `FinitePairHistory`; `MeasurableSet`; `Measurable.ite`; `measurableSet_eq_fun`; `measurable_of_countable`; time-varying budget/regime/bound; refined/log parents | gate the finite-arm initial function; use supplied successor-gate measurability; combine best-arm and gate branches; prove envelope domination; collapse the exact double finite sum; transport named window; split refined/log branches | arbitrary initial arm gate; all-time jointly measurable successor history-arm gates; all-time pointwise nonnegative deterministic schedule; probability arm laws; unit support; exact means; nonempty suboptimal set; gaps in `(0,1]`; finite horizon | previous-action/time-varying consumers; history-adaptive parents; Mathlib measurable sets and finite sums/measure/kernel/independence; both Tsallis paper cards | `leanCompiled` | predictable action and past observed clipped-feedback/loss-coordinate gates are closed under the deterministic envelope; current/raw/latent reward coordinates, realized/expected budgets, horizon-local contracts, `K=1`, paper constants, and final theorem remain open |

## 2026-07-23 Improved Self-Bounding Optimization Route

| leaf | Lean-facing statement | local APIs/imports | proof route | regularity contracts | retrieval evidence | status | failure policy |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `TSALLIS-SCHEDULED-SELF-BOUNDING-INTERPOLATION` | for `lambda in [0,1]`, generated scheduled upper regret plus terminal `gapMass-C <= regret` implies `(1+lambda)*upper-lambda*gapMass+lambda*C` | scheduled expected-probability upper; generated regret integral; `Set.Icc`; ordered multiplication; ring | scale upper by `1+lambda`; scale self-bound by `lambda`; subtract and normalize | probability prior; Standard Borel spaces; finite arms; bounded predictable loss; positive nonincreasing small rates; best arm membership; terminal self-bound | local self-bound/scheduled upper leaves; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; Masoudian--Seldin 2021 equations `self-bounding`, `upperfull` | `leanCompiled` | simplex-constrained quadratic maximization, threshold split, joint lambda optimization, and improved corruption endpoint remain open |
| `TSALLIS-CONSTRAINED-QUADRATIC-OPTIMIZATION` | positive-coefficient finite quadratic sums satisfy unconstrained and active `sum x<=M` branches; finite-simplex expected probabilities instantiate `x=sqrt(p)`, `c=lambda*gap` | interpolation leaf; expected-probability simplex; `Real.sum_sqrt_mul_sqrt_le`; `Real.sq_sqrt`; ordered-field and finite-sum algebra | complete squares; shift coefficient to the active boundary; Cauchy--Schwarz for square-root mass; generated-law specialization | finite decidable arms; active branch has best membership and nonempty erase; `0<lambda`; positive suboptimal gaps; exact threshold | local interpolation/expected-bound leaves; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; Mathlib sqrt-sum theorem; Masoudian--Seldin appendix | `leanCompiled` | across-time branch split, harmonic/log sum, joint lambda choice, and improved square-root corruption endpoint remain open |
| `TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-OPTIMIZATION` | exact finite-time active/inactive and prefix/suffix splits; generated square-root-schedule regret bounded by harmonic base, `lambda*C`, active `sqrt(cutoff)` term, and logarithmic tail | constrained quadratic; refined stability/penalty; sqrt schedule; `Finset.filter/range/Ico`; `AntitoneOn.sum_le_integral_Ico`; `integral_inv` | split each time by threshold; prove a cutoff prefix certificate; identify rate-square base; integrate inverse-square-root prefix and harmonic tail | probability generated law; finite nonempty decidable arms; best membership; nonempty suboptimal set; positive gaps; `lambda in (0,1]`; `0<cutoff<=T+1`; cutoff threshold; terminal self-bound | local constrained/refined/sqrt leaves; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; Masoudian--Seldin 2021 route card | `leanCompiled` | natural cutoff construction, horizon/rounding cases, joint lambda/corruption tuning, and final square-root endpoint remain open |
| `TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-FLOOR-TUNING` | floor the continuous threshold, remove the caller cutoff, and specialize `lambda=1` to generated `C+100*S+25*S*log(2*(T+1)*(K-1)/(25*S^2))` regret | previous cutoff/log theorem; `Nat.floor_pos`; `Nat.floor_le`; `Nat.lt_floor_add_one`; harmonic/log/sqrt algebra | prove floor factor-two sandwich; discharge cutoff threshold/horizon; bound active and tail terms; rewrite `q=25*S^2/(K-1)` | previous generated contracts; nonempty suboptimal set; positive gaps; terminal self-bound; fixed-lambda branch has `lambda in (0,1]`; large horizon `1<=q<=T+1` | previous local leaf; Mathlib floor and real log/sqrt APIs; Masoudian--Seldin general/refined route | `leanCompiled` | general `lambda=1` branch closed; refined `sqrt(C)` branch requires Lambert `W_-1` or equivalent convex-root certificate, absent from pinned Mathlib |
| `TSALLIS-SELF-BOUNDING-BETA-ROOT` | for `g(beta)=C*S/scale*beta-log(beta)-1`, the paper corruption window yields a root in `[1,scale/S^2]` | previous floor-tuning leaf; `Mathlib.Topology.Order.IntermediateValue`; `Real.continuousOn_log`; ordered-field algebra | prove opposite endpoint signs; normalize the upper endpoint; restrict log continuity to positive beta; apply `intermediate_value_Icc` | `0<scale`; `0<S`; `1<=scale/S^2`; `C*S<=scale`; `S*(log(scale/S^2)+1)<=C` | `MLIB-REAL-LOG-SQRT`; `MLIB-ORDER-ALGEBRA`; Mathlib IVT; Masoudian--Seldin route | `leanCompiled` | root existence closed; quantitative root bounds, alpha/lambda transport, coefficient-five reconciliation, and refined `sqrt(C)` regret remain open |
| `TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-TUNING` | coefficient-five local beta root, quantitative weight bound, alpha/lambda threshold transport, and generated explicit `1+log(T+1)+10*sqrt(C*S)*(2+sqrt(log(scale/(C*S))+1))` regret | beta-root and floor-tuning leaves; Mathlib IVT/log/sqrt/order; generated self-bound route | derive local offset `-2`; IVT; elementary `(sqrt(w)-1)^2` estimate; exact scalar rewrites; compose generated theorem | positive scalar data and explicit corruption window; finite supported arms; positive gaps; Standard Borel/probability generated-law contracts; terminal self-bound | previous local leaves; `MLIB-REAL-LOG-SQRT`; `MLIB-ORDER-ALGEBRA`; Masoudian--Seldin route evidence | `leanCompiled` | local endpoint closed; paper ideal constants, complementary windows, model-level corruption/self-bound source, and final Tsallis-INF theorem remain open |
| `TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES` | arbitrary measurable predictable reward shifts have all-regimes regret with `Cexp=sum_t sum_(a!=best) E[p_t(a)(abs shift_t(a)+abs shift_t(best))]`; measurable history-arm gates instantiate it directly; `Fin 1` reduces to `1+log(T+1)` | sample-dependent reference-gap self-bound; realized shift; `frestrictLe`; generated IID-prefix law; expected budget; refined/log consumers | prove shift measurability and clipping deviation; derive bounded integrability; retain `p` through integration; reuse reference gap law; use the refined branch only for nonempty erase plus expected window, otherwise log | probability arm laws; a.e. unit support; exact means; all-time measurable source; finite horizon; gaps in `(0,1]` (vacuous for `K=1`); no caller nonempty/integrability/window premise | local reference-gap/IID-prefix/refined cards; `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL`; `MLIB-PROBABILITY-KERNEL`; `Preorder.measurable_frestrictLe`; `Integrable.of_bound`; Tsallis-INF cards | `leanCompiled` | expected predictable gate-open corruption, `K=1`, and downstream horizon-local packaging are closed; current-action/nonpredictable or latent-law corruption, paper constants, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-IID-HORIZON-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES` | a source with initial data and only `Fin horizon` successor regularity has the same exact generated-policy expected-corruption all-regimes regret bound; supports `horizon=0` and `K=1` | horizon-local source; `FinitePairHistory`; `Fin`; all-time source; expected budget/bound; parent all-regimes theorem | zero-extend successor shifts and envelopes after the horizon; prove measurable/nonnegative/bounded extension by `n<horizon`; expose preservation/zero simp lemmas; reduce the final theorem definitionally to the parent | probability arm laws; a.e. unit support; exact means; initial and horizon-many successor witnesses; gaps in `(0,1]` vacuous for `K=1`; no post-horizon/nonempty/integrability/window premise | parent expected-corruption leaf; `MLIB-FINTYPE-FIN`; finite sums/integrals; probability kernel/independence; Tsallis-INF cards | `leanCompiled` | horizon-local predictable corruption is closed without changing the generated budget; current-action/nonpredictable or raw/latent-law corruption, paper constants, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-REWARD-LAW-REGRET` | time-varying `armLaw(t,a)` with fixed model means yields generated scheduled half-Tsallis logarithmic model-gap regret | finite product `Measure.pi`; `Measure.infinitePi`; clipped coordinate integral; nonidentical mean-gap producer; canonical prefix factorization; independent-mean endpoint | prove every round product loss gap equals `model.gap`; construct generated prefix factorization; transport nonidentical coordinate independence; rewrite to fixed mean-gap law; invoke log consumer | per-time/per-arm probability; a.e. `[0,1]` support; exact fixed model means; positive non-best gaps; finite horizon; nonnegative additive corruption | IID reward-law and nonidentical mean-gap leaves; `MLIB-MEASURE-INTEGRAL`; `MLIB-PROBABILITY-INDEPENDENCE`; Mathlib `Integral.Pi`; Tsallis-INF cards; weapons inspiration only | `leanCompiled`; distinct same-mean alternating-law final-theorem canary | independent nonidentical stationary-mean law is closed; drifting means, dependent arms, conditional/history laws, current-action corruption, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REWARD-LAW-REGRET` | independent `armLaw(t,a)` with armwise mean-deviation envelopes yields generated static-comparator log regret against fixed `model.bestArm` plus the induced explicit gap-deviation budget | product reward law; actual mean integral; independent time-varying mean-gap producer; expected-gap perturbation self-bound; sqrt-schedule endpoint | compute actual product gap; apply two-arm triangle deviation; construct prefix factorization; transport independence; invoke explicit-budget self-bound and log tuning | per-time/per-arm probability; a.e. unit support; deterministic mean envelope; positive non-best baseline gaps; finite horizon | parent nonidentical and time-varying expected-gap cards; Mathlib integral/product/finite sums; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; two-arm drifting-law final canary | fixed-comparator drifting means, explicit budget, compact-window refinement, all-regimes composition, and actual-mean dynamic-comparator consumer closed; conditional/history/dependent laws, current-action changes, sharper or data-derived envelopes, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REFINED-REGRET` | independent drifting-mean laws satisfy the explicit coefficient-aware local `sqrt(C*S)` bound, with `C` the induced mean-deviation budget and comparator fixed to `model.bestArm` | parent generated terminal self-bound; compact `RefinedLocalCorruptionWindow`; scalar-window extractor; refined local optimizer; reciprocal-gap finite sums | instantiate `C`, `S`, arm count, horizon mass; prove arm count <= `S` from positive gaps <=1; extract optimizer inequalities; apply the refined generated endpoint to the parent self-bound | parent law contracts; nonempty non-best arms; gaps in `(0,1]`; finite horizon; compact refined window; no new conditional-law assumption | parent drifting leaf; refined tuning/window cards; finite-sum/log/sqrt/integral/independence routes; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; exact two-arm refined theorem canary | compact-window static-comparator refinement closed; all-regimes and actual-mean dynamic-comparator wrappers compile downstream; sharper or data-derived envelopes, conditional/history/dependent laws, paper constants, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-ALL-REGIMES` | independent drifting-mean laws have one generated fixed-comparator bound selecting refined `sqrt(C*S)` for nonempty/window-positive inputs and logarithmic reciprocal-gap plus `C` otherwise; `Fin 1` simplifies to `1+log(T+1)` | parent log/refined endpoints; exact mean-deviation budget; classical branch split; finite erased-arm sums | define total branch envelope; split on erased-arm nonemptiness and refined window; consume matching parent endpoint; prove unique-arm simplification | parent law contracts; gaps in `(0,1]` vacuous for `K=1`; finite horizon; no caller window/nonempty premise | parent drifting/refined cards; local all-regime patterns; finite-sum/log/sqrt/integral/independence routes; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; no-window two-arm canary; `Fin 1` canary | arm-count and compact-window/fallback branches closed for explicit-envelope fixed-comparator regret; actual-mean dynamic-regret wrapper compiles downstream; sharper or data-derived envelopes, conditional/history/dependent laws, paper constants, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-DYNAMIC-REGRET-ALL-REGIMES` | generated scheduled half-Tsallis expected predictable-environment dynamic regret against a finite argmax of the actual roundwise reward means is at most the fixed all-regimes bound plus the explicit selected-plus-baseline mean-deviation penalty; `Fin 1` simplifies to `1+log(T+1)` | finite actual-mean argmax; moving-comparator regret; fixed-plus-advantage identity; independent product mean-gap law; model best-arm invariant; parent all-regimes theorem | choose `bestAt(t)` by `Finset.exists_max_image`; integrate the moving-comparator decomposition; identify exact actual-mean advantage; bound by two deviation coordinates; compose with fixed all-regimes | per-time/per-arm probability; a.e. unit support; deterministic all-time deviation envelope; baseline gaps in `(0,1]` vacuous for `K=1`; finite horizon; independent arms/rounds; no caller comparator/max/window/nonempty proof | parent drifting/all-regimes cards; `SCN-NONSTATIONARY`; `SCN-BOBW-ADAPTIVE`; finite-sum/integral/independence Mathlib cards; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; max-mean, one-arm, genuinely switching two-arm, and `Fin 1` canaries; the switching canary proves the round-1 maximizer differs from `model.bestArm` and the penalty is positive; cumulative path variation compiles downstream | expected predictable-environment actual-mean dynamic regret closed; realized sample-path regret, horizon-compressed/sharp standard `V_T` or switch-count rates, conditional/history/dependent laws, paper constants, and complete Tsallis-INF remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-PATH-VARIATION-DYNAMIC-REGRET-ALL-REGIMES` | replace the free all-time deviation family by the exact cumulative armwise actual-mean increment sum and prove the generated expected dynamic-regret all-regimes endpoint; `Fin 1` simplifies to `1+log(T+1)` | cumulative actual-mean path variation; triangle induction; initial actual/model mean match; parent dynamic theorem | prove `|mu_t-mu_0|<=sum_(s<t)|mu_(s+1)-mu_s|`; rewrite `mu_0`; specialize parent bound | per-time/per-arm probability; a.e. unit support; round-zero actual/model mean equality; baseline gaps in `(0,1]` vacuous for `K=1`; finite horizon; independent arms/rounds; no caller comparator/max/deviation/window/nonempty proof | parent dynamic card; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; zero, exact one-step `1/2`, `Fin 1`, and switching-law final canaries | exact cumulative envelope closed; sharp/horizon-compressed standard `V_T`, switch-count, realized sample-path, conditional/history/dependent, and complete paper routes remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES` | replace the path-variation envelope by the exact real-valued count of nonzero consecutive population-mean changes per arm and prove the generated expected dynamic-regret all-regimes endpoint; `Fin 1` simplifies to `1+log(T+1)` | bounded-law mean range; real indicator count/filter cardinality identity; path variation; initial actual/model mean match; parent dynamic theorem | identify raw and clipped means; prove means in `[0,1]`; bound each nonzero jump by one; sum and compose with the path theorem; specialize the parent dynamic bound | per-time/per-arm probability; a.e. unit support; round-zero actual/model mean equality; baseline gaps in `(0,1]` vacuous for `K=1`; finite horizon; independent arms/rounds; no caller comparator/max/variation/count/window/nonempty proof | parent path card; finite-sum/order/integral Mathlib cards; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; mean-range, zero, exact one-step count one, path-to-count, `Fin 1`, and alternating-law final canaries | exact per-arm prefix population-mean count closed; global change-point/minimax switch rate, compressed `V_T`, observable/sample count, realized sample path, conditional/history/dependent, and complete paper routes remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES` | replace all armwise switch envelopes by one exact prefix count of rounds where at least one population mean changes, then prove the generated expected dynamic-regret all-regimes endpoint; `Fin 1` simplifies to `1+log(T+1)` | parent armwise switch-count theorem; existential global indicator; `Finset.sum_boole`; filtered cardinality; path/model-deviation adapters; parent dynamic theorem | define the any-arm indicator; identify its finite sum with filtered cardinality; witness the current arm to dominate each armwise indicator; compose path and model-deviation bounds; specialize the parent theorem with the global count repeated across arms | per-time/per-arm probability; a.e. unit support; round-zero actual/model mean equality; baseline gaps in `(0,1]` vacuous for `K=1`; finite horizon; independent arms/rounds; no caller comparator/max/variation/armwise/global-count/window/nonempty proof | parent switch-count card; finite-sum/order/integral Mathlib cards; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only; no prior global declaration or memory hit | `leanCompiled`; root import; focused/tests; zero and exact one-step global counts, one-arm-only switch aggregation, cardinality identity, armwise/path domination, `Fin 1`, and alternating-law final canaries | exact global prefix population-mean change-point envelope closed; minimax/horizon-compressed switch-rate or `V_T`, observable/sample count, realized sample path, conditional/history/dependent, and complete paper routes remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-HORIZON-COMPRESSED-LOG-DYNAMIC-REGRET` | bound generated expected moving-comparator regret by the logarithmic reciprocal-gap term plus `4*(K-1)*(T+1)*globalCount(T)`; `Fin 1` remains `1+log(T+1)` | parent global-count route; count monotonicity; mean-deviation and moving-comparator budgets; exact decomposition; log fixed endpoint; `Finset.range_mono`; `sum_le_sum_of_subset_of_nonneg`; `sum_le_card_nsmul` | prove count monotonicity; compress each decision-time prefix to `globalCount(T)`, excluding the post-horizon transition; derive both factor-two budgets and their factor-four sum; combine the fixed and moving regret pieces | per-time/per-arm probability; a.e. unit support; round-zero actual/model mean equality; positive non-best gaps; finite horizon; independent arms/rounds; no upper gap, caller comparator/deviation/count/window/nonempty proof | parent global-count and drifting-log cards; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA`; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only; no matching local/memory hit | `leanCompiled`; root import; focused/tests; monotonicity, both factor-two budgets, factor-four total, `Fin 1`, and an explicit switching-law final inequality; review had no P0/P1 and both P2/P3 observations were resolved | linear terminal-count algebraic compression closed; minimax/sublinear `sqrt(S*T)` switch rates, sharp `V_T`, observable counts, realized paths, conditional/history/dependent laws, and complete paper route remain open |
| `TSALLIS-FINITE-ARM-NONIDENTICAL-SINGLE-SWITCH-DYNAMIC-COMPARATOR-ADVANTAGE-OBSTRUCTION` | exhibit a bounded independent two-arm law with one permanent mean switch, exact `globalCount(T)=1`, exact comparator advantage `T/4`, exact repeated-prefix penalty `2*T`, and arbitrary-coefficient square-root exceedance | compressed global-count route; actual best-arm argmax; exact mean integrals; `Finset.sum_range_succ`; `Real.sqrt_sq_eq_abs` | instantiate Dirac laws; prove regularity and unique best arms; reduce the global indicator to `0 -> 1`; induct exact sums; use `T=(4*c+1)^2` | concrete `Fin 2`; rational Dirac probability laws; a.e. unit support; initial model match; positive non-best gap at most one; independent nonidentical product route; no caller budget/envelope/comparator | parent compressed/dynamic cards; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only; no prior exact hit | `leanCompiled`; root import; focused/tests; exact count/advantage/penalty, arbitrary-coefficient, and final conjunction canaries | independent comparator-advantage upper-bound route is obstructed; this is not a regret lower bound, minimax lower bound, algorithm impossibility, or Tsallis-INF failure; cancellation-aware or restarted/windowed/change-detection routes remain open |
| `TSALLIS-ORACLE-RESTART-EPOCH-DYNAMIC-REGRET-ASSEMBLY` | prove exact finite epoch-fiber decomposition and assemble per-epoch `C*sqrt(length)` certificates into `C*sqrt(switches+1)*sqrt(horizon+1)` | predictable moving-comparator regret; epoch filters; Mathlib fiberwise sum/cardinality identities; finite sqrt Cauchy--Schwarz | partition the inclusive horizon; preserve the exact summand; conserve cardinality; apply `Real.sum_sqrt_mul_sqrt_le`; sum certificates; use epoch-card/switch-count monotonicity | finite nonempty arms; decidable actions/epochs; finite epoch registry covering every included round; nonnegative coefficient; one pointwise certificate per epoch; no probability/filtration/independence/concentration premises | parent dynamic and one-switch cards; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; nonstationary/BOBW scenarios; Tsallis-INF papers; exact searches returned no prior local hit; weapon inspiration only | `leanCompiled`; root import; focused/tests; concrete two-epoch, unused empty-fiber, exact decomposition, and both external endpoint canaries; independent review clean; baseline axiom audit | generic deterministic assembly closed; generated action law, restart-specific schedule alignment, and epoch expected-regret transport now compile downstream; pathwise estimated-regret certificate production and law-derived schedule-cardinality remain open |
| `TSALLIS-ORACLE-RESTART-GENERATED-TRAJECTORY-ACTION-LAW` | construct a schedule-driven generated half-Tsallis process that resets at boundaries, reads only the inclusive current-epoch suffix otherwise, and identify action `n+1` conditionally on the global prefix | `TsallisScheduledScoreAlignment`; finite pair histories; measurable finite-action sources/kernels; `HistoryAlgorithm`; canonical measurable-environment trajectory and conditional-action law | package continuation-or-boundary starts; measurably reindex `start..n`; branch to initial or local scheduled law; build algorithm/kernel; specialize canonical `condDistrib` theorem | measurable action/singletons; finite nonempty decidable arms; deterministic local eta/schedule; Standard Borel environment/action, nonempty action, and finite prior at endpoint; no reward independence, regret, concentration, comparator, or switch count | restart assembly; scheduled recursive trajectory; `MLIB-PROBABILITY-KERNEL`; `MLIB-FINSET-SUMS`; nonstationary/BOBW scenarios; Tsallis-INF papers; exact searches had no prior restart declaration; weapon inspiration only | `leanCompiled`; root import; focused/tests; both concrete suffix endpoints, canonical reductions, prefix-only and environment-retaining conditional laws, strict positivity; baseline axiom audit; review observations resolved | generated process/action law closed; restart-specific regret, direct schedule fibers, and fixed-comparator first-moment/expected-regret transport compile downstream; pathwise epoch certificate now compiles downstream; expected local stability-plus-penalty control remains open |
| `TSALLIS-ORACLE-RESTART-PREDICTABLE-DYNAMIC-REGRET-ASSEMBLY` | define generated-restart fixed and moving predictable regret; prove never-restart and fixed-plus-moving compatibility; partition by the schedule's own starts; expose schedule-epoch and switch-count square-root endpoints | generated restart probability; parent predictable regret algebra; `OracleRestartSchedule.start`; image epoch registry; generic fiberwise finite-sum/sqrt assembly | use the restart probability in every summand; define epochs as `(range (horizon+1)).image schedule.start`; prove automatic coverage and comparator constancy on fibers; reuse the generic assembly; specialize never-restart and switch-count bounds | finite nonempty decidable arms; deterministic eta/schedule; `best ∈ arms` for fixed-plus-moving; nonnegative coefficient and pointwise epoch certificates for bounds; explicit epoch-cardinality premise for switch endpoint; no fresh epoch law, independence, concentration, or expected-regret premise | generated action-law and generic restart-assembly cards; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; local declaration/retrieval indexes; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; concrete never/every restart epoch registries; both never-restart regret reductions; fixed-plus, exact fiber, and switch endpoint canaries; independent review no P0/P1; baseline axiom audit | pointwise restart regret and schedule alignment closed; fixed-comparator law/expected-regret transport now compiles downstream; pathwise epoch estimated-regret certificates, law-derived schedule-cardinality, fresh independent epochs, concentration, and final generated dynamic regret remain open |
| `TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-FIXED-COMPARATOR-REGRET-TRANSPORT` | prove restart importance-weighted first moments on the actual generated trajectory; identify stored-reward and predictable estimators a.e.; transport both estimated-regret surfaces to fixed-arm environment regret on each schedule fiber; assemble expected epoch certificates into schedule/switch square-root bounds | environment-retaining restart `condDistrib`; strict positive finite-action laws; canonical reward-zero/successor-loss a.e. laws; generic mixed/weighted IW first moments; epoch filters; integral finite sums; point-mass identity; compiled sqrt assembly | specialize the canonical environment-plus-prefix action law; split time zero/successors and boundary/continuation positivity; identify stored reward with predictable loss a.e.; prove measurability/finite-simplex/integrability; sum first moments and a.e. equalities over fibers; rewrite point masses using `schedule.start t=epoch`; transport observed certificates and apply Cauchy | measurable Standard Borel environment/action; measurable singleton, nonempty decidable actions; finite nonempty arms; finite prior; predictable `[0,1]` losses; comparator membership; nonnegative coefficient; explicit predictable or observed expected estimated-regret certificates; explicit epoch-card bound for switch endpoint; no probability prior, independence, stationarity, filtration, concentration, or fresh-run law | generated action-law, restart predictable assembly, scheduled expected-regret cards; `MLIB-PROBABILITY-KERNEL`; `MLIB-MEASURE-INTEGRAL`; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; generic Exp3 first-moment and canonical predictable-feedback APIs; nonstationary/BOBW scenarios; Tsallis-INF papers; weapon inspiration only | `leanCompiled`; root import; focused/tests; first-moment, predictable/observed point-mass epoch integral, and predictable/observed expected switch endpoint canaries; independent review confirms law direction/integrability/claim boundary; baseline axiom audit | conditional-law, observed-to-predictable transport, epoch integral transport, and expected assembly closed; pathwise score/fiber alignment now compiles downstream; exact next blocker is expected local stability-plus-penalty control yielding C*sqrt(fiber.card) under the global restart law; law-derived schedule-cardinality and final generated dynamic regret remain open |
| `TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-SCORE-ALIGNMENT` | align every actual restart probability and stored-reward IW loss with scheduled local time on a shifted path; prove each visited epoch fiber is a contiguous translated inclusive range with exact cardinality; transport actual observed point-mass epoch estimated regret to the scheduled pathwise FTRL stability-plus-penalty bound | `TsallisOracleRestartExpectedRegret`; scheduled score/FTRL certificate; restart schedule start laws and fibers; `Finset.max'`; `Finset.sum_image`; `Finset.card_image_of_injective` | shift the global trajectory at the epoch start; split zero/boundary/continuation probability definitions; identify observed estimators; prove start monotone/idempotent and fibers contiguous; reindex the fiber sum; reuse the scheduled time-varying FTRL endpoint | finite nonempty decidable arms; deterministic valid schedule and eta; visited epoch; best-arm membership; eta positive and nonincreasing at local times; inclusive horizons; no measure, prior, measurability, integrability, reward independence, concentration, or fresh epoch law | restart expected-regret and generated-action-law leaves; scheduled score-penalty and time-varying penalty leaves; `MLIB-FINSET-SUMS`; Mathlib finite-set APIs; Tsallis-INF paper cards; theorem cards evidence only and weapons inspiration-only | `leanCompiled`; root import; focused/root/Tests.Basic; external shift/fiber/certificate canaries; independent review; public-import axiom audit baseline only | pathwise score alignment, automatic fiber reindex/cardinality, and actual epoch FTRL stability-plus-penalty certificate closed; expected `C*sqrt(fiber.card)` control must be proved under the one global restart law without fresh-epoch independence; law-derived epoch-cardinality and final dynamic regret remain open |
| `TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-EXPECTED-STABILITY-TRANSPORT` | transport actual restart-local stored-reward half-Tsallis stability through the one global generated conditional action law; prove successor coarse/refined and global-time-zero endpoints; sum a contiguous probability-prior prefix; integrate the actual observed epoch FTRL certificate | `TsallisOracleRestartScoreAlignment`; environment-plus-global-prefix restart `condDistrib`; generic coarse/refined stability integrals; stored-reward/predictable a.e. equality; `IntegrabilitySums`; `ExpectationBochnerSums`; `integral_mono_ae` | retain the global prefix; use shifted trajectories only for deterministic reindexing; identify observable and predictable scores a.e.; apply coarse/refined condDistrib APIs; split time zero; sum mass-scaled one-round bounds; derive epoch start equality from the fiber; integrate the pathwise certificate | measurable Standard Borel environment/action; measurable singletons; nonempty decidable actions; finite nonempty arms; deterministic schedule/eta; predictable `[0,1]` loss; positive local eta and `eta<=1/2` for refined successors; finite prior for mass-scaled endpoints; probability prior for literal card/final epoch bound; no independence, stationarity, filtration, concentration, fresh epoch law, or shifted-law equality | score-alignment, generated action-law, fixed-comparator transport, scheduled all-rate stability cards; `MLIB-PROBABILITY-KERNEL`; `MLIB-MEASURE-INTEGRAL`; `MLIB-FINSET-SUMS`; Mathlib condDistrib/integral/finite-sum APIs; Tsallis-INF papers; theorem cards evidence-only and weapons inspiration-only | `leanCompiled`; root import; focused/Tests.Basic; finite-prefix and final-epoch external canaries; independent review findings resolved; public-import axiom audit baseline only | global-law coarse/refined one-round transport, time zero, coarse prefix summation, and linear-card actual observed epoch expected certificate closed; refined finite-sum control and local-rate/penalty tuning to `C*sqrt(fiber.card)` remain open; law-derived epoch cardinality and final dynamic regret remain separate |
| `TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-REFINED-STABILITY-TUNING` | tune the actual square-root-schedule epoch to `E[observed estimated regret] <= (8*sqrt(K))*sqrt(epochRounds.card)` | global-law refined transport; erased-arm sqrt mass; refined potential penalty; inverse-root prefix; epoch cardinality | bound successors, sum schedule budgets, handle actual boundary time zero, bound terminal mass, combine pathwise FTRL, erase local-horizon witness | probability prior; existing Standard Borel/action/arm/schedule/loss contracts; supported comparator; visited epoch; no caller eta contracts or fresh law | parent local/refined/sqrt cards; Mathlib finite sums, sqrt, cardinality, and integrals; Tsallis-INF route evidence; weapons inspiration-only | `leanCompiled`; root/focused/tests; external cardinality canary; declaration indexed; baseline-only axiom audit | local `C*sqrt(fiber.card)` closed with `C=8*sqrt(K)`; law epoch count, concrete dynamic regret, sharp constants, and complete Tsallis-INF remain separate |
| `TSALLIS-ORACLE-RESTART-GENERATED-DYNAMIC-REGRET` | generated predictable moving-comparator regret is integrable and at most `8*sqrt(K)*sqrt(scheduleEpochs.card)*sqrt(T+1)`; with explicit `scheduleEpochs.card<=switches+1`, at most `8*sqrt(K)*sqrt(switches+1)*sqrt(T+1)` | refined restart tuning; observed epoch certificate; observed-to-predictable schedule/switch assembly; integrals | instantiate coefficient `8*sqrt(K)`; discharge nonnegativity; supply every epoch certificate from membership and comparator support; invoke compiled finite Cauchy assembly | probability prior; Standard Borel measurable environment/action; measurable singleton/nonempty decidable action; finite nonempty arms; valid deterministic schedule; predictable `[0,1]` losses; supported epoch comparator; explicit epoch-count premise only for switch theorem | local refined/fixed-comparator/predictable-assembly cards; generic restart assembly; `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL`; `MLIB-REAL-LOG-SQRT`; Tsallis-INF papers; theorem cards evidence-only, weapons inspiration-only | `leanCompiled`; root/focused/tests; external switch canary; baseline-only axiom audit | generated schedule-cardinality and explicit switch endpoints closed; law-derived epoch count, concrete restart selection, optimal constants, and complete Tsallis-INF remain open |
| `TSALLIS-ORACLE-RESTART-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET` | exact change-point schedule registry/cardinality; within-epoch population-mean constancy; epoch-start raw-mean and clipped-loss maximizer optimality; concrete independent-law `E[R_T^dyn] <= 8*sqrt(K)*sqrt(globalMeanSwitchCount(T)+1)*sqrt(T+1)` | generated restart endpoint; global mean-count law; `OracleRestartSchedule`; finite best arm; independent reward-vector law; clipped-loss mean-gap identification; `Measure.infinitePi`; Finset range/filter/image/card | recursively restart after each change; induct exact epoch set; count successor image; specialize to global arm-mean changes; induct mean constancy; transport maximizer; use unit support to rewrite the clipped-loss gap as the raw-mean difference; rewrite generated endpoint by exact count | finite-bandit model; probability law per time/arm; a.e. `[0,1]` reward support; independent product environment; clipped reward loss; finite horizon; complete population-mean law oracle; no caller schedule/comparator/count, initial-model/gap, filtration, or concentration premise | parent generated/global-count cards; `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL`; `MLIB-REAL-LOG-SQRT`; pinned Finset APIs; Tsallis-INF papers; weapon inspiration-only; no prior memory hit | `leanCompiled`; root/focused/tests; external count/raw-mean-optimality/clipped-loss-optimality/final-signature canaries; declaration indexed; baseline-only axiom audit; independent-review support mismatch resolved | full-law population-mean oracle route under unit support closed; observed detector, delay/false alarms, high-probability/realized regret, dependent laws, constants, and complete Tsallis-INF remain open |
| `OFUL-MEASURABLE-RECURSIVE-SELECTION` | strict-fold measurable `Fin K` optimistic action; deterministic history algorithm; canonical successor-action and chosen-feature a.e. alignment | finite-action optimism; `ETC.realArgmaxCommit`; canonical trajectory; deterministic kernels; conditional-law/compProd APIs; `ae_map_iff` | prove maximum and coordinatewise measurability; package the Dirac policy; identify the canonical history/action joint law; prove selector-graph support; pull back to trajectories; map action equality through candidate features | `0<K`; Standard Borel nonempty reward at the process endpoint; finite decidable features; fixed-action score coordinates measurable; no confidence, MGF, integrability, or regret premise | local OFUL optimism and measurable-policy cards; Mathlib kernel basic/measure-compProd; Abbasi-Yadkori et al.; weapon inspiration-only | `leanCompiled`; root/focused/Tests and external canary; independent review resolved; baseline axiom audit and full check passed; concrete ridge consumer now compiled | tie-breaking and recursive alignment closed; generic confidence and width summation compile separately; concrete confidence/index hookup and OFUL regret remain open |
| `OFUL-CONCRETE-HISTORY-RIDGE-SELECTION` | concrete scalar-ridge state and score from inclusive finite history; deterministic algorithm; canonical actual-feature/selected-feature a.e. alignment | measurable recursive selection; finite-history coordinate maps; finite sums/products; determinant, adjugate, nonsingular inverse; finite-horizon Gram/response/ridge/radius | prove entrywise matrix and inverse measurability; extract observed arm features and responses; instantiate horizon `n+1`; discharge fixed-arm score measurability; reuse selector graph transport | `0<K`; finite decidable features; deterministic `Fin K` arm features; Real rewards; arbitrary valid `HistoryEnvironment`; arbitrary `lambda/R/delta/S`; no positivity, confidence, MGF, filtration, integrability, or regret premise | local measurable-selection, finite-action optimism, scalar-bias and measurable-quantity cards; Mathlib matrix determinant/adjugate/inverse; Abbasi-Yadkori et al.; weapon inspiration-only | `leanCompiled`; focused/root/Tests and external boundary/terminal canaries; independent review resolved; baseline axiom audit and full check passed | concrete score measurability and recursive selected-feature alignment closed; exact canonical `n` to `n+1` state and successor-gap transport compile downstream; generated confidence-law probability and OFUL regret remain open |
| `OFUL-UNIFORM-TIME-CONFIDENCE` | scheduled scalar-ridge confidence-failure union over exactly `n<=horizon`; simultaneous-confidence complement; equal-share total probability at most `delta` | scalar regularization bias; fixed-horizon confidence ellipsoid; finite union-bound wrappers; `Finset.range/card`; `ENNReal.ofReal` | name fixed-time events; union over `range(horizon+1)`; restrict horizon-local assumptions to each `n`; sum scheduled budgets; specialize to `delta/(horizon+1)` | Standard Borel probability space; finite decidable nonempty features; `0<lambda`; parameter norm bound; filtration-predictable features; strongly adapted zero-initialized noise; projection bounds; common-`R` conditional sub-Gaussian and response laws below `horizon`; `0<R`; scheduled levels in `(0,1]` or `0<delta<=1`; no independence, stationarity, feature ceiling, stopping time, process hookup, or regret premise | local scalar-bias, confidence-ellipsoid, and probability-union cards; Mathlib Finset/measure APIs; Abbasi-Yadkori et al.; weapon inspiration-only | `leanCompiled`; focused/root/Tests; scheduled/equal-share/membership/zero-horizon external canaries; independent review resolved; baseline axiom audit and full check passed | deterministic finite-window confidence budgeting closed; its good-event surface now feeds the canonical successor-gap implication; canonical feature/noise/response law contracts are still required to obtain the generated-process probability bound |
| `OFUL-ALL-TIME-TELESCOPING-SCALAR-RIDGE-CONFIDENCE` | one countable scalar-ridge confidence-failure event over every deterministic horizon with exact schedule `delta/((n+1)*(n+2))` and total probability at most `delta` | fixed-time scalar-ridge confidence; countable outer-measure subadditivity; `ENNReal.tsum_le_tsum`; reciprocal telescope; Real/NNReal/ENNReal `HasSum` transport | union fixed-time events over Nat; restrict all-time MGF/response laws to each horizon; telescope `1/((n+1)(n+2))`; prove exact ENNReal budget; specialize the scheduled theorem | Standard Borel probability space; finite decidable nonempty features; `0<lambda`, `0<R`, `0<delta<=1`; theta norm bound; filtration-predictable features; strongly adapted zero-initialized noise; nonnegative projection domination; all-time conditional sub-Gaussian and response laws; no independence, stationarity, bounded rewards, event measurability, stopping time, generated policy, feature ceiling, or regret integrability | local uniform/fixed-time confidence and self-normalized cards; `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-MARTINGALE-STOCHASTIC`; `MLIB-MEASURE-INTEGRAL`; Abbasi-Yadkori et al.; textbook/scenario; weapon inspiration-only; no targeted local schedule hit | `leanCompiled`; root imported; focused/root/Tests; exact-budget and full-terminal external canaries; declaration indexed; baseline axiom audit; independent review found no correctness/P0/P1 issue and both ledger findings were resolved; full check passed | one-process deterministic-horizon-uniform confidence closed and consumed by the scheduled canonical route; do not identify the older horizon-dependent generated family with one policy or claim stopping-time/regret conclusions |
| `OFUL-SCHEDULED-GENERATED-TRAJECTORY-ALL-TIME-CONFIDENCE-GAP-TAIL` | one fixed telescoping-schedule history policy; actual-feature all-time confidence; existential successor optimism-gap violation probability at most `delta` | all-time telescoping confidence; generic measurable strict-fold history algorithm; concrete ridge score/state; strict-past filtration; predictable residual; finite-action projection cap; trace-state identities; finite-history optimism; a.e. event transport | use `deltaAt(n+1)` at selector index `n`; package one algorithm; prove scheduled predictable/actual feature alignment and residual adaptedness; apply all-time confidence to predictable features; transport events; prove every fixed successor gap; use `ae_all_iff`; include the existential violation event in the countable failure event | `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`, `0<delta<=1`; theta norm bound; valid Real history environment; all-time scheduled predictable-residual conditional sub-Gaussian MGF on the same generated measure; no independence, stationarity, bounded rewards, feature ceiling, integrability, event measurability, cumulative width, stopping time, or regret | all-time confidence, concrete history selection, predictable-residual, and environment-law local cards; Mathlib measure/sub-Gaussian/martingale/kernel APIs; OFUL paper/textbook/scenario; weapon inspiration-only; no targeted scheduled-algorithm hit | `leanCompiled`; root imported; focused/root/Tests; all 28 declarations and external confidence/full-gap-tail canaries pass; review, axiom audit, declaration/JSON indexing, and full check recorded before handoff | scheduled policy/index/measurability/actual-feature confidence/existential gap-tail closed; its concrete scheduled environment-law producer now compiles downstream; cumulative all-horizon regret and stopping-time evaluation remain open |
| `OFUL-SCHEDULED-HISTORY-ENVIRONMENT-LINEAR-SUBGAUSSIAN-REWARD-LAW` | construct the scheduled all-time residual law from `CanonicalLinearSubgaussianEnvironmentLaw`; prove direct environment-backed actual confidence and existential successor-gap tails | algorithm-parametric canonical initial/successor reward map, `condDistrib`, and trimmed `condExpKernel.map` laws; scheduled history-step reward marginal; centered conditional-MGF transport; compiled scheduled tail | require a Dirac equality for the generic initial-action bridge; condition successors on `frestrictLe n`; rewrite the history-step marginal to `environment.feedback` at the scheduled action; match the linear center to the scheduled predictable feature; transport to the before-filtration; apply the all-time consumers | `0<K`; finite decidable Feature and nonempty Feature at the confidence endpoint; `0<lambda`, `0<R`, `0<delta<=1`; theta norm bound; initial and every history/action feedback section sub-Gaussian around the linear center; no independence, stationarity, bounded rewards, feature ceiling, integrability, event measurability, cumulative width, stopping time, or regret | scheduled all-time and constant-parameter environment-law local cards; `MLIB-PROBABILITY-KERNEL`; `MLIB-PROBABILITY-POSTERIOR`; `MLIB-CONDITIONAL-EXPECTATION`; `MLIB-PROBABILITY-SUBGAUSSIAN`; OFUL paper/textbook/scenario; weapon inspiration-only; no scheduled producer hit | `leanCompiled`; root imported; focused/root/Tests.Basic pass; nine declaration checks and producer/direct-confidence/direct-gap canaries; public axiom audit baseline only; independent review no P0/P1; full check passed | scheduled kernel-to-conditional-MGF and direct environment-backed all-time tails closed; next prove a uniform terminal-radius envelope for varying telescoping budgets and combine it with deterministic selected-width summation for an all-horizon cumulative-gap tail; stopping-time evaluation remains separate |
| `OFUL-SELECTED-WIDTH-SUMMATION` | selected-action cumulative clipped confidence width at the standard `sqrt(T)*sqrt(2*d*log(1+T*L2/(d*lambda)))` budget; raw-width specialization under `width<=1` | confidence-width definition; prefix regularized Gram positivity; inverse-quadratic nonnegativity; standard log elliptical potential; finite Cauchy--Schwarz | identify clipped inverse-quadratic width with `min 1 confidenceWidth`; apply Cauchy to clipped updates; consume the log potential; specialize a generic feature sequence to `actionFeature(selectedAction t)` | finite decidable nonempty features; `0<lambda`; `0<=L2`; selected-feature squared norm `<=L2` before `T`; raw endpoint additionally assumes width `<=1`; arbitrary nonmeasurable action type; no probability/filtration/response/confidence/policy law/regret | local elliptical-potential, optimism, and adjacent concrete-history cards; `MLIB-FINSET-SUMS`; `MLIB-CONVEX-LINALG`; `MLIB-REAL-LOG-SQRT`; textbook/OFUL paper/scenario cards; weapon inspiration-only | `leanCompiled`; focused/root/Tests; clipped/raw selected-action and zero-horizon canaries; baseline axiom audit; independent review and full check passed | deterministic selected-action width sum closed; the full actual-prefix radius-width consumer compiles under the explicit premise, and the normalized downstream consumer now discharges it under `L2<=lambda`; initial round and bad-event integration remain |
| `OFUL-GENERATED-TRAJECTORY-CONFIDENCE-GAP-TRANSPORT` | exact inclusive-history `n` to generic-horizon `n+1` Gram/response/estimate/radius transport; concrete strict-fold one-step gap; cumulative true linear gap over actual rounds `1..horizon` conditional on the equal-share uniform-confidence good event | concrete history ridge selection; uniform-time confidence event semantics; selector-independent score-max gap; canonical successor-action alignment; finite sums | prove trace-coordinate identities; rewrite all ridge-state quantities; consume the strict-fold score maximum directly; intersect fixed-time a.e. statements; apply the uniform good-event membership theorem; sum over `Finset.range horizon` with action index `n+1` | `0<K`; finite decidable nonempty Feature; `0<lambda`; deterministic arm features; arbitrary theta/R/delta/S/comparator and valid Real-reward `HistoryEnvironment`; no feature ceiling, filtration, conditional MGF, response/noise law, independence, integrability, or delta positivity for the implication | local concrete-history, uniform-confidence, finite-action optimism, and selected-width cards; `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL`; `MLIB-CONVEX-LINALG`; OFUL paper/textbook/scenario cards; weapon inspiration-only | `leanCompiled`; focused/root/Tests; external response/estimate/radius, fixed-time, cumulative, and true zero-horizon terminal canaries; independent review findings resolved; baseline axiom audit and full check passed | exact state/index and successor good-event gap assembly closed; explicit probability and standard radius-width consumers compile downstream; do not equate strict-fold with `Classical.choose`, include time zero, integrate bad events, or call this OFUL regret |
| `OFUL-GENERATED-TRAJECTORY-UNIFORM-CONFIDENCE-GAP-TAIL` | package canonical scalar-ridge confidence regularity; specialize the equal-share failure probability to the canonical measure; prove the strict successor-gap violation event has measure at most `ofReal delta` | generated confidence-gap transport; uniform-time confidence; canonical trajectory probability instance; `measure_mono_ae`; conditional sub-Gaussian API | instantiate uniform confidence from the source; combine its failure bound with the a.e. good-event gap implication; show strict violation implies confidence failure almost everywhere; apply measure monotonicity | `0<K`; finite decidable nonempty Feature; deterministic arm features; valid Real-reward `HistoryEnvironment`; `0<lambda`, `0<R`, `0<delta<=1`; source-provided parameter norm, filtration-predictable actual features, shifted adapted residual noise, projection bounds, common-`R` conditional MGF, and pointwise response law; no independence, stationarity, feature ceiling, supplied integrability, stopping time, or anytime premise | generated gap, uniform confidence, concrete history, and optimism local cards; `MLIB-MEASURE-INTEGRAL`; `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-FINSET-SUMS`; OFUL paper/textbook/scenario; weapon inspiration-only | `leanCompiled`; focused/root/Tests; full terminal and empty zero-horizon event canaries; declaration indexed; baseline axiom audit; independent review | explicit-source canonical failure probability and successor-gap `delta` tail closed; predictable residual, concrete environment, standard radius-width, and normalized no-hwidth consumers compile downstream; initial round, expected bad-event loss, and regret remain |
| `OFUL-GENERATED-TRAJECTORY-PREDICTABLE-RESIDUAL-CONFIDENCE` | strict-past canonical filtration; pointwise predictable scalar-ridge selected feature; all-time a.e. actual-feature alignment; predictable residual; reduced-law actual confidence and successor-gap `delta` tails | explicit-source canonical tail; `Filtration.piLE`; finite-history selector measurability; canonical successor feature alignment; `ae_all_iff`; event congruence | use bottom at time zero and `piLE n` at time `n+1`; compose the strict-fold selector with `frestrictLe`; prove initial Dirac and successor alignment; derive residual adaptedness, response identity, and finite-action projection ceiling; run uniform confidence on the predictable feature; transport events a.e. to actual features | `0<K`; finite decidable nonempty Feature; deterministic arm features; valid Real-reward environment; `0<lambda`, `0<R`, `0<delta<=1`; `euclideanLength thetaStar<=S`; horizon-local strict-past residual conditional sub-Gaussian MGF witnesses; no `Countable Real`, independence, stationarity, feature ceiling, caller predictability/adaptedness/response/integrability, stopping time, or anytime premise | explicit-source/gap/concrete-history local cards; `MLIB-CONDITIONAL-EXPECTATION`; `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-MEASURE-INTEGRAL`; `MLIB-FINSET-SUMS`; Mathlib `Filtration.piLE`; OFUL paper/textbook/scenario; weapon inspiration-only | `leanCompiled`; root/focused/Tests; external source/all-time-alignment/terminal canaries; declaration indexed; baseline-only axiom audit; independent review found no P0-P2 issue | strict-past predictability, residual regularity, finite projection control, actual confidence transport, and reduced-law successor-gap tail are closed; concrete kernel production, standard radius-width tail, and normalized width discharge now compile downstream; initial round, expected bad-event loss, and regret remain |
| `OFUL-HISTORY-ENVIRONMENT-LINEAR-SUBGAUSSIAN-REWARD-LAW` | concrete initial/successor reward laws; Real trimmed `condExpKernel.map`; predictable residual conditional-MGF; direct successor-gap delta tail | canonical trajectory laws; deterministic OFUL policy; `condDistrib_comp`; rational `Iic`; frozen center; predictable-residual confidence | project pair laws through `Prod.snd`; reconstruct Real measures from rational rays; freeze the prefix-measurable center; consume per-section centered sub-Gaussian laws; invoke the tail | `0<K`; finite decidable Feature; Markov Real reward environment; theta norm; initial-arm and all history/action feedback sections centered sub-Gaussian with proxy `R^2`; terminal confidence contracts; no `Countable Real`, independence, stationarity, stopping time, or anytime premise | predictable-residual/concrete-history/conditional-expectation cards; Mathlib Condexp/CondDistrib/Borel Real/SubGaussian; OFUL paper; weapon inspiration-only | `leanCompiled`; root/focused/Tests canary; declaration and JSON indexed; independent review, baseline axiom audit, and full check passed | concrete stochastic source closed; its standard radius/full-prefix width and normalized no-hwidth successor-gap tails compile; Markovness alone is insufficient; initial round, bad-event envelope, and complete regret remain |
| `OFUL-GENERATED-TRAJECTORY-STANDARD-RADIUS-WIDTH-GAP-TAIL` | standard log-det budget, uniform radius upper, selected-width budget, exact scalar/prefix Gram equality, deterministic successor-gap violation event, and concrete `measure <= ofReal delta` | history-environment linear-sub-Gaussian law; selected-width summation; standard log elliptical potential; scalar confidence radius; `Finset.sum_range_succ'`; log/exp/sqrt monotonicity; measure monotonicity | dominate every prefix radius `n<=T`; instantiate width summation on the full actual prefix with `T=horizon+1`; remove only the nonnegative time-zero radius-width term; include the deterministic violation event in the existing random radius-width event | `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`, `0<delta<=1`; `0<=S`, `0<=L2`; arm-feature norm ceiling; explicit pathwise raw `confidenceWidth<=1` before `horizon+1`; concrete linear-sub-Gaussian environment law; no `Countable Real`, independence, stationarity, stopping time, or anytime premise | history-environment, selected-width, predictable-residual, and standard-log local cards; `MLIB-FINSET-SUMS`; `MLIB-CONVEX-LINALG`; `MLIB-REAL-LOG-SQRT`; `MLIB-MEASURE-INTEGRAL`; OFUL paper/textbook/scenario; weapon inspiration-only | `leanCompiled`; focused/root/Tests and external theorem canaries; declaration indexed; independent review P3 attribution fix resolved; baseline-only axiom audit; full check passed | radius/index/deterministic successor-gap tail closed; keep this base theorem's raw-width premise and use the normalized downstream wrapper under `L2<=lambda`; do not charge successor-only Grams, include time zero, integrate bad-event loss, or claim complete regret |
| `OFUL-GENERATED-TRAJECTORY-NORMALIZED-RADIUS-WIDTH-GAP-TAIL` | scalar-ridge `xᵀV⁻¹x<=1`; general and canonical `confidenceWidth<=1`; standard successor-gap `measure<=ofReal delta` without caller `hwidth` | regularized Gram PosDef and inverse nonnegativity; inverse cancellation; exact Gram quadratic energy; finite Cauchy--Schwarz; `Real.sqrt_le_one`; standard radius-width tail | set `z=V⁻¹x`; derive `lambda*||z||²<=xᵀz`; combine `q²<=||x||²||z||²` with `||x||²<=lambda`; use `q>=0` to get `q<=1`; compose arm norm `<=L2<=lambda`; reuse deterministic and measure consumers | `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`, `0<delta<=1`; `0<=S`, `0<=L2`; arm-feature norm ceiling; explicit `L2<=lambda`; concrete linear-sub-Gaussian environment law; no pathwise width, `Countable Real`, independence, stationarity, stopping time, or anytime premise | standard radius-width, selected-width, and standard-log local cards; `MLIB-CONVEX-LINALG`; `MLIB-FINSET-SUMS`; `MLIB-REAL-LOG-SQRT`; OFUL paper/textbook/scenario; weapon inspiration-only; targeted retrieval found no direct finite-matrix inverse-Loewner API | `leanCompiled`; focused/root/Tests and external declaration/terminal canaries; declaration index passed; independent review found no P0-P2 issue and both P3 findings resolved; baseline-only axiom audit; full check passed | normalized width discharge and no-hwidth successor-gap tail closed; do not drop `L2<=lambda`, include time zero, integrate bad-event loss, or claim complete regret; next initial-round accounting |
| `OFUL-GENERATED-TRAJECTORY-ALL-ROUND-STANDARD-GAP-TAIL` | finite Cauchy linear-value envelope; canonical time-zero gap charge; complete `0..horizon` standard cumulative-gap violation event; concrete `measure<=ofReal delta` without caller `hwidth` | normalized successor tail; fixed initial-arm a.e. law; `Real.sum_mul_le_sqrt_mul_sqrt`; `Finset.sum_range_succ'`; `measure_mono_ae` | prove `|thetaᵀx|<=||theta||*||x||`; charge any two-arm gap by `2*S*sqrt(L2)`; transport the fixed initial arm almost surely; split the all-round sum and reduce its violation to the normalized successor event | `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`, `0<delta<=1`; `0<=S`, `0<=L2`; arm norm ceiling; `L2<=lambda`; concrete linear-sub-Gaussian environment law; no pathwise width, `Countable Real`, independence, stationarity, stopping time, or anytime premise | normalized and predictable-residual local cards; `MLIB-FINSET-SUMS`; `MLIB-CONVEX-LINALG`; `MLIB-REAL-LOG-SQRT`; OFUL paper/textbook/scenario; weapon inspiration-only | `leanCompiled`; focused/root/Tests and external declaration/terminal canaries; declaration/JSON checks; independent review no P0-P3; baseline-only axiom audit; full check passed; expected pseudo-regret consumer compiled downstream | initial-round accounting and all-round high-probability tail closed; use the downstream measurable-envelope theorem for expectation integration; do not infer expected regret from this tail alone |
| `OFUL-GENERATED-TRAJECTORY-EXPLICIT-HIGH-PROBABILITY-PSEUDOREGRET-RATE` | exact radius at `delta/(T+1)`; displayed finite-window budget `2*S*sqrt(L2)+2*(R*sqrt(B_T+2*log((T+1)/delta))+sqrt(lambda)*S)*sqrt(T+1)*sqrt(2*B_T)`; nonnegative fixed-optimal-arm pseudo-regret and strict exceedance probability `<=ofReal delta` | all-round tail; fixed-optimal-arm gap nonnegativity; standard log-det/radius/width definitions; Real log/sqrt identities | prove `log(sqrt(exp B_T)/(delta/(T+1)))=B_T/2+log((T+1)/delta)`; factor `R^2`; unfold the all-round budget; rewrite the existing violation set and specialize its comparator | unchanged canonical contracts: `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`, `0<delta<=1`; `0<=S`, `0<=L2`; arm ceiling; `L2<=lambda`; certified optimal arm; canonical linear-sub-Gaussian law; no pathwise width, caller integrability, countability, independence, stationarity, stopping time, anytime, supplied conditional MGF, or uniform-over-parameter claim | all-round/expected/explicit-expected local cards; `MLIB-REAL-LOG-SQRT`; `MLIB-EXP-LOG-INEQUALITIES`; `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL`; OFUL paper/textbook/scenario; weapon inspiration-only; targeted retrieval no hit; missing BRL task file recorded as metadata debt | `leanCompiled`; focused/root/Tests; all six signature checks; radius and terminal proof canaries; independent-review P2 statement-index truncation resolved with bracket-aware parser and regression test; baseline-only axiom audit; full check passed | explicit finite-window high-probability pseudo-regret rate closed; do not call it anytime, simultaneous all-horizon, minimax, contextual/dynamic, uniform-over-parameter, or one-policy consistency |
| `OFUL-GENERATED-TRAJECTORY-EXPECTED-PSEUDOREGRET` | measurable/integrable complete gap sum; deterministic all-round envelope; generic bad-event expectation split; concrete `budget+envelope*delta`; nonnegative fixed-optimal-arm pseudo-regret; tuned outer budget `delta_T=1/(T+1)` endpoint | all-round gap tail; canonical action measurability; finite sums; `Integrable.of_bound`; measurable indicators and Bochner integrals; ENNReal-to-Real tail conversion | bound absolute per-round gaps by `2*S*sqrt(L2)`; integrate `budget + bad.indicator envelope`; evaluate the indicator integral; consume the all-round `ofReal delta` tail; certify the optimal arm; cancel `(T+1)` at the canonical outer budget; algorithm parameter is `1/(T+1)^2` | `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`; `0<=S`, `0<=L2`; arm norm ceiling; `L2<=lambda`; certified optimal fixed arm; concrete linear-sub-Gaussian law; no caller delta for tuned endpoint, pathwise width, `Countable Real`, independence, stationarity, stopping time, anytime, or supplied integrability | all-round local card; `MLIB-MEASURE-INTEGRAL`; `MLIB-FINSET-SUMS`; `MLIB-CONVEX-LINALG`; `MLIB-REAL-LOG-SQRT`; OFUL paper/textbook/scenario; weapon inspiration-only; targeted local memory search had no hit | `leanCompiled`; focused/root/Tests; generic, explicit-delta, exact/zero-horizon cancellation, and tuned canaries; independent-review findings resolved; baseline-only axiom audit | finite-window expected fixed-optimal-arm pseudo-regret and delta tuning closed; the downstream explicit finite-window and fixed-model asymptotic presentations now compile; minimax, anytime, contextual, dynamic, uniform-over-parameter, and unrestricted linear-bandit regret remain separate |
| `OFUL-GENERATED-TRAJECTORY-EXPLICIT-EXPECTED-PSEUDOREGRET-RATE` | exact algorithm parameter `1/(T+1)^2`; explicit confidence radius `R*sqrt(B_T+4*log(T+1))+sqrt(lambda)*S`; nonnegative expected pseudo-regret bounded by the fully displayed radius-width expression | expected pseudo-regret endpoint; standard log-det/radius/width definitions; Real log/sqrt identities; field/ring normalization | prove outer-budget square identity; expand `log(sqrt(exp B)*(T+1)^2)`; factor `R^2`; unfold radius-width and initial charges; rewrite the generated theorem | unchanged expected-route contracts: `0<K`; finite decidable nonempty Feature; `0<lambda`, `0<R`; `0<=S`, `0<=L2`; arm ceiling; `L2<=lambda`; optimal fixed arm; concrete linear-sub-Gaussian law; no caller delta, pathwise width, countability, independence, stationarity, stopping time, anytime, or supplied integrability | expected/all-round local cards; `MLIB-REAL-LOG-SQRT`; `MLIB-EXP-LOG-INEQUALITIES`; `MLIB-FINSET-SUMS`; `MLIB-CONVEX-LINALG`; `MLIB-MEASURE-INTEGRAL`; OFUL paper/textbook/scenario; weapon inspiration-only; targeted memory search no hit | `leanCompiled`; focused/root/Tests and full check; algorithm-delta, radius-normalization, composition-identity, and terminal canaries; independent-review findings resolved; baseline-only axiom audit | explicit finite-window logarithmic square-root expected rate closed; the downstream fixed-model asymptotic consumer now compiles; minimax, anytime, contextual/dynamic, uniform-over-parameter, and broader linear-bandit claims remain separate |
| `OFUL-GENERATED-TRAJECTORY-ASYMPTOTIC-EXPECTED-PSEUDOREGRET-RATE` | fixed-model canonical expected pseudo-regret at algorithm parameter `1/(T+1)^2` is `O(sqrt(T+1)*log(T+1))` at `Filter.atTop` | explicit expected-regret bound; determinant/confidence log budgets; Mathlib asymptotics/log/sqrt APIs | prove determinant and confidence budgets are `O(log(T+1))`; transport square roots/products; absorb `sqrt(log)` into `log` eventually; apply the pointwise canonical expected-regret bound via `isBigO_iff` | `0<K`; finite decidable nonempty Feature; fixed `lambda`, `R`, `S`, `L2`, features, environment, and best arm; `0<lambda`, `0<R`, `0<=S`, `0<=L2`; arm ceiling; `L2<=lambda`; certified optimal arm; canonical linear-sub-Gaussian law; no caller delta, pathwise width, countability, independence, stationarity, stopping time, anytime, supplied integrability, or uniform-over-parameter claim | explicit/expected local cards; `MLIB-ASYMPTOTICS`; `MLIB-REAL-LOG-SQRT`; `MLIB-EXP-LOG-INEQUALITIES`; `MLIB-CONVEX-LINALG`; `MLIB-MEASURE-INTEGRAL`; OFUL paper/textbook/scenario; weapon inspiration-only; old aggregate asymptotics import replaced by the three compiled Mathlib modules and migrated in retrieval snapshots | `leanCompiled`; focused/root/Tests/full check; all public signature checks; explicit-bound and terminal-composition proof canaries; baseline-only axiom audit; independent-review P2/P3 findings resolved | fixed-model expected-regret asymptotic corollary closed; minimax, anytime, high-probability all-horizon, contextual/dynamic, uniform-over-parameter, and unrestricted linear-bandit claims remain separate |
| `OFUL-GENERATED-TRAJECTORY-EXPECTED-AVERAGE-PSEUDOREGRET-CONSISTENCY` | exact complete canonical expected pseudo-regret divided by `T+1` tends to zero for the fixed-model horizon-indexed family | canonical asymptotic expected-regret theorem; `isLittleO_log_rpow_atTop`; little-o multiplication/transitivity/division APIs | prove `log(T+1)=o(sqrt(T+1))`; multiply by the reflexive sqrt scale; rewrite `sqrt(T+1)^2=T+1`; transport canonical Big-O to little-o; apply `tendsto_div_nhds_zero` | same fixed-model contracts as the asymptotic theorem; algorithm parameter `1/(T+1)^2`; no caller delta, pathwise width, countability, independence, stationarity, stopping time, anytime, supplied integrability, uniform-over-parameter, pathwise-convergence, or probability-convergence claim | asymptotic/explicit local cards; `MLIB-ASYMPTOTICS`; `MLIB-REAL-LOG-SQRT`; OFUL paper/textbook/scenario; weapon inspiration-only; targeted local retrieval found no matching card | `leanCompiled`; focused/root/Tests/full checks; all five public signature checks; analytic little-o and terminal canonical proof canaries; independent review no P0-P3; baseline-only axiom audit | horizon-indexed expected-average convergence closed; do not call it almost-sure Hannan consistency, an anytime theorem, or consistency of one horizon-independent policy |
