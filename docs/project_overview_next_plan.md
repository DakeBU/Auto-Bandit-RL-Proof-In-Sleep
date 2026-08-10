# ABRL Project Overview And Next Plan

## Paper-Guided Priority Order

The paper's audited focal cases remain the source-shaped ETC expected-regret
route and uncapped finite-horizon stopped-value RL route; both should be
maintained without treating them as complete algorithm families. New proof
work now follows the paper's dependency order:

1. consolidate reusable probability, filtration, stopping-time, and
   concentration contracts;
2. close canonical stochastic/adversarial textbook statements through thin
   consumers of that shared layer;
3. build the self-normalized matrix-probability layer needed by OFUL;
4. assemble reusable RL Bellman, occupancy, confidence, and policy-output
   interfaces before attempting a complete UCB-VI-style endpoint.

Within item 2, finite-arm sampled UCB already has a compiled logarithmic
pseudo-regret route and average-regret convergence. EXP3 already has compiled
expected-regret and several fixed-horizon Bernstein-style confidence routes.
The concrete geometric schedule, deterministic unit-variance producer,
same-process predictable-regret event, and pure realized-deviation event now
feed a compiled all-positive-prefix realized selected-loss regret theorem.
The next adversarial target is a finite-supported-comparator union and best-arm
external-regret surface on that same fixed process. This follows the paper's
EXP3 order: importance-weighted moments, potential/stability/comparator
analysis, realized-loss composition, then comparator aggregation. Ideal
Freedman/EXP3.P and a horizon-free tuned algorithm remain open.

## Current Lean Frontier: Generated EXP3 Realized-Regret All-Time Tail

`EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL` is accepted in
`BanditRLProof.Exp3RealizedRegretAllTime`. It fixes one generated process and
one supported comparator, then controls realized selected-loss regret over
every positive prefix `n+1`.

The scheduled budget gives total confidence `delta/2` to the accepted
predictable-regret all-time family and `delta/2` to the accepted pure
realized-deviation family. A new finite-sum theorem proves exactly that
realized selected-loss regret equals exploration-mixed predictable regret plus
cumulative realized deviation. The combined failure event is therefore a
subset of the union of the two parent events; `measure_mono`,
`measure_union_le`, and `ENNReal.ofReal_add` close the outer-measure bound.

Contracts are a probability prior, Standard Borel nonempty environment and
action spaces, measurable action singletons, decidable nonempty arms, fixed
`eta>0`, `0<gamma<1`, one `PredictableLossVector`, one comparator in the arms,
and `delta>0`. Event measurability, `delta<=1`, independence, stationarity,
countable actions, supplied integrability, or a new law transport is not
required. Retrieval is local-first through the two accepted all-time parent
cards and the fixed-horizon realized-regret composition precedent; source cards
are placement only and proof weapons are inspiration only.

Focused/root/`Tests.Basic`, five semantic canaries, SafeVerify
`34d6b6dd...5702`, and six baseline-only axiom reports pass. Independent
review found no P0/P1/P2/P3. Lifecycle records are accepted, verified memory
is `mem-2a0ffec376992850`, frontier shadow has zero mismatches, and the full
harness passes. This is fixed-parameter regret against one comparator,
not best-arm external regret, a tuned sublinear all-time rate, horizon
retuning, Ville/Doob, mixture, optional stopping, self-normalization, general
Freedman, horizon-free tuned EXP3, or ideal EXP3.P.

## Current Lean Frontier: Generated EXP3 Predictable-Regret All-Time Tail

`EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL` is accepted in
`BanditRLProof.Exp3PredictableRegretAllTime`. It fixes one generated process and
one supported comparator, then controls the outer measure of predictable-
regret budget crossings over every positive prefix `n+1`.

The scheduled budget calls the existing fixed-horizon pathwise Hedge/
exploration/comparator budget at confidence
`geometricConfidenceShare delta n / 2`. This preserves the parent's internal
equal split between its pure-cross and comparator-estimator failures, while
the outer event receives share `delta/2/2^n`. The proof specializes that parent
at every `n+1`, applies `MeasureTheory.measure_iUnion_le` and
`ENNReal.tsum_le_tsum`, then rewrites the exact geometric tsum.

Contracts are a probability prior, Standard Borel nonempty environment and
action spaces, measurable action singletons, decidable nonempty arms, fixed
`eta>0`, `0<gamma<1`, one `PredictableLossVector`, one comparator in the arms,
and `delta>0`. Event measurability, `delta<=1`, independence, stationarity,
countable actions, supplied integrability, or a new law transport is not
required. Retrieval is local-first through the fixed predictable-regret and
geometric-schedule cards, with Mathlib measure/finite-sum/order APIs; source
cards are placement only and potential/tail weapons are inspiration only.

Focused/root/`Tests.Basic`, three semantic canaries, SafeVerify
`dc280a8f...b13a5`, and four baseline-only axiom reports pass. Independent
review found no P0/P1/P2 and its retrieval-timing P3 is closed. Lifecycle
records are accepted, verified memory is `mem-b8cfa9865d91f12a`, frontier
shadow has zero mismatches, and the full harness passes. This parent is
consumed by the compiled realized-regret all-time composition above, but by
itself is fixed-parameter predictable pseudo-regret confidence, not realized regret,
a tuned sublinear all-time rate, horizon retuning, Ville/Doob, mixture,
optional stopping, self-normalization, general Freedman, horizon-free tuned
EXP3, or ideal EXP3.P.

## Current Lean Frontier: Pure Generated EXP3 Geometric All-Time Deviation

`EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL` is accepted in
`BanditRLProof.Exp3RealizedDeviationAllTime`. On one fixed generated EXP3
trajectory law it bounds the outer measure of the union, over every positive prefix `n+1`, where
realized selected loss minus predictable selected loss crosses the geometric-
share quadratic radius with deterministic predictable-variance budget `n+1`.

The support leaf in `Exp3RealizedPredictableVariance` proves that a finite
probability law on `[0,1]` losses has centered second moment at most one,
instantiates that bound for the exact generated action law at every time, and
sums it over `Finset.range horizon`. The target then defines the linear budget,
radius, and named pure crossing event; proves exact membership; identifies the
previous joint deviation/variance event at this budget with the pure event;
and rewrites the accepted geometric all-time measure theorem.

Contracts are a probability prior, Standard Borel nonempty environment and
action spaces, measurable action singletons, decidable nonempty arms, one
fixed `eta`, `0 < gamma <= 1`, one `PredictableLossVector`, and `delta > 0`.
No event measurability, independence, stationarity, `delta <= 1`, caller-
supplied budget, or variance-good premise is required. Retrieval is local-
first through the selected-loss variance, geometric all-time, countable
quadratic, finite-sum/order, variance, and MGF cards; textbook and EXP3 source
cards give placement only, and the tail weapon is inspiration only.

Focused/root/`Tests.Basic` builds and six external canaries pass. SafeVerify
fixes statement hash `5479f334...870`; the ten new declarations have only the
baseline axioms. Independent review found no P0/P1 and its direct-canary,
API-contract, and outer-measure wording findings are closed. Lifecycle and
the full harness pass; verified memory is `mem-7ceab55257453017`, and active
frontier shadow has zero mismatches. Its missing same-process predictable-
regret side now compiles in the frontier above; the next target combines both
events. This is pure selected-loss deviation confidence, not full regret,
horizon retuning, a small-loss or self-
normalized result, Ville/Doob, a mixture boundary, optional stopping, general
Freedman, a horizon-free tuned EXP3 algorithm, or ideal EXP3.P.

## Current Lean Frontier: Generated EXP3 Geometric All-Time Tail

`EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL` is accepted in
`BanditRLProof.Exp3RealizedPredictableVarianceAllTime`. On one fixed generated
trajectory law it bounds the union, over every positive prefix `n+1`, of the
event that selected-loss realized deviation crosses its optimized radius while
cumulative predictable variance stays below `varianceBudget n`.

The supporting `ConcentrationConfidenceSchedule` leaf defines
`delta / 2 / 2^n`, proves positivity, and transports `hasSum_geometric_two'`
through `HasSum.toNNReal` and `ENNReal.hasSum_coe` to an exact
`ENNReal.ofReal delta` total. The EXP3 consumer specializes the generated
fixed-tilt tail at each `n+1`, uses the accepted countable scheduled quadratic
parent with constant scale/cap one, and rewrites that exact budget.

Contracts are a probability prior, Standard Borel nonempty environment and
action spaces, measurable action singletons, decidable actions, nonempty
arms, one fixed `eta`, `0 < gamma <= 1`, one `PredictableLossVector`, a
pointwise-positive variance-budget schedule, and `delta > 0`. No event
measurability, independence, stationarity, `delta <= 1`, or proof that the
variance-budget events hold is assumed.

Retrieval is owned by
`LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE` and the EXP3 consumer,
with the countable/quadratic/fixed-tilt parents and the OFUL all-time scalar
ridge confidence leaf as an exact-budget transport precedent. Root, focused,
and `Tests.Basic` builds; exact-sum, membership, and terminal canaries;
SafeVerify hash `be643bca...73b2`; baseline axiom audit; and independent review
pass. Verified memory is `mem-1d262929553ef1ca` and the active frontier has
zero shadow drift. The deterministic unit-variance producer and pure-event
consumer now compile in the frontier above. This joint theorem itself is not
full regret, Ville/Doob, a mixture boundary, optional stopping,
self-normalization, general Freedman, a horizon-free tuned EXP3 algorithm, or
ideal EXP3.P.

## Current Lean Frontier: Countable Scheduled Quadratic Tail

`CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL` is accepted in
`BanditRLProof.ConcentrationQuadraticScheduled`. It defines the time-indexed
optimized radius, bounds the countable union of scheduled joint
deviation/variance events by `sum' n, ENNReal.ofReal (deltaAt n)`, and exposes
a direct outer-budget corollary.

The route specializes the compiled one-event quadratic fixed-MGF delta theorem
at every index, applies `MeasureTheory.measure_iUnion_le`, compares terms with
`ENNReal.tsum_le_tsum`, and composes with the supplied budget. Its contracts
are a measurable ambient space, pointwise-positive scale/budget/cap/share
schedules, and the displayed fixed-tail family. It needs no event
measurability, probability measure, independence, filtration, boundedness,
stationarity, or `deltaAt n <= 1`.

Retrieval is local-first through the quadratic-delta and finite-maximal leaves,
with Mathlib measure/MGF/log-sqrt/exp-order cards; the EXP3 paper card is only
downstream placement and the tail weapon is inspiration only. Root import,
focused build, external full-statement canary, declaration/index, axiom,
lifecycle, and full harness gates pass. Its explicit geometric schedule and
fixed-process EXP3 consumer now compile in the frontier above. This leaf proves
no Ville/Doob or mixture boundary, optional stopping,
self-normalization, general Freedman theorem, horizon-free anytime result, or
ideal EXP3.P theorem.

## Current Lean Frontier: Scalar Joint-Error Stopped-Return Confidence

`RL-STOPPED-SAMPLED-POLICY-RETURN-JOINT-ERROR-DETERMINISTIC-TAIL-HIGH-PROBABILITY-OPTIMALITY`
is accepted through seven declarations, the project root, and an external
typed five-field canary. It exposes one measurable scalar maximum of the six
literal capped/uncapped sampled-return, actual `successorPolicyAt`
trajectory-law return, and same-prefix-gap errors. For every positive real
`epsilon, delta`, one existential natural cutoff works at every later index:
the weak scalar bad event is below the `ENNReal.ofReal delta` budget, the
strict scalar good event has real probability above `1-delta`, and the scalar
strict bound is exactly the conjunction of all six literal strict bounds.

The route consumes the accepted deterministic-tail named-event parent and
uses `Measurable.dist`, `Measurable.max`, `max_lt_iff`, `le_max_iff`, and exact
event equalities. SafeVerify fixes `f4fc8680...355a`; all seven axiom reports
are baseline-only. Retrieval is `mem-cd67b8453f91af1b`, verified memory is
`mem-6f587b6fba5f9bfd`, and cards are placement only. Independent review's
P2/P3 filename and ledger findings are closed; lifecycle, zero-drift frontier,
and full harness gates pass.

The next leaf must remain below broad policy/regret theorems. This result has
no computable cutoff, rate, `delta <= 1`, independence, optional stopping,
expectation/random-index interchange, model uniformity, raw episodes,
recommended-policy substitution, minimax/reachability, or complete UCB-VI.

## Current Lean Frontier: Deterministic-Tail Stopped-Return Confidence

`RL-STOPPED-SAMPLED-POLICY-RETURN-DETERMINISTIC-TAIL-HIGH-PROBABILITY-OPTIMALITY`
is accepted through seven declarations, the project root, and an external
typed canary. For every positive real accuracy and confidence tolerance, it
extracts one existential natural cutoff such that every later schedule index
has a measurable six-error bad event below the `ENNReal.ofReal delta` budget,
a named complement with real probability greater than `1 - delta`, and an
exact iff with all six literal stopped-return errors below `epsilon`.

The route consumes the accepted simultaneous-confidence parent, uses
`eventually_atTop.1` for the cutoff, and converts strict bad-event mass through
`ENNReal.toReal_lt_toReal` and `probReal_compl_eq_one_sub`. The named good event
is exactly the existing bad event's complement. SafeVerify fixes
`09d8972f...a28f`; placeholders are empty and all seven declarations have
baseline-only axiom reports. Retrieval is `mem-89d817ed84c75c44`; cards are
placement only. Independent review's P2/P3 ledger findings are closed, and
lifecycle/full harness gates pass. Verified memory is
`mem-5265bad6103b31c3`.

The next leaf must remain below broad policy or regret theorems. This theorem
provides no computable cutoff or quantitative rate, and uses no independence,
optional stopping, expectation/random-index interchange, model uniformity,
raw episodes, recommended-policy substitution, minimax/reachability, or
complete UCB-VI.

## Current Lean Frontier: Simultaneous Stopped-Return High Probability

`RL-STOPPED-SAMPLED-POLICY-RETURN-SIMULTANEOUS-HIGH-PROBABILITY-OPTIMALITY`
is accepted through eleven declarations, the project root, and an external
typed canary. It forms one measurable event at a common schedule index from
the six literal distance violations for capped/uncapped sampled return,
actual `successorPolicyAt` trajectory-law expected return, and their
same-prefix gaps. Event exclusion gives six strict epsilon bounds, the event
probability tends to zero, and every positive real confidence tolerance is
eventually met.

The route reuses six accepted `TendstoInMeasure` endpoints and applies
`tendstoInMeasure_iff_dist`, a six-term limit, repeated `measure_union_le`, and
`tendsto_order`. It needs no independence. Four stopped-coordinate
measurability wrappers are local; two policy-return measurability facts are
inherited. SafeVerify fixes `abeed7f0...2c443`; placeholders are empty and
seven representative axiom reports are baseline-only. Retrieval is
`mem-8642ef20df67310d`; cards are placement only. Independent review's P2/P3
ledger findings are closed, and lifecycle/full harness gates pass.

The next leaf must remain below broad policy or regret theorems. A suitable
consumer may add a quantitative cutoff only after a separately compiled rate
for all six coordinate-event probabilities; this leaf itself proves no rate,
optional stopping, expectation/random-index interchange, model uniformity,
raw episodes, recommended-policy substitution, minimax/reachability, or
complete UCB-VI.

## Current Lean Frontier: Stopped Return In-Measure And A.E. Optimality

`RL-STOPPED-SAMPLED-POLICY-RETURN-IN-MEASURE-AE-OPTIMALITY` is accepted
through fifteen declarations, the project root, and external canaries. At the
exact capped inverse-square-root first-passage and genuine uncapped
`hittingAfter` prefixes, it proves that literal sampled return and the
trajectory-law expected return of the actual `successorPolicyAt` policies
converge in measure and almost everywhere to the optimal initial return. Their
same-prefix gap converges to zero in both modes. The terminal packages six
`TendstoInMeasure` and six a.e. `Tendsto` contracts.

The in-measure half uses the accepted true `L1` route through Mathlib
`tendstoInMeasure_of_tendsto_eLpNorm`. The almost-sure half is separate: capped
realized convergence is transported through a.s. eventual equality, then
sampled and policy returns use exact complement identities and the gap uses
the exact deviation rearrangement. No a.e. conclusion is inferred from
convergence in measure.

SafeVerify fixes `22635f14...ad041`; the source is placeholder-free and seven
representative declarations have baseline-only axioms. Retrieval is
`mem-1ae15dfd64b32dc6`; source cards are placement only and no theorem card or
weapon is consumed. Independent review found no Lean issue and its sole P3
stale-ledger finding is closed. The full harness gate passes. This remains a
fixed-model qualitative route: no expectation/random-index interchange,
optional stopping, rate, model uniformity, raw episodes, recommended-policy
substitution, minimax/reachability, or complete UCB-VI follows.

## Current Lean Frontier: Stopped Sampled/Policy Return L1 Optimality

`RL-STOPPED-SAMPLED-POLICY-RETURN-L1-OPTIMALITY` is accepted through twenty
declarations, the project root, and external canaries. It upgrades the previous
expectation-level return theorem to actual `L1` performance at both the exact
capped inverse-square-root first-passage prefix and the genuine uncapped
`hittingAfter` prefix.

Three named processes expose sampled return minus optimal value, the literal
trajectory-law expected return of the actual `successorPolicyAt` policies
minus optimal value, and sampled return minus that policy return. Exact
pointwise identities identify them with negative realized behavior regret,
negative behavior expected regret, and return deviation. The already compiled
capped/uncapped parent routes then yield six coordinatewise `MemLp 1`
contracts and six `eLpNorm · 1 -> 0` limits. Thus the word `L1` here means
vanishing expected absolute error, not the weaker absolute difference of
expectations.

SafeVerify fixes statement hash `604b612b...a9562a`; the focused source is
placeholder-free and ten representative declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Retrieval is
`mem-de0a77c377532117`; `SCN-RL-MDP` and the UCB-VI paper card are route
placement only, with no theorem-card or weapon consumed. Independent review's
only P2 regression-canary finding is closed by an explicit twelve-contract
destructure/reassembly canary, with no open P0-P3. Lifecycle and the full
harness gate pass. The theorem remains fixed-model qualitative `L1`
consistency: no expectation/random-index interchange, optional stopping,
pathwise/rate result, model uniformity, raw episodes, recommended-policy
substitution, minimax/reachability, or complete UCB-VI follows.

## Current Lean Frontier: Stopped Sampled/Policy Return Consistency

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-SAMPLED-RETURN-SUCCESSOR-POLICY-EXPECTED-RETURN-CONSISTENCY`
is compiled through 29 declarations, the project root, and external canaries.
It adds the missing literal benchmark: each actual exploratory
`successorPolicyAt trajectory t` is evaluated by integrating cumulative reward
under its own generated trajectory law. The natural-prefix average uses the
optimal initial return at zero and is proved, rather than defined, to equal
optimal return minus average behavior expected regret.

Combining this bridge with the accepted sampled-return complement and exact
`realized = behaviorExpected - returnDeviation` decomposition gives, at one
identical stopped prefix,
`sampledReturn - policyExpectedReturn = returnDeviation`. The theorem holds
pathwise and after Bochner integration for both the capped first-passage and
genuine uncapped `hittingAfter` prefixes. Both signed and absolute expected
gaps tend to zero, and the stopped policy-return expectations themselves tend
to the optimal initial expected return. The terminal now exposes the
policy/behavior complements and their integral forms in addition to these
same-prefix identities and six limits.

SafeVerify fixes statement hash `e35de2a4...7353`; the source is
placeholder-free and ten representative declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Retrieval is
`mem-06aaf9949ace539d`. Independent review found no P0/P1; its P2/P3
API-hardening findings were closed with typed positive-prefix, `untopA`, and
terminal-projection canaries plus the expanded terminal bundle. This remains
fixed-model qualitative consistency: no
expectation/random-index interchange, optional stopping, pathwise return
convergence, quantitative rate, raw-episode result, recommended-policy
substitution, minimax/reachability, or complete UCB-VI is proved.

## Current Lean Frontier: Expected Stopped Sampled-Return Optimality

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-AVERAGE-SAMPLED-RETURN-EXPECTED-OPTIMALITY`
is compiled through 22 declarations, the project root, and external canaries.
It defines the literal observed successor-batch sample mean and its natural
finite-prefix average. The empty prefix is assigned the optimal initial
expected return; finite-sum algebra then proves at every prefix
`sampledReturn = optimalInitialExpectedReturn - realizedRegret`.
The generic batch-mean API documents Lean's totalized zero-denominator value;
the self-consistent scheduled route used by the terminal has positive batch
sizes.

The identity supplies natural-filtration strong adaptation, generic stopped
measurability, and pointwise complement identities for both the practical
capped first-passage prefix and genuine uncapped `hittingAfter`. Existing
`MemLp 1` parents give integrability; `integral_sub` and the probability
integral of a constant give exact expectation identities. The accepted
stopped realized-regret expectation limits then imply that both expected
stopped sampled returns converge to the optimal initial expected return.

SafeVerify fixes statement hash `cf81f234...e5f5`; the source is
placeholder-free and representative declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Retrieval is
`mem-31b7a2396410fc17`. Independent review's two P3 hardening findings were
closed by the totalization contract and direct zero-prefix plus capped/uncapped
measurability canaries; no P0-P3 remains, lifecycle shadow passes, and the full
gate passes. This remains fixed-model expected-return optimality:
it does not prove expectation/random-index interchange, optional stopping,
sample-path return convergence, a quantitative rate, model-uniform control,
raw episodes, behavior=recommended equality, minimax/reachability, or
complete UCB-VI.

## Current Lean Frontier: Expected Realized/Policy-Value Consistency Square

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-REALIZED-POLICY-VALUE-EXPECTED-CONSISTENCY`
is accepted through seven declarations, a root import, and external
declaration/terminal canaries. For both the practical capped first-passage
prefix and genuine uncapped `hittingAfter`, the exact identity
`E realized - E policyValue = - E returnDeviation` holds at every schedule
index, and its signed and absolute left-hand sides tend to zero.

The proof normalizes the accepted expected decompositions, applies
`Tendsto.neg` to the compiled return-deviation expectation limits, and maps
the signed limits through `continuous_abs`. The terminal combines these two
vertical edges with the accepted capped-to-uncapped behavior and realized
expectation gaps. It also states exact equality of the two paths around the
square at every index, rather than leaving commutativity implicit.

SafeVerify fixes statement hash `d07f9ed4...c7b9`; the source is
placeholder-free and all seven declarations have only `propext`,
`Classical.choice`, and `Quot.sound`. Retrieval is
`mem-4fafd4fc9904f47d`; independent local review found no open P0-P3. A next
narrow consumer may use this square to replace expected realized regret by
the successor-policy value-gap asymptotically, but must retain the exact
fixed-model/source semantics and must not infer random-index expectation
interchange, optional stopping, finite-index equality, a quantitative rate,
model-uniform control, raw episodes, behavior=recommended equality,
minimax/reachability, or complete UCB-VI.

## Current Lean Frontier: Componentwise Expected Truncation Replacement

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-BEHAVIOR-RETURN-EXPECTED-TRUNCATION`
is accepted through seven declarations, a root import, and external
expected-gap/decomposition/terminal canaries. On the exact generated
trajectory law, both behavior-value and return-deviation signed expectation
gaps between genuine uncapped `hittingAfter` and its practical capped
double-linear approximation tend to zero; the absolute values of those
signed gaps also tend to zero.

The proof consumes the accepted componentwise L1 integral limits. It first
derives coordinate integrability from `MemLp 1`, uses `integral_sub` to expose
the actual expectation differences, and applies `continuous_abs`. Separately,
the exact pathwise identity
`realized = behavior expected - return deviation` is retained at each prefix
and integrated for both capped and uncapped stops. The terminal packages all
six integrability facts, both exact expected decompositions, four gap limits,
and the four component signed-expectation limits.

SafeVerify fixes statement hash `d46e2fb3...e0e53`; the source is
placeholder-free and all seven public declarations have only `propext`,
`Classical.choice`, and `Quot.sound`. Retrieval is
`mem-bf148b8e7faff0cd`; independent local review found no P0-P3. A next narrow
leaf may consume these expectation decompositions in a policy-value
comparison, but it must not exchange expectation with a random stopping
index or infer optional stopping, finite-index equality, a truncation rate,
model-uniform control, raw episodes, behavior=recommended equality,
minimax/reachability, or complete UCB-VI.

## Current Lean Frontier: Componentwise Policy-Value L1 Truncation

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-CAPPED-UNBOUNDED-STOPPED-BEHAVIOR-RETURN-L1-TRUNCATION`
is accepted through eighteen declarations, a root import, and external
declaration/terminal canaries. The practical capped double-linear
first-passage prefix now carries the same successor-policy value-gap and
return-deviation semantics as genuine uncapped `hittingAfter`: capped
behavior and return coordinates are `MemLp 1` with vanishing `eLpNorm 1` and
signed integrals, and both componentwise uncapped-minus-capped errors vanish
in those same L1/integral surfaces.

The proof first derives capped `untopA` divergence from almost-sure eventual
equality with the common fourth-power base. Random-prefix composition and the
uniform `2H` envelope close capped behavior L1. The exact stopped identity
`realized = behavior expected - return deviation` closes capped return L1.
For truncation replacement, behavior uses the L1 triangle, while return uses
the compiled algebra `Delta return = Delta behavior - Delta realized` and
therefore consumes the accepted realized-regret truncation theorem rather
than bypassing it.

SafeVerify fixes statement hash `20132e52...62acb`; the placeholder scan is
empty and the axiom set is exactly the baseline of both accepted parents.
Local-first retrieval is `mem-1011ebc0a0909b71`; scenario and UCB-VI paper
cards remain placement evidence only. The next narrow route may consume this
practical capped policy-value surface in an expected policy-value comparison,
but must not infer optional stopping, expectation/random-index interchange,
finite-index equality, a quantitative rate, model-uniform control, raw
episodes, behavior=recommended equality, minimax/reachability, or complete
UCB-VI.

## Current Lean Frontier: Uncapped Policy-Value And Return-Deviation L1

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPED-BEHAVIOR-EXPECTED-REGRET-AND-RETURN-DEVIATION-L1-CONSISTENCY`
is accepted through twenty-three declarations, a root import, and external
arbitrary-prefix decomposition and exact-terminal canaries. At the genuine
uncapped `hittingAfter` prefix, the pathwise successor-policy value-gap
average is measurable, nonnegative, bounded by `2H`, `MemLp 1`, and converges
a.e., in expected absolute value, in `eLpNorm 1`, and in signed expectation.

The exact same-prefix identity is
`realized = behavior expected - return deviation`. Combining it with the
accepted realized-regret L1 route gives return-deviation `MemLp 1`,
`eLpNorm 1 -> 0`, and signed-integral convergence. The proof uses
`measurable_apply_randomNat`, `ae_tendsto_apply_randomPrefix`,
`tendsto_integral_filter_of_norm_le_const`,
`MemLp.eLpNorm_eq_integral_rpow_norm`, `memLp_congr_ae`, and
`eLpNorm_sub_le`; it never moves an integral through a random index.

SafeVerify fixes statement hash `0af3bbb9...79da77`; five key declarations
have only baseline axioms. Independent read-only review found no P0-P3, and
the full repository gate passes with 36 CLI tests and one expected skip.
This is a fixed-model policy-value semantic bridge, not optional stopping,
finite-index equality, a quantitative rate, model-uniform control, raw
episodes, behavior=recommended equality, minimax/reachability, or complete
UCB-VI.

## Current Lean Frontier: Expected-Regret Truncation Replacement

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-UNBOUNDED-HITTINGAFTER-EXPECTED-REGRET-TRUNCATION-REPLACEMENT`
now compiles through six declarations, a root import, and external generic,
exact-gap, and terminal canaries. On one exact generated trajectory law, each
capped and uncapped stopped average realized behavior-regret coordinate is
integrable, and `integral_sub` identifies the integral of the pointwise
uncapped-minus-capped error with the signed difference of expectations.

The new arbitrary-measure wrapper uses `memLp_one_iff_integrable`,
`integrable_zero`, `eLpNorm_congr_ae`, and `tendsto_integral_of_L1'` to carry
exponent-one norm convergence through the Bochner integral. Applying it to
the accepted L1 truncation error proves that both the integral of the error
and the signed expected gap tend to zero; `continuous_abs` gives the absolute
expected-gap limit. A second application gives the capped signed-expectation
limit, while the accepted exact uncapped expectation theorem supplies the
last terminal conjunct. SafeVerify preserves statement hash
`ef44a0df...b9741`, and the declaration audit uses only baseline axioms.
Independent review found no P0-P2; both P3 metadata findings were closed by
recording the actual arbitrary-measure API and synchronizing lifecycle state.
Lifecycle shadow and the full repository gate pass, including 36 CLI tests
with one expected skip.

This is fixed-model qualitative expected-regret replacement. It does not
prove finite-index equality, equality on or between delayed events, a
quantitative truncation rate, optional stopping, a policy-value identity,
model-uniform control, raw-episode regret, behavior=recommended equality,
minimax/reachability, or complete UCB-VI.

## Current Lean Frontier: Capped/Uncapped HittingAfter L1 Truncation Equivalence

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-UNBOUNDED-HITTINGAFTER-L1-TRUNCATION-EQUIVALENCE`
now compiles through ten declarations, a root import, and an external terminal
canary. Outside the existing capped delayed set, the capped first-passage stop
and genuine uncapped `hittingAfter` stop both equal the common fourth-power
base, so their stopped average realized behavior-regret coordinates agree.
Summable avoidance of that delayed set gives almost-everywhere eventual exact
equality.

On the common generated trajectory law, both process coordinates retain their
compiled `MemLp 1` and exponent-one norm limits. `MemLp.sub` and
`eLpNorm_sub_le` therefore make the uncapped-minus-capped difference converge
to zero in `eLpNorm 1`; the module packages the same difference as a named
`Lp Real 1` sequence converging to zero and derives `TendstoInMeasure` for the
raw representatives. The focused module, root, and `Tests.Basic` targets pass.
SafeVerify preserves statement hash `b68c4bc4...76a80`; the placeholder and
baseline-axiom audits pass. Independent review found no P0-P2, and its two P3
metadata findings were closed by accepting the lifecycle rows and narrowing
the proof-parent description/import to the actual capped L1 and uncapped Lp
parents. Lifecycle shadow and the full repository gate pass.

This closes a comparison interface, not a delayed-event identity: equality is
proved only off the capped delayed set, and no uncapped delayed event is
identified with it. The result is fixed-model qualitative L1 truncation
equivalence, not a quantitative rate, optional stopping, raw-episode regret,
behavior=recommended equality, minimax/reachability, or complete UCB-VI. The
accepted expected-regret replacement child above is now the compiled consumer
of this named Lp difference; any policy-value argument remains separate.

## Current Lean Frontier: Delayed-Event Expected Contribution At Exact HittingAfter

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-DELAYED-EVENT-EXPECTED-CONTRIBUTION`
now compiles through three declarations, a root import, and external generic
and exact terminal canaries. It consumes the existing capped first-passage
delayed event, whose probability tends to zero, but integrates the genuine
uncapped `hittingAfter` stopped average realized behavior-regret process.
Both the restricted expected absolute contribution and the absolute signed
restricted expectation tend to zero.

The general bridge uses the accepted uniform-absolute-continuity epsilon-delta
bound. ENNReal event-mass convergence eventually enters the positive
`ofReal delta` neighborhood; nonnegativity and the half-epsilon bound give the
restricted L1 limit. `abs_integral_le_integral_abs` then gives the signed
limit. The exact terminal reuses the compiled delayed-set measurability and
`delayedProbability_tendsto_zero` producer without adding an event-tail
assumption. SafeVerify passes at `304b5afc...499c0`; placeholders are empty and
all three declarations use only baseline axioms. Independent review found no
P0-P3; its signed generic application-canary request is closed. Lifecycle
shadow and the full repository gate pass.

This is qualitative fixed-model rare-event contribution control. It does not
give a computable convergence rate, optional stopping, model-uniform control,
raw-episode regret, behavior=recommended equality, minimax/reachability, or
complete UCB-VI. The capped/uncapped child above now supplies the complementary
pointwise and L1 comparison interface; policy-value consumers remain separate.

## Accepted Parent: Exact Uncapped HittingAfter Uniform Absolute Continuity

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-UNIFORM-ABSOLUTE-CONTINUITY`
now compiles through a two-declaration module, root import, and external
generic/terminal canaries. For every positive epsilon, one positive delta
works uniformly over every schedule index and measurable trajectory event:
if the event probability is at most `ENNReal.ofReal delta`, then both the
restricted integral of absolute stopped regret and the absolute signed
restricted integral are at most epsilon.

The proof consumes the accepted exact `UniformIntegrable` parent. Mathlib's
`UnifIntegrable` definition gives the indicator `eLpNorm` bound;
`MemLp.eLpNorm_eq_integral_rpow_norm` and `integral_indicator` identify the
exponent-one norm with the restricted absolute integral; and
`abs_integral_le_integral_abs` gives the signed bound. SafeVerify passes at
`db0cd463...71c67`; placeholder and baseline-axiom audits are clean. The
independent review's one P3 missing uncapped-stop fence guard was repaired,
leaving no P0-P3, and the lifecycle/full repository gates pass.

This is qualitative fixed-model epsilon-delta control. It does not provide a
computable delta, a stopping-time tail/moment rate, optional stopping,
uniformity over models, raw-episode regret, behavior=recommended equality,
minimax/reachability, or complete UCB-VI. The next route should consume this
small-event interface in a concrete truncation or policy decomposition with
an independently proved event-probability bound.

## Accepted Parent: Exact Uncapped HittingAfter Uniform Integrability

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-UNIFORM-INTEGRABILITY-EXPECTED-CONSISTENCY`
is accepted through a four-declaration module, root import, and external
generic/terminal canaries. The exact genuine uncapped stopped average realized
behavior-regret sequence is `UniformIntegrable` at exponent one, and its
signed Bochner expectations tend to zero.

The route consumes the accepted Lp parent. Mathlib
`unifIntegrable_of_tendsto_Lp` supplies measure-theoretic UI; boundedness of
the convergent named `Lp Real 1` range supplies the probability definition's
uniform norm field; `tendsto_integral_of_L1'` gives the signed limit.
SafeVerify passes at `2c010bef...fcd24`, baseline-axiom and placeholder audits
are clean, and independent review found no P0-P3.

This is not an optional-stopping identity and does not provide a stopping-time
moment/rate theorem, uniform-in-model/index control, raw-episode regret,
behavior=recommended equality, minimax/reachability, or complete UCB-VI. A
accepted child above consumes its UI interface on arbitrary small measurable
events without broadening those boundaries.

## Accepted Parent: Exact Uncapped HittingAfter Lp

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-LP-CONSISTENCY`
is accepted through its root import and external canaries. It transports the
accepted expected-absolute exact stopped-regret limit into `MemLp 1`, an exact
`eLpNorm 1 = ENNReal.ofReal E|.|` identity and limit, a named `Lp Real 1`
process converging to zero, and a joint terminal retaining in-measure and a.e.
convergence. The route uses existing Mathlib Lp APIs and adds no optional-
stopping premise. Its accepted child above now adds sequence uniform
integrability and signed expectation convergence. SafeVerify passes at
`30ec3b42...aaca8a8`; independent review, lifecycle shadow, and the full
repository gate pass.

## Accepted Parent: Exact Uncapped HittingAfter L1

`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-L1-CONSISTENCY`
is accepted through the root, external canaries, SafeVerify, independent
review, lifecycle frontier, and full repository gate. Its terminal theorem is
the canonical expected-absolute limit for the exact stopped average realized
behavior regret. The missing negative side is discharged by first-hit
predecessor positivity, exact one-step averaging, uniform successor-coordinate
L2 control, and square-summable reciprocal stopping-fiber weights. It is now
the accepted expected-absolute parent of the Lp theorem route above.

## Current Harness Gate: Lifecycle And Proof Frontier

`HARNESS-LIFECYCLE-PROOF-FRONTIER-HARDENING` is accepted without
changing Lean statements. `runs/active_frontier.json` now owns the root
objective, one current leaf, dependency DAG, statement hash, source status,
bounded-memory policy, shadow evidence, and last accepted verifier. Typed
memory, append-only session branches, declaration fences, canonical-path
mutation locks, steering/follow-up ordering, deterministic skill collision
rules, and transient-only retries live in `tools/abrl_lifecycle.py` behind thin
`tools/bandit.py` commands.

The live shadow audit found a stale Tsallis memory digest against the newer RL
stopping-time trials. Three replayed task transitions preserved frontier
selection while reducing prompt payloads from roughly 165k-169k characters to
1.6k-1.9k. Autonomous execution remains disabled. The current mathematical
frontier below remains the latest compiled proof boundary; this harness leaf
does not claim a new bandit/RL theorem.

## Current Frontier: Expected Positive-Part Consistency At Exact HittingAfter

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-EXPECTED-POSITIVE-PART-CONSISTENCY`
now compiles. It defines the expected positive part of the exact natural-causal
average realized behavior regret stopped at the genuine uncapped
inverse-square-root `hittingAfter` and proves that this expectation tends to
zero.

The proof reuses fixed-index integrability, derives integrability of
`max stoppedProcess 0` by domination with the absolute stopped process, and
uses a.e. hit finiteness plus the exact at-hit threshold inequality. Integral
monotonicity gives the threshold upper bound, and `squeeze_zero` consumes the
compiled threshold limit. The focused module, root import, three external
canaries, SafeVerify, axiom audit, and independent local review pass.

This is one-sided excess consistency, not convergence of the signed
expectation or expected absolute value. It supplies no uniform integrability,
L1 convergence, optional-stopping identity, uniform-in-model/index result,
raw-episode theorem, or complete UCB-VI. A next narrow leaf should connect
this one-sided endpoint to a concrete downstream decision/regret statement or
add a separately justified lower-side control without weakening the exact
source contracts.

## Compiled Parent: Cauchy-Schwarz Degree-Four Expected-Absolute Asymptotics

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-CAUCHY-SCHWARZ-ABSOLUTE-FIRST-MOMENT-ISBIG-O-DEGREE-FOUR`
now compiles. With all finite-MDP and generated-source parameters fixed, the
actual expected absolute stopped average realized behavior regret is
`O((scheduleIndex+1)^4)` over the public explicit schedule.

The route proves a reusable fixed-stopping-time Cauchy--Schwarz theorem for
the sum of square-root stopping-fiber masses. It identifies the first square
sum with the actual successor-round second moment and the second with the
shifted inverse-square series. The exact RL process then inherits a constant
times the square root of the accepted polynomial moment budget. Mathlib's
`IsBigO.sqrt` and the exact identity `sqrt(s^8)=s^4` finish the endpoint.
The two generic declarations, focused RL module, root import, five external
canaries, SafeVerify, axiom audit, and independent review all pass.

This is still a polynomial growth bound, not a decreasing rate. It supplies
no uniform-in-model or uniform-in-index moment theorem, uniform integrability,
L1 convergence, optional-stopping identity, sharp exponent, raw-episode
theorem, or complete UCB-VI. A next narrow leaf should improve the stopping
round moment/tail input or connect this integrability route to a concrete
downstream theorem without weakening the exact source contracts.

## Compiled Parent: Degree-Eight Stopping-Round Moment Asymptotics

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-POLYNOMIAL-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-ISBIG-O`
remains compiled. With all finite-MDP and generated-source parameters fixed,
the actual successor stopping-round second moment is
`O((scheduleIndex+1)^8)`. Its older Young-inequality expected-absolute
endpoint is superseded in exponent by the Cauchy--Schwarz child above.

The route proves a natural-number degree-eight checkpoint bound and absorbs
the named nonnegative weighted MDP failure constant into the scale. The
focused module, root import, and five external canaries compile; SafeVerify
and independent review pass. The named weighted constant remains symbolic.

## Compiled Parent: Polynomial Stopping-Round Second-Moment Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-POLYNOMIAL-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`
now compiles. It bounds the accepted ceiling start plus one by
`(Nat.ceil rateCoefficient + 2) * (scheduleIndex + 1)`, then raises that
linear scale through the existing fourth-power checkpoint and outer square.
The resulting checkpoint term is an explicit degree-eight polynomial.

The unchanged seventh-degree weighted failure-budget `tsum` is isolated as a
named MDP-only ENNReal/Real constant and proved finite under
`4 < mdp.horizon`. The actual successor stopping-round second moment is at
most the polynomial checkpoint term plus this constant. The stopped average
realized behavior regret remains integrable and inherits the corresponding
absolute-integral budget. The focused module and five external generic-MDP
canaries compile through the root import.

The named failure constant is not numerically evaluated. The fixed-model
`IsBigO` child above now consumes this pointwise envelope. No uniform moment
estimate, uniform integrability, L1 convergence, optional stopping, raw
episodes, or complete UCB-VI follows from either route.

## Compiled Parent: Explicit Tail-Start Deterministic Second-Moment Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-EXPLICIT-TAIL-START-DETERMINISTIC-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`
remains the exact-ceiling parent. It proves the reciprocal-linear scheduled
rate envelope, constructs the all-later max/ceiling start, bounds the
canonical `Nat.find` witness, and exposes the deterministic moment and
stopped-regret budgets. The polynomial child above bounds its checkpoint term
while preserving the same weighted failure series and exact source contracts.

## Compiled Parent: Deterministic Stopping-Round Second-Moment Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-DETERMINISTIC-STOPPING-ROUND-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`
now compiles. For each fixed inverse-sqrt index it chooses a canonical
deterministic checkpoint after the scheduled regret-rate envelope lies below
the threshold forever. From that checkpoint onward every delayed event is
charged to the exact compiled model/return failure budget. The squared
successor stopping round is bounded by the squared initial checkpoint plus
the seventh-degree weighted failure-budget series.

The finite ENNReal budget converts to a Bochner second-moment bound under
`4 < mdp.horizon`, and the stopped average realized behavior regret obtains a
deterministic absolute first-moment endpoint. Neither equality-fiber masses
nor an actual stopping-time integral remains in its RHS. The source/RL modules
and external generic-MDP canary compile.

The explicit child above now bounds this canonical checkpoint by a ceiling
expression. This parent remains the compatibility surface for the delayed
event and layer-cake construction; it still supplies no uniform moment
estimate, uniform integrability, L1 convergence, optional stopping, raw
episodes, or complete UCB-VI.

## Compiled Parent: Stopping-Round Second-Moment Absolute First-Moment Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPING-ROUND-SECOND-MOMENT-ABSOLUTE-FIRST-MOMENT-BOUND`
now compiles. It removes the equality-fiber distribution from the prior
absolute first-moment endpoint. For each fixed inverse-sqrt index under
`4 < mdp.horizon`, the expected absolute stopped average realized behavior
regret is at most the square root of the uniform coordinate second-moment
envelope times one half of the actual stopping-round second moment plus the
universal shifted inverse-square series.

The generic route proves an exact ENNReal weighted-fiber decomposition, takes
`ENNReal.toReal` under `MemLp 2`, identifies the resulting real sum with the
Bochner second-moment integral, and sums Young's inequality using Mathlib's
inverse-square p-series and `Summable.tsum_add`. The RL endpoint names the
new budget and preserves the exact generated source and fixed-index
contracts. Focused generic/RL builds and the external generic-MDP canary
compile.

This is a sharper fixed-index interface, not a bound on how the actual second
moment varies with `scheduleIndex`. The next theorem route must expose a
quantitative delayed-checkpoint second-moment bound from the existing model
and return tail budget before claiming a uniform/asymptotic estimate. Uniform
integrability, L1 convergence, optional stopping, raw episodes, and complete
UCB-VI remain open.

## Compiled Parent: Stopping-Fiber Absolute First-Moment Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-STOPPING-FIBER-ABSOLUTE-FIRST-MOMENT-BOUND`
now compiles. It exposes the quantitative content of the prior stopping-fiber
proof: for each fixed inverse-sqrt index and `4 < mdp.horizon`, the expected
absolute stopped average realized behavior regret is bounded by the square
root of the uniform coordinate second-moment envelope times the summable
series of square roots of genuine equality-fiber masses.

The generic theorem uses the a.e. equality-fiber decomposition, local `2,2`
indicator Holder, `integral_tsum_of_summable_integral_norm`, and the compiled
L2-round fiber summability bridge. The RL endpoint names the explicit RHS,
retains integrability, and preserves the exact generated source. The generic
module, RL module, and external generic-MDP canary compile. This is a finite
budget for one fixed index, not a theorem that the budget is uniform or tends
to zero; uniform integrability, L1 convergence, optional stopping, raw
episodes, and complete UCB-VI remain open.

SafeVerify, baseline-only axiom audit, independent no-P0-P3 local review,
refreshed retrieval indexes, the synchronized accepted lifecycle frontier,
and the full repository gate pass.

## Compiled Parent: Unbounded HittingAfter Expected Upper Bound

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-INTEGRABLE-EXPECTED-UPPER-BOUND`
now compiles. Under `4 < mdp.horizon`, every fixed genuine inverse-sqrt
`hittingAfter` stops an integrable exact natural-causal average realized
behavior-regret process, whose expectation is at most the hit threshold.

The generic bridge decomposes the L2 stopping time into equality fibers,
uses Young and the inverse-square p-series to sum square-root fiber masses,
and applies indicator Holder to uniformly L2 deterministic coordinates. The
RL consumer supplies one explicit coordinate second-moment ceiling, handles
round zero, and integrates the finite-hit `Set.Iic` certificate.

Seven declarations, root import, and the external generic-MDP `Tests.Basic`
canary compile. Placeholder and axiom audits are clean/baseline-only. This is
a fixed-index expected upper bound, not expected nonnegativity, an absolute-
moment rate, uniform integrability, L1 convergence, optional stopping, or a
complete UCB-VI theorem.

## Compiled Parent: Unbounded HittingAfter Fixed-Index Second Moment

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-SQUARE-INTEGRABLE-FINITE-STOPPING-TIME`
now compiles. Under the explicit horizon-at-least-five contract, it upgrades
every fixed genuine inverse-sqrt `hittingAfter` to
`OFUL.SquareIntegrableFiniteStoppingTime` on the exact generated source.
Squaring fourth-power checkpoints produces seventh-degree block widths;
inverse-tenth local confidence shares leave a summable inverse-cube shifted
pair envelope, and the exact exponential return share remains summable. A
generic indicator/`lintegral_tsum` bridge proves integrability of the square
and invokes Mathlib `memLp_two_iff_integrable_sq`.

The 17 declarations, project-root import, and external generic `Tests.Basic`
canary compile. Placeholder scanning is clean and three critical theorem
axiom reports are baseline-only. For horizons at most four the previous
first-moment theorem remains the valid boundary; no second moment is claimed.
The next consumer may use this fixed-index L2 contract for a carefully stated
random-horizon overflow or uniform-integrability step, but still must not
infer uniform-in-index moments, optional stopping, or a complete UCB-VI rate.

## Compiled Parent: Unbounded HittingAfter Fixed-Index First Moment

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-INTEGRABLE-FINITE-STOPPING-TIME`
now compiles. It proves that every fixed inverse-sqrt `hittingAfter` has an
integrable random horizon on the exact generated source. The key quantitative
step weights the explicit checkpoint crossing budget by cubic widths between
fourth-power checkpoints. Shifted model-tail charges reduce to a summable
inverse-square diagonal series, while the return share is polynomial times
exponential. Eventually delayed checkpoints lie in the compiled regret
violation event, and `lintegral_tsum` converts the crossing tails into the
first-moment contract `OFUL.IntegrableFiniteStoppingTime`.

The 21 declarations, project-root import, and concrete `Tests.Basic` canary
compile. Placeholder and four-theorem axiom audits are clean/baseline-only;
independent local checks found no P0-P3 issue. The next quantitative boundary
is a second moment or uniform-integrability contract strong enough for an
uncapped stopped-process L1/expectation consumer. This route proves neither
such a contract nor optional stopping.

## Compiled Parent: Unbounded HittingAfter A.E. Finiteness And In-Measure Consistency

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-UNBOUNDED-HITTINGAFTER-AE-FINITE-EVENTUAL-IMMEDIATE-STOPPING-AND-IN-MEASURE-CONSISTENCY`
now compiles. It uses genuine Mathlib `hittingAfter` to search below
`1/sqrt(n+1)` from `(n+1)^4` without a cap. The route exposes lower,
immediate-base, finite-hit, and stopping-time semantics; proves each fixed hit
finite a.e. from all-prefix a.e. convergence; combines every schedule index
on one a.e. set; and uses the summable-delay parent for eventual exact-base
stopping. The resulting `untopA` indices diverge, so the generic stopped
theorem gives a.e. convergence and Mathlib gives convergence in measure.

The 12 declarations, root import, and direct canaries compile. Placeholder
and public-axiom audits are clean/baseline-only. Independent review's one P3
request for standalone immediate-base and finite-hit semantic canaries was
repaired; follow-up review found no P0-P3. The separate fixed-index route now
adds expected-horizon integrability. Second moments, uniform integrability,
uncapped stopped-process L1 transport, and optional stopping remain open.

## Compiled Parent: Inverse-Sqrt First-Passage Eventual Immediate Stopping

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-INVERSE-SQRT-THRESHOLD-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-SUMMABLE-DELAY-AND-EVENTUAL-IMMEDIATE-STOPPING-L1-CONSISTENCY`
now compiles. It uses threshold `1/sqrt(n+1)`, identifies delay beyond the
fourth-power base exactly with the strict base-prefix threshold violation,
and embeds it in the compiled scheduled distance event. Dividing the
inverse-cubic/inverse-square L1 envelope by this threshold yields summable
inverse-`5/2` and inverse-`3/2` shifted p-series. The ENNReal delay
probabilities therefore have finite total mass, and first Borel-Cantelli
proves that almost every trajectory eventually stops exactly at `(n+1)^4`.
The root theorem also retains the complete stopped `MemLp 1`,
expected-absolute, `eLpNorm`, in-measure, and a.e. package.

The twenty declarations, root import, focused build, and direct semantic/L1
canaries compile. Placeholder and public-axiom audits are clean/baseline-only.
Independent read-only review initially found one P3 canary gap; the exact
external examples closed it and the reviewer confirmed no P0-P3 findings.

This closes the previous moving-threshold summability boundary without an
independence assumption and supplies eventual base membership to the
uncapped consumer above. It independently retains the stronger stopped L1
package, but does not expose genuine uncapped-hit finiteness.

## Compiled Parent: Reciprocal-Threshold First-Passage Delay Probability

The theorem route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-RECIPROCAL-THRESHOLD-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-VANISHING-DELAY-PROBABILITY-AND-L1-CONSISTENCY`
now compiles. It calibrates the finite first-passage threshold to `1/(n+1)`,
identifies delay beyond the fourth-power base exactly with the strict
one-sided base-prefix threshold violation, and embeds that event into the
compiled scheduled absolute-distance event. The explicit L1/Markov envelope
gives an inverse-square plus inverse-linear probability rate tending to zero.
The root theorem simultaneously returns the complete stopped `MemLp 1`,
expected-absolute, `eLpNorm`, in-measure, and a.e. package.
The sixteen declarations, root import, and external semantic/rate/root
canaries compile; all eleven theorem axiom reports are baseline-only, and
independent read-only review found no P0-P3 issue.

This remains the faster-threshold parent. Its inverse-square plus
inverse-linear Markov rate proves delay probability tends to zero, but the
inverse-linear term is not summable. The inverse-sqrt consumer above repairs
that boundary by slowing the threshold before applying first Borel-Cantelli.

## Compiled Parent: Capped Double-Linear Raw-Window First Passage

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-CAPPED-DOUBLE-LINEAR-RAW-WINDOW-FIRST-PASSAGE-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingTimeL1AverageRealizedBehaviorRegretConsistency`.
At schedule index `n`, Mathlib `hittingBtwn` scans every natural prefix from
`(n+1)^4` through `(n+1)^4+(2*n+1)`, stops at the first value at or below a
deterministic threshold, and otherwise returns the right endpoint. The module
compiles exact first-hit, base-hit, fallback, before-hit, strict-pre-cap-hit,
`IsStoppingTime`, and window-bound interfaces. The generic rate-controlled
parent returns the full `MemLp 1`, expected-absolute, `eLpNorm`, in-measure,
and almost-everywhere terminal.

This remains the structural finite-window parent consumed by the reciprocal
calibration above. A cap stop is not necessarily a hit; no optional-stopping
identity, raw-episode result, behavior/recommended-policy equality,
minimax/reachability, or complete UCB-VI is established.

## Compiled Parent: Threshold-Triggered Double-Linear Raw-Window Stopping

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-THRESHOLD-TRIGGERED-DOUBLE-LINEAR-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency`.
At schedule index `n`, it observes the natural average realized
behavior-regret process at `(n+1)^4`, stops there when the value is at most
a deterministic threshold, and otherwise stops at
`(n+1)^4+(2*n+1)`. Strong adaptation makes the trigger event known at the
base filtration, so Mathlib's two-constant piecewise constructor proves a
genuine stopping time. The generic rate-controlled parent then returns
`MemLp 1`, expected-absolute and `eLpNorm` convergence, convergence in
measure, and almost-everywhere convergence.

This remains the compiled one-shot, two-endpoint parent and contrasts with
the new first-passage scan. No optional-stopping identity, arbitrary candidate
set, raw-episode result, behavior/recommended-policy equality,
minimax/reachability, or complete UCB-VI is established.

## Current Frontier: Rate-Controlled Raw-Window Stopping-Time L1 Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-RATE-CONTROLLED-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalRateControlledRawWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency`.
At index `n`, a stopping prefix may choose any raw natural prefix from
`baseRounds n` through `baseRounds n+windowWidth n`. Positive bases and the
explicit contract `((windowWidth n+1)/sqrt(baseRounds n))->0` make the full
candidate budget vanish. The terminal returns stopped `MemLp 1`, expected-
absolute and `eLpNorm` convergence, convergence in measure, and a.e.
convergence; `n<=baseRounds n` is used only for the last conclusion.
`Tests.Basic` externally instantiates the theorem with the fourth-power base,
the strictly wider width `2n+1`, and a measurable trajectory event reaching
both endpoints.

The next theorem-level boundary is no longer deterministic raw-window growth.
A stronger route must either replace the contiguous-window union bound by a
structural optional-stopping/uniform-integrability argument, or derive a
rate-controlled base/window schedule from a concrete adaptive stopping rule.
The present theorem does not prove arbitrary finite candidate sets, arbitrary
diverging-stopping L1, raw-episode rates, behavior/recommended-policy
equivalence, minimax/reachability, or complete UCB-VI.

## Compiled Parent: Polynomial-Base Growing Raw-Window Stopping-Time L1 Consistency

The concrete route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-BASE-GROWING-RAW-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
remains the fourth-power/width-`n` parent. The new module proves its candidate
ratio directly, so it is now a checked instance of the generic theorem.

## Compiled Parent: Growing-Window Grid Stopping-Time L1 Consistency

The sparse-grid route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-GROWING-WINDOW-GRID-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
still permits an arbitrary finite number of future fourth-power grid
candidates through a summable-tail argument. It differs from the new route,
which permits every raw coordinate in one quantitatively limited contiguous
window.

## Compiled Parent: Fixed-Window Stopping-Time L1 Consistency

The fixed raw-prefix window route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-WINDOW-STOPPING-TIME-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
remains the direct parent for `n+1 <= tau_n <= n+1+window`. It uses finite
shifted all-prefix envelopes and proves the same L1/in-measure/a.e. package for
one deterministic width. It does not imply a growing raw-prefix window.

## Compiled Parent: Deterministic-Moment Expected Bounded-Stopping Regret

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-DETERMINISTIC-MOMENT-EXPECTED-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles across `ConcentrationSubGaussian` and
`FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitDeterministicMomentExpectedAverageRealizedBehaviorRegret`.
It proves a conservative sub-Gaussian second-moment wrapper, bounds each
positive deterministic-prefix average realized-regret second moment, sums
those envelopes over `Finset.Icc 1 T`, and dominates the exact stopped second
moment by that deterministic finite budget. The terminal replaces both parent
square roots by `(1/2) * sqrt(momentBudget)` while retaining stopped `MemLp 2`,
the `1/4` tail, `3/4` good mass, rate budget, and pathwise stopped certificate.

`Tests.Basic` reuses the trajectory-dependent one-or-two stopping time and
projects the stopped-moment and expected-integral bounds. The next boundary is
to simplify the conservative finite moment sum or derive a rate-compatible
budget; the present sum may grow with `T`. No sharp variance identity,
endpoint monotonicity, optional stopping, arbitrary confidence, unbounded
stopping, raw-episode rate, behavior/recommended-policy equivalence,
minimax/reachability, or complete UCB-VI is claimed.

## Compiled Parent: Exact-Moment Expected Bounded-Stopping Regret

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-EXPECTED-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles across `MeasureL2Indicator` and
`FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitExpectedAverageRealizedBehaviorRegret`.
It establishes deterministic-coordinate and bounded-stopped `MemLp 2`, names
the exact stopped second moment and finite positive-prefix logarithmic-rate
budget, charges the fixed quarter bad event by a valid `2,2` Holder bound, and
proves expected stopped regret is at most that rate budget plus
`(1/2) * sqrt(secondMoment)`. It also retains the three-quarter good mass and
the prior pathwise stopped rate.

`Tests.Basic` instantiates the terminal at the existing trajectory-dependent
one-or-two stopping time and projects stopped `MemLp 2`, the overflow bound,
and the expected integral bound. The next expected-rate route must prove a
deterministic or asymptotic envelope for the exact stopped second moment. This
theorem does not use optional stopping and does not claim arbitrary confidence,
unbounded stopping, nonnegative expected realized regret, raw-episode rates,
behavior/recommended-policy equivalence, minimax/reachability, or complete
UCB-VI.

## Compiled Parent: Explicit Three-Quarter Bounded-Stopping Good Event

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-EXPLICIT-THREE-QUARTER-GOOD-EVENT-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitThreeQuarterGoodEventAverageRealizedBehaviorRegret`.
Its five declarations prove the unchanged self-consistent finite model budget
is at most `1/8`, assign another `1/8` to the return window, and expose one
measurable joint bad event and every contained stopped violation with mass at
most `1/4`. The complement has real probability at least `3/4`, and every path
there obeys the stopped logarithmic average realized behavior-regret rate.

`Tests.Basic` applies the terminal to the existing trajectory-dependent
one-or-two stopping time and directly projects the model, stopped-tail, and
good-mass constants. The route relies on the explicit positive-horizon
contract because the scheduled exponent is `mdp.horizon + 5 >= 6`. It does not
parameterize the confidence schedule: arbitrary caller confidence, unbounded
stopping, stopped expectations, behavior/recommended-policy identification,
minimax rates, and complete UCB-VI remain separate routes.

## Compiled Parent: Bounded Stopping-Time Single-Model-Event Rate

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-SINGLE-MODEL-EVENT-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonNaturalCausalBoundedStoppingTimeSingleModelEventHighProbabilityAverageRealizedBehaviorRegret`.
Its thirteen declarations prove the self-consistent model bad event monotone
in the finite prefix, allocate one global return budget over the possible
positive stopped prefixes, and cover the stopped violation by one horizon-`T`
model event plus a return-only finite window. The resulting stopped tail is
`modelFailureBudget mdp T + ENNReal.ofReal returnDelta`, removing the older
repeated charging of cumulative model budgets at every possible prefix.

`Tests.Basic` reuses the trajectory-dependent stopping time selected from the
coordinate-zero sampled return and taking values one or two. It externally
projects filtered measurability, the sharper stopped tail, and the pathwise
joint-good rate. Independent review found no P0-P3; representative axioms are
baseline-only, and the full repository check passes. The model budget is
deliberately retained, so this is not a total-`delta` theorem. An unbounded anytime route still requires a summable
all-time event or separate moment/integrability infrastructure.

## Compiled Parent: Bounded Stopping-Time High-Probability Rate

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-BOUNDED-STOPPING-TIME-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET`
now compiles in
`FiniteHorizonNaturalCausalBoundedStoppingTimeHighProbabilityAverageRealizedBehaviorRegret`.
For one stopping time of the exact dependent natural filtration with pointwise
`1 <= tau <= T`, its fourteen declarations evaluate the exact average realized
behavior regret and a caller-scheduled fixed-prefix logarithmic rate at
`tau.untopA`. The stopped violation is measurable at filtration level `T`, is
contained in the finite union over `Finset.Icc 1 T`, and both event measures
are bounded by the exact finite sum of model plus return failure shares.

`Tests.Basic` reuses the trajectory-dependent stopping time selected by the
coordinate-zero sampled return and proves it always chooses one or two. The
terminal's filtered measurability, stopped tail, and pathwise good-window rate
are externally projected. Stopping-time regularity is used only for
measurability; probability uses pathwise containment and finite
subadditivity. The sharper single-model-event return-allocation consumer now
compiles above. An unbounded anytime route still requires summable all-time
events or separate moment/integrability infrastructure. Independent review
found no P0-P3; positive source mass for both canary branches and a concrete
total budget below one remain optional numerical nontriviality consumers.

## Compiled Parent: Diverging Stopping-Time Almost-Sure Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-DIVERGING-STOPPING-TIME-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalStoppingTimeAverageRealizedBehaviorRegretAlmostSureConsistency`.
Its fourteen declarations expose the exact dependent natural filtration,
prove the realized-regret process strongly adapted, apply Mathlib
`measurable_stoppedValue`, and transport the all-prefix a.e. limit through any
sequence of stopping times whose `untopA` values diverge. Since Mathlib maps
`top.untopA` to an arbitrary fixed Nat default, this forces eventual finiteness
but allows finitely many early `top` values. The practical terminal assumes
pointwise `n <= tau_n.untopA`.

`Tests.Basic` constructs a trajectory-dependent two-point stopping time from
the coordinate-zero sampled cumulative reward; explicit all-zero and all-one
reward trajectories witness both branches. The theorem does not use
optional stopping or prove a stopped expectation identity. The next distinct
boundary is a quantitative anytime/stopped-rate or stopped-expectation theorem
with the necessary event, moment, and integrability contracts; raw episodes,
behavior=recommended, minimax/reachability, and complete UCB-VI also remain
separate.

## Compiled Parent: Diverging Random-Prefix Almost-Sure Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-DIVERGING-RANDOM-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalRandomPrefixAverageRealizedBehaviorRegretAlmostSureConsistency`.
Its eight declarations make countable random evaluation measurable, transport
the deterministic all-prefix a.e. limit through any coordinatewise measurable
schedule tending to infinity almost everywhere, and expose a practical
pointwise `n <= tau_n` source terminal. All limits and schedules live on the
same generated dependent causal trajectory measure.

The external source canary uses a measurable trajectory-dependent schedule
which reads the prefix-one regret process and chooses `n+1` or `n+2`.
Independent read-only re-review found no soundness, API, or scope issue.

This parent closes arbitrary measurable diverging subsequences. Its natural
filtration, adaptedness, and stopping-time consumer now compile above. It still
supplies no optional-stopping expectation identity, anytime rate, or raw
online-episode theorem.

## Compiled Parent: All-Prefix Almost-Sure Equal-Round Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-ALL-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureConsistency`.
Its 21 declarations combine the existing successor-policy expected-regret
limit with Mathlib Cesaro convergence, an inverse-square fixed-prefix return
schedule, a square-root/logarithmic radius envelope, event-measure summability,
and first Borel-Cantelli on the same dependent causal trajectory measure.
The terminal exposes measurability of every deterministic-prefix process and
almost-everywhere convergence to zero; separate APIs expose the behavior and
return components, bad events, measure bounds, and summability certificate.

No independence is introduced: first Borel-Cantelli consumes only summable
event measures. The route preserves natural successor indexing, global
centering, and per-batch normalization before equal round averaging. Its
measurable a.e.-diverging random-prefix consumer now compiles above; this
parent still supplies no optional-stopping, anytime-rate, or raw-episode
theorem.

## Compiled Parent: Explicit Polynomial-Prefix Almost-Sure Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-ALMOST-SURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureExplicitSchedule`.
Its 21 declarations specialize the exact equal-round process to prefixes
`(n+1)^4`, construct summable `O((n+1)^-3) + O((n+1)^-2)` L1 envelopes, prove
summability of the scheduled expected absolute process and every fixed
positive distance-event probability series, and derive almost-everywhere
convergence by first Borel-Cantelli and reciprocal-natural thresholds.

The route adds no independence: first Borel-Cantelli needs only event
summability. It preserves per-batch normalization before equal round
weighting and therefore is not a transport of the older total-episode-mass
process. The all-prefix deterministic a.e. consumer now compiles above. This
fourth-power route remains regression and alternative L1/Markov evidence; it
must not be reported as anytime, stopping-time, raw online episode regret,
behavior/recommended policy equality, or complete UCB-VI.

## Current Frontier: All-Prefix L1 Equal-Round Natural Realized Regret

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-ALL-PREFIX-L1-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretL1Consistency`.
Its 23 declarations expose the cumulative normalized-return MGF, integrability
and first-moment bound, a linear-proxy inverse-square-root comparison, the
expected absolute equal-round realized behavior-regret envelope and all-prefix
zero limit, and Mathlib `MemLp`, exact exponent-one `eLpNorm`, named `Lp`, and
`TendstoInMeasure` endpoints.

This strictly strengthens the prior fourth-power-prefix in-measure result for
the same equal-round process. It does not use the older natural-causal L1
terminal as a transport: that terminal divides by total successor episode
mass, whereas this route divides each batch separately before averaging
rounds. The next theorem route must keep this distinction and may target a
summable sparse schedule for almost-sure convergence or a downstream
consumer, but it must not silently promote the result to anytime, stopping
time, raw online episode regret, behavior/recommended-policy equality, or
complete UCB-VI.

## Current Frontier: Explicit Polynomial-Prefix Absolute In-Measure Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-ABSOLUTE-IN-MEASURE-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalRealizedBehaviorRegretInMeasureExplicitSchedule`.
Its 11 declarations name the exact equal-round-weighted scheduled process,
distance events and probabilities; prove their measurability, a strict
event-outside lower bound, eventual event/probability domination, every
fixed-threshold probability limit, and the final Mathlib
`TendstoInMeasure` theorem.

The key new step is two-sided. The existing explicit parent supplies the
upper regret rate outside its model-tail/return event. The return-event
complement, expected cumulative behavior-regret nonnegativity, the exact
expected-minus-deviation identity, and positive scheduled rounds supply the
lower bound by the negative average return radius. Since both deterministic
sides and the exact union budget vanish, the distance-event probabilities
are squeezed to zero. No independence or new stopping-time contract enters.

Focused and `Tests.Basic` builds pass, with Bool/Bool canaries for the process,
distance set, eventual set inclusion, budget bound, probability limit, and
final convergence-in-measure endpoint. The axiom audit is baseline-only and
the placeholder scan is clean. Independent review found no proof, event,
criterion, regularity, or scope issue; its ledger and direct-canary feedback
was integrated. Exact retrieval was a no-hit; local compiled
and Mathlib APIs are proof evidence, while scenario/UCB-VI cards and weapons
remain placement or inspiration only.

The older `realizedSuccessorAverageRegret` convergence theorem controls a
total-episode-mass-weighted process. It is not identified with this route's
per-batch-normalized, equal-round-weighted process. The next theorem route
must explicitly add the infrastructure needed for an L1, almost-sure, or
all-prefix result; none follows from this deterministic fourth-power
subsequence theorem.

## Current Frontier: Explicit Polynomial-Prefix Upper-Tail Probability Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-UPPER-TAIL-IN-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalRealizedBehaviorRegretUpperTailInProbability`.
For every fixed `epsilon > 0`, its 8 declarations define the measurable
one-sided scheduled upper-tail set and its trajectory probability, prove
eventual inclusion in the compiled rate violation, retain the exact vanishing
model-tail/return budget, and prove the ENNReal probability tends to zero.

The route directly consumes the explicit fourth-power high-probability parent
with Mathlib `measurableSet_lt`, `measure_mono`, eventual strict-threshold
transport, and order squeeze. It inherits the parent's finite nonempty
Standard Borel, probability, positivity, bounded-mean, selected-reward
sub-Gaussian, path-support, filtration, and adaptation contracts without new
independence. Exact retrieval was a no-hit; compiled local declarations and
Mathlib APIs are proof evidence, while UCB-VI/scenario cards and weapons remain
placement or inspiration only.

Focused and `Tests.Basic` builds pass. Typed Bool/Bool canaries separately
consume measurability, event inclusion, exact-budget domination, and the
probability limit; representative axioms are baseline-only and independent
review findings are integrated. The next route must prove a matching lower
tail or connect this exact process to an existing absolute in-measure theorem.
Do not infer absolute `TendstoInMeasure`, all-prefix, anytime, minimax,
reachability, behavior/recommendation equality, or complete UCB-VI.

## Compiled Parent: Explicit Polynomial-Prefix High-Probability Average Realized Behavior-Regret Consistency

The route
`RL-FINITE-HORIZON-NATURAL-CAUSAL-EXPLICIT-POLYNOMIAL-PREFIX-HIGH-PROBABILITY-AVERAGE-REALIZED-BEHAVIOR-REGRET-CONSISTENCY`
now compiles in
`FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityExplicitSchedule`.
It uses scale/burn-in `n+1`, fourth-power prefix length, and exponential
return share. Its 25 declarations prove the own-count return proxy bound,
the normalized radius limit, the exact union-budget limit, the full average
realized-regret envelope limit, and one terminal that projects all
measurability, inclusion, probability, strict-subunit, and event-good
pathwise certificates at every scheduled prefix.

The route reuses the compiled burn-in/tail terminal, finite sums,
conditional-MGF radius algebra, Real log/exp/sqrt, ENNReal `ofReal`, and
filter limits. Contracts remain one dependent natural-causal source, finite
nonempty Standard Borel State/Action, probability, positive horizon/floors/
proxy/counts, bounded means, selected-reward sub-Gaussianity, path support,
and inherited filtration adaptation; no event independence is introduced.
Exact retrieval was a no-hit. Local compiled declarations and Mathlib cards
are proof evidence; UCB-VI/scenario cards and weapons are placement or
inspiration only.

This terminal is consumed by the compiled fixed-`epsilon` upper-tail
probability route above. Its one-sided and fourth-power-subsequence boundary
is unchanged.

## Current Frontier: Burn-In Tail High-Probability Logarithmic Realized Behavior Regret

The natural dependent causal route now has a fixed-`burnin`, fixed-`rounds`
terminal that removes early sampled-model failures from the probability event.
It charges the first `burnin` actual behavior-regret coordinates by `2H`, uses
the compiled model-good planning rate after burn-in, and combines the infinite
model tail with the normalized successor-batch-average return event. The exact
failure budget is `tailModelFailureBudget burnin + ofReal returnDelta`; no
independence is used.

Outside the joint event, cumulative realized behavior regret is at most
`2H * burnin + C_mdp * (1 + log rounds) + returnRadius`, and the positive-round
average is the same envelope divided by `rounds`. The module is root-imported,
its fully typed Bool/Bool terminal and definition-shape canaries compile, and
its proof dependencies are local/Mathlib declarations rather than theorem
cards or weapons.

The next theorem route is now specific: define explicit schedules
`burnin rounds` and `returnDelta rounds`, prove `burnin rounds / rounds -> 0`,
the logarithmic and normalized-return contributions divided by `rounds` tend
to zero, and `tailModelFailureBudget (burnin rounds) + ofReal
(returnDelta rounds) -> 0`. Until those schedule lemmas compile, this route is
not anytime, minimax, reachability, one-episode online regret, or complete
UCB-VI.

## Current Frontier: Fixed-Prefix High-Probability Logarithmic Realized Behavior Regret

The natural causal realized route now compiles on the one genuine dependent
self-consistent trajectory measure. Natural round `t` uses the actual batch at
coordinate `t+1`, generated by the policy selected from the prefix through
`t`, and subtracts that batch's sample-average return from the optimal initial
expected return. Reciprocal-batch conditional sub-Gaussian transport and the
existing strongly-adapted finite-sum theorem control the globally centered
normalized return-deviation sum.

An exact finite-sum identity combines this return process with the compiled
random behavior expected-regret process. The terminal's measurable joint event
is the actual finite-prefix model event union the normalized return event; its
measure, and the measures of both cumulative and average one-sided violation
sets, are at most the exact accumulated model budget plus
`ENNReal.ofReal returnDelta`. Outside the event, cumulative realized regret is
bounded by `C_mdp * (1 + log rounds)` plus the normalized return radius, and
the positive-round average is bounded by the same quantity divided by
`rounds`. No independence is used. The terminal separately exposes the
nontrivial-confidence contract: an exact total budget below one makes the
joint event and both violation probabilities strictly below one.

Contracts remain finite nonempty Standard Borel State/Action, probability,
positive horizon/rounds/base floor/proxy and scheduled batches, bounded means,
uniform selected-reward sub-Gaussianity, path support, and a valid return
share. The theorem is fixed-prefix batch-average realized behavior regret. It
does not provide one raw episode per online round, caller-controlled model
delta, uniform-time/anytime control, minimax/optimal rates, reachability, or a
complete UCB-VI theorem. The next substantial boundary is an all-prefix or
asymptotic consumer with an explicit return-share schedule and a principled
treatment of the accumulated model budget.

## Compiled Parent: Fixed-Prefix High-Probability Logarithmic Behavior Expected Regret

On the one genuine dependent causal trajectory measure, the random
`Finset.range rounds` sum of actual exploratory successor-policy expected
regrets now has a named measurable one-sided violation event. That event is
contained in the actual finite-prefix selected empirical-model bad event, so
its probability is at most
`selfConsistentScheduledCausalModelFailureBudget mdp rounds`. The terminal
also exposes the pathwise event-complement chain from the actual random process
to the natural planning sum and then to `C_mdp * (1 + log rounds)`.

The probability comes entirely from the compiled finite union of selected
count-and-reward model failures. The new exact budget theorem shows it is the
ENNReal finite sum of both local shares; it is deliberately not rewritten as
an arbitrary user delta or claimed to vanish as the prefix grows. Coordinate
transport unfolds that finite union, and the remaining proof uses measurable
finite sums, the coordinate actual-behavior planning theorem, the previous
logarithmic envelope, violation-set inclusion, and measure monotonicity.

Contracts remain finite nonempty Standard Borel State/Action, probability
initial law, positive horizon/base floor/reward proxy, bounded means, uniform
mean-compatible selected-reward sub-Gaussianity, and exploratory path support.
This is high probability over source randomness for behavior expected regret
at one fixed prefix. It is not realized-return, arbitrary-delta, anytime,
uniform-time, every-trajectory, minimax, or complete UCB-VI control. The next
realized fixed-prefix consumer above now compiles the normalized sampled-return
deviation and combines it with this model event.

## Compiled Parent: Natural-Causal Explicit Logarithmic Cumulative/Average Behavior Rate

The actual expected cumulative regret of the exploratory
`source.successorPolicyAt` process is now bounded on the one genuine dependent
causal trajectory measure by
`C_mdp * (1 + Real.log rounds)`. The corresponding actual average is bounded
by `C_mdp * (1 + Real.log rounds) / rounds`; both actual objectives have named
Mathlib `IsBigO` interfaces, and the actual average tends to zero. The terminal
also retains the refined cumulative envelope before constants are absorbed.

The proof expands the compiled coordinate rate into shifted inverse-square,
harmonic-exploration, and high-power terms. A telescoping comparison with
`1 / ((t+1)*(t+2))` and `Finset.sum_range_sub'` bounds the inverse-square sum;
`one_div_pow_le_one_div_pow_of_le` handles every exponent at least two;
Mathlib `harmonic_le_one_add_log` controls the exploration sum. The zero-round
case is explicit, while `Real.isLittleO_log_id_atTop`,
`tendsto_const_div_atTop_nhds_zero_nat`, and Mathlib asymptotic APIs close the
`log n / n` limit and actual Big-O wrappers.

The scalar sum leaves are unconditional. The causal consumers retain finite
nonempty Standard Borel State/Action, a probability initial law, positive
horizon/base floor/reward proxy, bounded deterministic means, uniform
mean-compatible selected-reward sub-Gaussianity, and exploratory path support.
This remains an expectation-over-source theorem: it is not realized-return,
every-trajectory, anytime/high-probability, reachability, minimax/optimal-rate,
or complete UCB-VI control. Its fixed-prefix high-probability random-process
consumer now compiles above and states the accumulated nonvanishing confidence
budget explicitly.

## Compiled Parent: Natural-Causal Finite-Prefix Cumulative And Average Behavior Rate

The actual exploratory `source.successorPolicyAt` expected-regret coordinates
now form a pathwise `Finset.range` cumulative process on the one genuine
round-varying dependent causal trajectory measure. The new Mathlib-backed
consumer proves every finite prefix integrable and uses
`ExpectationBochnerSums.integral_finset_sum` to identify its expectation
exactly with the finite sum of coordinate expected absolute regrets.
`Finset.sum_le_sum` therefore transports the compiled explicit coordinate
envelope to a cumulative deterministic rate. Dividing both sides by
`(rounds : Real)` gives the natural-prefix average bound, including the
zero-prefix convention.

The deterministic average rate is exactly `natWeightedAverage` with unit
positive natural weights. The compiled `tendsto_natWeightedAverage_zero`
theorem consumes the coordinate envelope's zero limit, and a nonnegative
squeeze proves the actual average behavior expected regret tends to zero. The
terminal exposes finite-prefix integrability, the exact integral/sum identity,
cumulative and average bounds, and both deterministic and actual average zero
limits.

Beyond the module-wide finite measurable-space assumptions, the finite-sum
identity only needs a probability initial law and bounded means for coordinate
integrability. The rate terminal retains finite nonempty
Standard Borel State/Action, positive horizon/base floor/reward proxy, uniform
mean-compatible selected-reward sub-Gaussianity, and path support. The explicit
logarithmic consumer above now closes the shifted inverse-square, harmonic,
and high-power finite sums and exposes actual cumulative/average pointwise and
Big-O bounds. This parent remains the exact finite-prefix integral/sum assembly
surface and does not itself prove realized-return, every-trajectory/anytime,
reachability, minimax/optimal-rate, or complete UCB-VI control.

## Compiled Parent: Natural-Causal Explicit Integrated Behavior Rate

The actual exploratory `source.successorPolicyAt` now has a finite-coordinate
expected-absolute regret bound on the one genuine round-varying dependent
causal trajectory measure. A generic Mathlib-backed event split integrates a
local rate outside one measurable bad event and a global envelope on it. The
causal instantiation uses the compiled pointwise planning certificate off the
single model-round event, the global `2 * horizon` policy bound on the event,
and the exact coordinate model-confidence mass bound.

The two confidence shares have real mass
`2 * selfConsistentScheduledLocalDelta mdp t`, so the bad-event contribution
is exactly `4 * horizon * delta_t`. The named envelope adds this term to
`selfConsistentScheduledCausalPlanningRateAt`; a closed-form theorem expands
the scale-squared reward/transition part, decaying exploration charge, and
`delta_t = 1 / (t + 2)^(horizon + 5)`. The envelope is nonnegative and tends
to zero, yielding a quantitative squeeze proof of expected-absolute
convergence without a realized-return MGF.

Regularity remains finite nonempty Standard Borel State/Action, probability
initial law, positive horizon/base floor/reward proxy, bounded deterministic
means, uniform mean-compatible selected-reward sub-Gaussianity, and path
support. The finite-prefix consumer above now sums this coordinate envelope,
proves the exact same-source integral identity, and obtains cumulative and
average behavior expected-regret bounds plus Cesaro consistency. This parent
itself remains per-coordinate and does not provide realized-return,
every-trajectory, anytime, reachability, minimax/optimal-rate, or complete
UCB-VI control.

## Compiled Parent: Natural-Causal Behavior Expected L1 Consistency

The actual exploratory `source.successorPolicyAt` expected-regret process now
has coordinate `Integrable` and `MemLp Real 1` proofs and converges to zero in
expected absolute value on the one genuine round-varying dependent causal
trajectory measure. The proof applies the existing policy regret bound
pointwise to obtain a global `2 * horizon` dominator, then lets Mathlib
`tendsto_integral_filter_of_norm_le_const` consume the compiled same-source
a.e. limit. Nonnegativity identifies the integral absolute value with the
integral of the process. This behavior-value argument does not use the
realized-return MGF.

The module also exposes the exact exponent-one `eLpNorm` identity, a named
`Lp Real 1` process and its norm convergence, and a joint terminal that pairs
behavior and realized `Lp`/`TendstoInMeasure` convergence on exactly the same
`source.trajectoryMeasure`. The terminal retains the parent finite nonempty
Standard Borel State/Action, positive horizon/base floor/reward proxy, bounded
means, selected-reward sub-Gaussianity, and path-support contracts; the
pointwise bound and coordinate integrability themselves need no Standard
Borel law or reward MGF.

The explicit integrated-rate consumer above now turns the coordinate
integrability and `2 * horizon` bound into a finite-coordinate expectation
envelope. This parent remains the same-source `MemLp`/`Lp` and joint behavior/
realized convergence surface; it does not itself provide cumulative or
average expected regret.

## Compiled Parent: Natural-Causal Behavior Expected In-Measure Consistency

The actual exploratory `source.successorPolicyAt` expected-regret process is
now coordinate-measurable and converges to zero in Mathlib
`TendstoInMeasure` on the one genuine round-varying dependent causal
trajectory measure. The generic Lean leaf represents a statistic of a
measurable finite policy-table selector as a finite sum of singleton
indicators. `Finset.measurable_sum` and `Measurable.ite` therefore avoid a new
Bellman-continuity development. For the concrete process, sampled empirical-
optimistic table measurability is composed with `measurable_pi_apply t`, and
unfolding the heterogeneous successor selector recovers the actual table and
the exploration rate at `t + 1`.

Coordinate strong measurability lets Mathlib
`tendstoInMeasure_of_tendsto_ae` consume the compiled behavior a.e. limit
without changing the source. A joint terminal pairs this behavior result with
the existing realized-regret `TendstoInMeasure` theorem on exactly the same
trajectory measure. Regularity is unchanged from the a.e. parent; the generic
selector lemma itself needs finite measurable State/Action with equality and
measurable singletons, a nonempty Action, and a probability initial law; it
does not need a nonempty State.

The L1 consumer above now supplies coordinate integrability, expected-
absolute convergence, exact exponent-one `eLpNorm`, and named `Lp`
convergence. This parent remains the coordinate-measurability and in-measure
surface; it does not supply an explicit finite-round integrated rate.

## Compiled Parent: Natural-Causal Behavior And Realized A.E. Consistency

The genuine round-varying causal source now has almost-sure consistency for
both the actual exploratory successor policy's expected regret and realized
successor-average regret. A new pointwise theorem works outside one
model-round bad event: it applies the sampled empirical model's recommended-
policy certificate, transports that recommendation to
`source.successorPolicyAt`, evaluates the occupancy-radius sum, and closes the
result under `selfConsistentScheduledCausalPlanningRateAt`. First
Borel-Cantelli is needed only for model events; no return event or round
independence enters the expected-regret limit. Nonnegativity and the vanishing
planning rate then give the a.e. squeeze.

The final theorem uses one intersection of full-measure sets. On it, every
sufficiently late sampled model is optimistic with its recommended-policy
occupancy certificate, the actual exploratory behavior expected regret tends
to zero, and realized regret tends to zero. The theorem deliberately keeps
the recommended/behavior distinction visible.

The finite-selector consumer above now supplies coordinate measurability and
same-source `TendstoInMeasure`. This parent remains the source of the a.e.
limit; it does not itself provide `MemLp`, `L1`, or expected-value convergence.

## Compiled Parent: Heterogeneous Natural Causal Almost-Sure Realized Consistency

The genuine round-varying causal source now has almost-sure realized
successor-average consistency on its own dependent trajectory measure. Lean
proves `exp (-sqrt n)` summable through Mathlib Schloemilch condensation,
transfers it to the actual successor-mass return schedule, and combines finite
model-event and return-event measure tsums with first Borel-Cantelli. No
cross-round independence is introduced. Almost every trajectory has a finite
model-good burn-in, is eventually return-good, and follows the existing
absolute-regret envelope to zero. The final joint theorem exposes coordinate
measurability and a.e. `Tendsto` to zero while retaining, on the same full set,
eventual all-state optimism and the recommended-policy occupancy-radius regret
certificate for every sufficiently late actual sampled empirical model. The
behavior-expected consumer above now reuses its joint realized terminal on the
same source and adds no new sampled-return regularity.

## Compiled Parent: Heterogeneous Natural Causal L1 Consistency

The genuine round-varying causal source now has `L1` consistency on its own
dependent trajectory measure. The route integrates the same-stream cumulative
return sub-Gaussian MGF, pays the global `2 * horizon` mean-policy bound only
on the post-burn-in model tail, and divides by actual successor mass. A
two-parameter limit makes the tail, fixed-burn-in planning envelope, and
normalized return first moment vanish. Lean exposes expected-absolute
convergence, coordinate `MemLp 1`, exact exponent-one `eLpNorm`, named
`Lp Real 1` convergence, and induced `TendstoInMeasure`.

The distinct almost-sure consumer above closes summable full-sequence
sampled-return deviations and first Borel-Cantelli on this same causal source;
it is not inferred from `L1` convergence alone.

## Compiled Parent: Heterogeneous Causal Explicit Weighted Rate

The genuine round-varying causal source now has a finite-prefix explicit-rate
terminal. A generic Mathlib-backed theorem shows that positive natural weights
preserve a zero limit under finite weighted averaging. Applied with
`episodes (t+1)`, it turns the coordinatewise scheduled planning rate into an
actual-successor-mass average tending to zero. The exact heterogeneous return
proxy is linear in that same mass, and its fixed-half normalized radius also
tends to zero.

One named model/return event retains its exact finite budget, every actual
sampled-model optimism certificate, and realized successor-average regret
below the explicit deterministic envelope. The existing finite Standard
Borel/probability/sub-Gaussian/path-support contracts are unchanged. Its
cumulative model budget retains early coordinate failures, so this parent is
not itself a convergence theorem. The natural causal route above now consumes
it with a tail event and finite burn-in dilution.

## Compiled Parent: Heterogeneous Causal Realized Successor Regret

The round-varying causal source now has an end-to-end finite-prefix realized
successor-average behavior-regret theorem. Coordinate `n+1` is generated by the
policy selected from the prefix through `n`; it is weighted by its actual batch
size `episodes (n+1)`. The denominator is the finite sum of those successor
batch sizes, and Lean proves the exact weighted expected-to-realized identity
against the compiled globally centered return deviation.

The terminal combines the actual-sampled model-confidence and return events,
keeps their exact finite failure budget, proves every sampled model optimistic,
and bounds realized successor regret by the weighted planning average plus the
heterogeneous return radius divided by actual successor episode mass. The
explicit weighted-rate module above now consumes this parent. Old constant-
window rates, the independent-window common-space theorem, and complete UCB-VI
do not transfer automatically.

## Current Frontier: Heterogeneous Causal Model Confidence

The round-varying causal source now has its own actual-sampled empirical-model
confidence route. Coordinate `t` uses `episodes t`, its own count/reward local
share, and the policy that actually generated that batch. Exact initial and
selected successor iid laws are integrated through the dependent `compProd`
surface; a finite union gives the genuine sum of nonuniform `ENNReal` shares.
No cross-round independence is introduced.

The self-consistent specialization closes event measurability, scheduled
positivity, path-floor calibration, and transition contraction. Off the named
event, every actual batch `0..rounds-1` yields optimism and recommended-policy
expected-regret. The downstream causal realized-successor theorem now performs
the model/return event union and regret assembly. That endpoint remains
fixed-prefix: the accumulated failure budget is not yet a vanishing-rate result.

## Current Frontier: Heterogeneous Causal Return Concentration

The round-varying actual-sampled causal process now has its own concentration
route. A supporting process centers each batch at the selected policy value of
its sampled initial state. The regret-facing process sets coordinate zero to
zero and globally centers successor coordinates `1..rounds` by the initial-law
expected selected-policy value. Exact iid fibers are transported through
dynamic `condDistrib` and trimmed `condExpKernel`; both processes are
`Filtration.piLE` adapted and have coordinate-specific conditional
sub-Gaussian MGFs. The global finite sum uses the true heterogeneous
`iidGlobalProxy(episodes t)` proxies and has a two-sided fixed-round tail.

The self-consistent wrapper closes total-proxy positivity from positive
rounds/horizon/reward proxy and scheduled positive batches. Heterogeneous
all-coordinate count/reward empirical-model confidence now compiles, and the
downstream causal realized-successor theorem performs their event union. The old
finite-window confidence or convergence rates cannot be reused by marginal
equality.

## Current Frontier: Heterogeneous Actual-Sampled Causal Law

ABRL now has a single actual-sampled self-consistent process whose coordinate
types vary with the schedule. Dependent `Kernel.trajMeasure` constructs the
law; the source reads only the latest batch, applies round-indexed budgets, and
uses the next round's exploration rate and batch size for the next kernel.
Initial, selected-fiber, regular-conditional, prefix/next, and projective laws
all compile.

This closes law construction, not the regret route. It is a different
round-varying algorithm from the independent family of fixed-parameter
windows, so the old finite-window confidence and `TendstoInMeasure` theorems
cannot be reused by marginal equality. Its heterogeneous sampled-return
concentration consumer now compiles; next build empirical-model confidence,
then assemble the causal successor regret theorem under the new normalization.

## Current Frontier: Actual-Sampled Convergence In Probability

The actual-sampled self-consistent schedule now lives on one Mathlib common
space. A new absolute finite-window adapter combines the model-good expected
successor-policy certificate with the return-good two-sided global deviation.
The dependent product `Measure.infinitePi` has each complete scheduled
trajectory law as an exact coordinate marginal, and evaluation transports the
same three-share event. The explicit regret and failure envelopes then prove
the realized successor-average process tends to zero in `TendstoInMeasure`.

This common-space theorem deliberately uses independent complete windows. It
does not identify the coordinates as prefixes of one online run. The distinct
heterogeneous causal source, projective laws, and fixed-round return
concentration now compile, but still need model-confidence and regret
transports; do not report either construction as pathwise, almost-sure,
anytime, reachability, minimax, or complete UCB-VI control.

## Current Frontier: Explicit Actual-Sampled Self-Consistent Rate

The scheduled actual-sampled route now has a finite-window rate consumer. For
`scale=n+2`, the exact self-consistent transition budget is bounded by
`12*card(State)*horizon/scale^2`; the three confidence shares equal
`ofReal(3/scale)`. The planning certificate combines the explicit
scale-squared reward/transition terms with the inverse-scale exploration
charge, and the full realized successor-average envelope adds the inverse-scale
globally centered return radius. Both explicit envelopes tend jointly to zero.

The new source terminal changes only the numerical certificate: actual sampled
rewards, successor indexing, initial exclusion, the measurable three-share
event, all-round optimism, global centering, and `episodes*rounds`
normalization are inherited unchanged. All parent finite nonempty Standard
Borel, probability, positive proxy, sub-Gaussian selected-reward, bounded-mean,
and path-support contracts remain visible.

A distinct heterogeneous causal source now compiles, but it is a new
round-varying algorithm and does not inherit this window rate. The next route
must transport conditional concentration and model confidence to that source,
or add a genuinely tighter rate ingredient. Lean compiles the explicit
inverse-scale-dominated formula, not a named `IsBigO` theorem; do not infer
reachability, almost-sure/anytime/minimax control, or complete UCB-VI.

## Current Frontier: Scheduled Actual-Sampled Self-Consistent Consistency

The actual-sampled route now has an explicit horizon-indexed schedule consumer.
With `scale=n+2`, it chooses `explorationRate=delta=1/scale`,
`rounds=scale^(horizon+4)`, scales the full-exploration path floor by
`explorationRate^horizon`, and chooses episodes one above the maximum of the
existing calibration threshold plus new count- and reward-shrink thresholds.
The compiled algebra gives `rewardBudget<scale^-2`,
`q<4*card(State)*horizon/scale^2`, and `q<=1/2`; hence the exact fixed-point
transition budget `q*(1+2*rewardBudget)/(1-q)` tends to zero.

Coordinates `0..rounds-1` still select source successor batches `1..rounds`;
the initial batch is excluded and count, reward-model, and return failures keep
three shares. Existing decaying-exploration and global-return envelopes show
that the named planning and full realized successor-average bounds tend to
zero, jointly with the three-share ENNReal failure budget. At each finite
window, the source terminal gives measurable-event control, all-round optimism,
and realized successor-average regret below that bound using actual rewards.

The next route must cross a genuinely different boundary: either place these
changing finite-window laws on a natural shared causal stream, or add one
sharper algorithm-specific finite-horizon rate. Preserve the current finite
nonempty Standard Borel, probability, positive proxy, sub-Gaussian selected
reward, bounded-mean, path-support, exact-fiber, successor-indexing, three-share,
global-centering, and `episodes*rounds` contracts. Theorem cards and proof
weapons remain evidence only; the compiled family is not state reachability,
almost-sure/anytime/minimax control, or complete UCB-VI.

## RL Stochastic IID Explicit Calibration Update

The sampled-reward iid empirical-model terminal now has a concrete exploratory
calibration producer. A common path-support visit floor gives every expected-
count lower bound; one uniform reward radius and the explicit transition budget
`rewardBound + 2 * rewardBudget` discharge all coordinate covers under the
existing scalar half-contraction.

The finite-round history-selected consumer transports this calibration through
every exact sampled-policy fiber, and the cumulative recommendation consumer
now sums its selected-radius conclusions. Calibration by itself still does not
imply exploratory behavior, realized, anytime, minimax, or complete-UCB-VI
control.

The external horizon-two canary uses a nondegenerate symmetric `+/-1` reward
source and internally proved floor/contraction conditions. Independent review
confirmed the denominator and doubled-envelope algebra; all reported excess
helper regularity was removed. Focused/root/Tests and the full gate pass.

## RL Stochastic IID Empirical-Model Confidence Update

The fixed-policy stochastic-reward iid route now compiles through actual
sampled-reward empirical means, one measurable count/reward union event, a
complete `FiniteBatchModel.Confidence`, global optimism, and the recommended
policy's selected-radius one-episode expected-regret bound. The construction
keeps separate count and reward confidence shares and uses the conservative
reward-sum proxy `episodes * varianceProxy`; sampled rewards need not be
bounded.

Verification includes focused/root/`Tests.Basic` builds, a nondegenerate
symmetric `+/-1` Bool/Bool canary whose 16384-episode margins and covers are
proved in Lean, clean placeholder and baseline-only public-axiom audits,
resolved independent review, refreshed indexes, and the full project gate.

The fixed-policy object and its explicit calibration are consumed by the
finite-round history-selected sampled-source route, whose pointwise output is
now summed by the cumulative recommendation theorem above. The next boundary
is exploratory behavior expected regret, not realized regret, anytime/minimax
control, or complete UCB-VI.

## RL Stochastic Common-Space L1 Update

The stochastic common-space route now compiles beyond convergence in
probability. Each realized-behavior regret coordinate is integrable and
`MemLp 1`; expected absolute regret and exact exponent-one `eLpNorm` converge
to zero, and the named `Lp Real 1` process converges in the native Lp topology.

The key concentration adapter evaluates the existing sub-Gaussian MGF at the
reciprocal square-root proxy. This preserves unbounded sampled rewards: only
mean-reward policy regret uses the deterministic `2H` envelope. The L1 bound
combines the planning term, one count-event share, and the normalized MGF
first-moment term.

The independent complete-window route remains useful as a separate coupling.
Natural causal `L1` now compiles on the heterogeneous dependent source above;
it is not derived from these coordinate marginals. Natural-causal almost-sure
consistency now also compiles separately through first Borel-Cantelli on that
dependent source. Separately formalized stochastic reward-mean estimation
remains open. No every-trajectory pathwise, anytime, minimax, or complete-
UCB-VI theorem follows from the independent coupling.

## RL Stochastic Common-Space In-Probability Update

The stochastic cumulative decaying-exploration route now has a compiled common
probability space. A new absolute finite-window adapter uses the two-sided
global return event and expected policy-regret nonnegativity. The complete
scheduled stochastic trajectory laws are then placed on a dependent
`Measure.infinitePi`; coordinate evaluation has the exact scheduled marginal,
and the common-space realized-regret process is measurable and converges to zero
in measure.

Bool/Bool canaries instantiate the common measure, every exact coordinate
marginal, and the terminal `TendstoInMeasure` theorem with a non-degenerate
symmetric stochastic reward source. The route retains global initial-law
centering, successor indexing, two confidence shares, and the
`episodes * rounds` denominator.

The next semantic boundary is a natural shared-stream construction with
cross-window causal consistency, or a separate stochastic reward-mean
estimation route. The current product coupling is independent across complete
scheduled experiments, so it does not imply pathwise, almost-sure, anytime,
minimax, or complete-UCB-VI control.

## RL Stochastic Cumulative Regularity Closure Update

The dependent Standard Borel boundary on the stochastic cumulative consistency
route is now compiled. `EpisodeStep` transports the product Standard Borel
structure through its exact coordinate equivalence. Deterministic `Nat`-indexed
batch trajectories then use Mathlib's generic countable product; a dedicated
constant-family wrapper stabilizes the stochastic trajectory case. Finite
`Fin`-indexed batches synthesize from those coordinates.

New `_of_standardBorel` finite- and all-window endpoints retain only State and
Action Standard Borel assumptions. Bool/Bool canaries infer all five relevant
composite instances and instantiate both endpoints without indexed witness
arguments. The underlying finite-window events, two confidence shares,
violation-set coverage, and joint scalar limit are unchanged.

The downstream common-space route now supplies a separately justified
independent product coupling and `TendstoInMeasure`. A natural nested causal
shared stream, stochastic reward-mean estimation, and complete UCB-VI remain
downstream theorem routes.

## RL Stochastic Cumulative Consistency Route Update

The cumulative projected-selector stochastic source now reaches a compiled
decaying-exploration realized successor-average consistency route. Exact
trajectory pushforward reuses the deterministic cumulative count/optimism and
expected exploratory-behavior certificate. A separately normalized globally
centered stochastic return radius is added through the two-delta transport.
Both the two-share failure budget and the resulting realized bound tend to zero.

The finite-window endpoint locks the measurable combined event, named violation
set coverage and tail, projected optimism, and realized regret bound. Its parent
all-window endpoint exposes four indexed Borel witnesses, while the downstream
regularity wrapper now infers them. Both retain a family of changing
finite-window experiments rather than convergence on one process. The concrete
Bool/Bool symmetric-reward canaries lock the complete finite-window result type
and the witness-free all-window wrapper.

Independent review found no P0/P1. Its missing all-window canary and leaked
scalar radius contracts were repaired; the later regularity-closed route now
discharges the documented dependent Borel boundary.

The next route should not inflate this result into UCB-VI. Useful downstream
boundaries are a genuine stochastic shared-stream coupling with separately
proved marginals or stochastic reward-mean estimation. Neither is supplied by
this route.

## RL Concrete Stochastic Realized-Behavior Route Update

The projected stochastic empirical-optimistic source now reaches a concrete
fixed-window realized successor-average behavior-regret theorem. The route
keeps count and return confidence shares separate, derives the source's dynamic
global-return measurability, transports projected recommendation regret to the
actual exploratory policies with an explicit exploration charge, rewrites the
fixed-bonus occupancy average to `horizon * (2 * transitionBonus)`, and adds the
globally centered stochastic return radius.

Independent review found no high-severity issue and confirmed the event union,
deviation sign/normalization, projected indexing, and exploration charge. The
positive Bool/Bool canary now locks the complete endpoint proposition. The
dependent batch and trajectory `StandardBorelSpace` instances remain explicit
caller contracts rather than locally synthesized instances.

The next theorem route should replace the fixed transition bonus and fixed
exploration charge by a cumulative or scheduled count-radius source, then prove
a vanishing realized average rate without changing global centering, successor
indexing, or the two confidence allocations. The current theorem excludes the
initial batch and is not stochastic reward estimation, anytime/common-space
convergence, minimax control, or complete UCB-VI.

## RL Stochastic Reward Erasure Law Update

The project now compiles
`FiniteHorizonStochasticRewardErasureLaw`. Coordinatewise erasure discards the
sampled Real reward while retaining every action and next state. A reusable
two-output `compProd` map theorem and horizon induction identify the mapped
stochastic trajectory kernel with the ordinary policy trajectory kernel.
Initial-state mixing, a finite iid trajectory family, and the existing
known-reward `EpisodeBatch` conversion preserve that equality exactly.

The final projected batch uses `mdp.reward`, not the sampled reward value. The
external canaries make this distinction concrete: a Bool-action uniform policy
and symmetric non-degenerate reward source instantiate the law, action and next
state are retained, sampled reward `7` is erased, and the empirical batch
reward is the known mean `0`. Zero horizon and zero episodes are also covered.
Only the final measurable `EpisodeBatch` projection needs measurable
singletons for State and Action; no Standard Borel contract is introduced. The
next narrow route is now the adaptive lift: define the prefix-dependent
stochastic known-mean empirical-transition source, identify its projected
successor count law, and consume the compiled count/optimism and
realized-regret interfaces. This leaf alone does not prove stochastic reward
learning, adaptive regret, minimax rates, or complete UCB-VI.

## RL Adaptive Stochastic Realized-Regret Update

The project now compiles fixed-window expected-to-realized behavior-regret
transport for adaptive batches of complete stochastic-reward episodes. The new
global statistic centers each selected batch by the policy's expected return
under the initial-state law. It includes the sampled initial-state policy-value
fluctuation that the previous per-state-centered route intentionally omitted.

Within one iid batch, the sampled-return and value-fluctuation components are
combined without an independence claim, using the squared sum of square roots
of their proxies. Across adaptive rounds, the exact prefix-selected conditional
law supplies successor conditional MGFs; the tail charges coordinates
`1..rounds`, while coordinate zero is a zero placeholder. Exact finite-sum
algebra connects this deviation to realized cumulative and average regret.

The reusable endpoint combines any measurable count/optimism bad event of mass
at most `delta` with the return-deviation event of mass at most `delta`, and on
the complement adds the normalized sub-Gaussian radius to the expected-regret
bound. The fixed-policy reward-erasure and known-reward iid batch law now
compile. The next narrow route should lift them to a concrete adaptive
stochastic empirical-policy source and matching count/optimism event. It
should not jump directly to an anytime, minimax, or complete UCB-VI claim.

## RL Adaptive Stochastic Episode Concentration Update

The project now compiles an adaptive history-kernel trajectory whose
coordinates are finite iid families of complete stochastic-reward episodes.
The initial batch uses one fixed policy; every successor prefix selects its own
policy and the successor kernel is exactly that policy's compiled iid
stochastic trajectory-family law. The target statistic remains the sum of
sampled returns centered by each trajectory's own initial-state policy value.

The proof retains the prefix with `Kernel.id ×ₖ batchKernel`, maps the
prefix/batch pair through the dynamic deviation, identifies the resulting
conditional law, and feeds its MGF into the `piLE` strongly-adapted finite-sum
tail. The initial batch is a genuine deviation coordinate, not a zero
placeholder. The total proxy is exactly the number of adaptive rounds times
the compiled iid episode-batch proxy.

Explicit prefix×batch deviation measurability and a `StandardBorelSpace` for
the infinite real-reward trajectory are regularity contracts. External
Bool/Unit canaries check the public source, law, MGF, numeric proxy, and tail
surfaces. A history-sensitive Bool-action `Kernel.piecewise` canary also proves
that different prefixes select unequal complete conditional iid batch laws.
Independent review's canary-strength and overbroad-regularity findings are
repaired; the concentration endpoints require `Nonempty Action`, not a global
`Nonempty State` contract. The globally centered expected-to-realized
behavior-regret consumer now compiles above; this parent alone still carries
no regret or anytime conclusion.

## RL Finite IID Stochastic Episode Concentration Update

The project now compiles
`FiniteHorizonStochasticRewardIIDTotalReturnConcentration`. Its twelve
declarations define the complete stochastic-trajectory product law, probability
instance, exact coordinate marginal, episode deviation/sum/proxy surfaces,
episode independence, coordinate and sum MGFs, and the fixed-sample tail. A
two-episode Bool-state canary checks the exact marginal, independence, proxy
`11`, MGF, and tail. Zero-episode canaries separately check the empty product
probability law, zero sum, zero proxy, and zero-proxy MGF; the positive-proxy
tail contract deliberately excludes that degenerate branch.

The independent coordinates are complete episodes sharing one fixed policy and
initial-state law. The next narrow route is an adaptive history-kernel producer
whose successor law is this iid product, followed by an exact conditional-MGF
transport. Within-episode stage independence, uniform/anytime control, regret,
optimism, minimax rates, and complete UCB-VI are not implied.

## RL Initial-Law Sampled Total-Return Concentration Update

The project now compiles
`FiniteHorizonStochasticRewardInitialLawTotalReturnConcentration`. Its five
declarations add a reusable finite-state `compProd` MGF mixture theorem, the
full initial-state-dependent sampled-return deviation and measurability, and
the full-trajectory MGF/tail endpoints. The common proxy remains
`horizon * rewardVarianceProxy +
meanBellmanInnovationVarianceProxy rewardBound horizon`.

The proof integrates fiberwise MGF bounds with Mathlib Fubini APIs. It centers
each trajectory by the recursive policy value of that trajectory's sampled
initial state, not by one global mean. Its finite iid episode product/sum
consumer now compiles above. Adaptive policy updates, uniform or
anytime control, regret, optimism, minimax rates, and complete UCB-VI remain
open.

## RL Sampled Total-Return Concentration Update

The project now compiles
`FiniteHorizonStochasticRewardTotalReturnConcentration`. Its 33 declarations
define actual sampled return minus recursive policy value, prove the exact
pathwise reward-noise/Bellman split, construct the retained action/state and
centered reward kernels, identify their mapped laws with the generated head,
and prove the one-step and recursive MGFs plus fixed-horizon tail with additive
proxy `remaining * rewardVarianceProxy +
meanBellmanInnovationVarianceProxy rewardBound remaining`.

The proof uses conditional `add_compProd`, not independence of two marginal
MGFs. External canaries cover nondegenerate sampled rewards, randomized actions,
and randomized transitions. Its explicit initial-state-law consumer now
compiles above; a finite iid episode source is the next boundary before any
stochastic-reward regret claim. Uniform/anytime,
adaptive empirical optimism, minimax, and complete UCB-VI remain open.

## RL Mean Bellman Innovation Concentration Update

The project now compiles
`FiniteHorizonStochasticRewardBellmanInnovationConcentration`. Its 15
declarations add the symmetric interval proxy identity, stage and cumulative
Bellman-innovation proxies, policy-value envelope, recursive statistic and
measurability, exact reward-dropping and Bellman-mean laws, one-step and
generated-trajectory MGFs, and a fixed-horizon two-sided tail.

The centered head variable is `r(s,a)+V(s')-V_current(s)`, so it includes both
randomized-policy action selection and transition randomness. Its cumulative
proxy is `sum k=1..H, (k*rewardBound)^2`; this is deliberately neither a
next-state-only statement nor the coarse whole-return `H^2` shortcut. Randomized
action and uniform-transition canaries respectively witness a `3/2` innovation
and two transition branches of mass `1/2` with cumulative innovations
`+1/2/-1/2`. Independent review found no route defect after those compile and
coverage repairs. Its conditional combination with actual sampled reward noise
now compiles in the sampled total-return route above. This parent alone must
not be reported as sampled-return, regret, uniform/anytime control, minimax
rate, or complete UCB-VI.

## RL Stochastic Reward Cumulative Concentration Update

The project now compiles
`FiniteHorizonStochasticRewardCumulativeConcentration`. Its seven declarations
add two generic kernel-MGF bridges, define the actual state/action-centered
cumulative reward deviation, prove joint measurability, transport the head
MGF to the one-step action/reward/state kernel, and prove the recursive MGF
and fixed-horizon two-sided tail with total proxy
`remaining * varianceProxy`.

The recursion uses the sampled next state and Mathlib `add_compProd`. The
source models reward and next state as conditionally independent given the
current state/action via `rewardNextStateKernel`; it does not assume
independence between trajectory stages and does not replace the target by an
`horizon^2` bounded-return estimate. A two-step symmetric canary computes the
all-positive event mass as `1/4` and proves the `delta = 3/4` tail event has
strictly positive mass. The transition/Bellman mean innovation route now
compiles separately; the next narrow route should combine it with this
reward-noise term to control sampled total return around `valueRemaining`.
That route must keep reward noise, transition noise, and policy regret
separate; no uniform/anytime, optimism, minimax, or complete UCB-VI claim
follows here.

## RL Stochastic Reward Head Concentration Update

The project now compiles `FiniteHorizonStochasticRewardConcentration`. Its ten
declarations define the measurable sampled-action head mean and actual reward
deviation, package a uniform selected-law sub-Gaussian contract, construct it
from common interval support, and expose conditional MGF, global MGF, and
one-step two-sided delta-tail endpoints on the generated trajectory law.

The route preserves the selected action-dependent law and centers by
`mdp.reward state headAction`; it does not use the randomized reward marginal.
The symmetric `{-1,1}` canary is nondegenerate and computes proxy one. Its
multi-step cumulative reward-noise consumer now compiles downstream. No
transition/Bellman innovation tail, uniform/anytime, regret, optimism,
minimax, or complete UCB-VI theorem follows from this leaf.

## RL Stochastic Reward Head Conditional-Law Update

The project now compiles `FiniteHorizonStochasticRewardConditionalLaw`. Its
ten declarations add the measurable head-action projection, the state-frozen
selected reward kernel, exact action/reward composition-product
factorization, action marginal, generated action map, one-step and generated
`condDistrib` laws, and the terminal trimmed `condExpKernel.map` law.

This is the first regular-conditional adapter on the actual reward-bearing RL
trajectory. Its separately contracted bounded/sub-Gaussian source,
head-reward conditional/global MGF, and cumulative reward-noise tail now
compile downstream. The remaining narrow boundary is transition/Bellman
innovation concentration; mean compatibility alone still does not imply it.

## RL Stochastic Reward Head Marginal Update

The project now compiles `FiniteHorizonStochasticRewardMarginal`. Its 16
registered declarations provide measurable first-coordinate projections, two
Markov marginal kernels, exact generated head/action-reward/reward map laws,
joint rectangle factorization, the randomized-policy reward mixture, and one
bundled generated-law endpoint.
Independent review found no semantic error; its stage-index and nondegenerate
generated-law coverage risks are resolved by horizon-two and symmetric-source
transport canaries.

This is the missing law adapter between actual sampled stochastic trajectories
and concentration. Its regular conditional-law, one-step selected-law, and
cumulative reward-noise sub-Gaussian consumers now compile. Transition and
Bellman innovation control remains the next boundary, and mean compatibility
alone still does not imply it.

## RL Stochastic Reward Trajectory Update

The project now compiles `FiniteHorizonStochasticRewardTrajectory`. Its 18
registered declarations construct the reward-bearing finite trace and Markov
trajectory kernels, prove actual sampled cumulative reward measurable and
`L1`, establish the statewise stochastic backward-value identity, construct
the full initial-state probability law, and expose one terminal equating the
sampled-return expectation with both stochastic and existing mean `valueAt 0`.
The nondegenerate generated-law canary computes first sampled reward `1` with
exact mass `1/2`, so it detects accidental replacement by the mean reward.

The proof preserves the prior selected-reward `L1` contract and does not add a
boundedness shortcut. Exact first-coordinate marginals now compile downstream;
the next theorem route should transport them through a finite-history
filtration and regular conditional law, then consume a separate bounded or
conditional-sub-Gaussian source. It must not infer concentration or regret
tails from mean compatibility alone.

## RL Stochastic Reward Planning Update

The project now compiles `FiniteHorizonStochasticRewardBellman`. Its 14
registered declarations add a mean-compatible Real reward-kernel contract,
the conditionally independent reward/next-state product kernel, integrability
of the sampled one-step return, exact stochastic-to-mean Bellman identities at
the action and policy levels, an independent stochastic backward recursion,
all `valueRemaining`/`valueAt` identities, a deterministic embedding, and one
terminal planning-transport theorem.

This closes the mean-planning layer only. The downstream stochastic trajectory
route now compiles. The next narrow route should expose the existing sampled
reward coordinate as a reusable marginal or conditional law before adding a
separately contracted concentration or regret consumer. Arbitrary correlated
reward/next-state laws, stochastic realized regret, minimax rates, and complete
UCB-VI remain open.

## RL Common-Space L1 Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceL1Consistency`. Its eight
public declarations convert the expected-absolute route into native Mathlib
`MemLp`, `eLpNorm`, and `Lp Real 1` interfaces and prove convergence to zero in
the `Lp` topology. The terminal also derives convergence in measure through the
standard Mathlib Lp bridge.

This adds no assumptions beyond the parent and does not use a theorem-card as
proof. The next honest theorem boundary is a natural nested shared stream or a
stochastic reward-law MDP extension. Current L1 convergence is under the
independent product coupling and does not establish pathwise/a.s./anytime,
cross-window causal, minimax, or complete UCB-VI behavior.

## RL Expected-Absolute Common-Space Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceExpectedConsistency`.
Its 17 public declarations prove reward-consistent support for generated
adaptive successor batches, a uniform `2*horizon` almost-everywhere envelope,
integrability of every scheduled common-space regret coordinate, an explicit
finite expected-absolute bound, and convergence of those expectations to zero.

The proof reuses the exact common-space marginals and finite-window good-event
bound, then integrates the measurable bad-event indicator and converts the
vanishing `ENNReal` confidence budget to `Real`. Contracts and retrieval status
are recorded in `BRL-OP-RL-BELLMAN-001`; theorem cards remain route evidence,
not compiled proof. The next honest boundary is either a natural nested shared
stream or stochastic reward laws. The current independent-coordinate coupling
does not establish pathwise, almost-sure, anytime, minimax, or complete UCB-VI
results.

## RL Common-Space Convergence-In-Probability Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceConsistency`. It upgrades
the indexed finite-window family to one dependent infinite-product probability
space. Every coordinate marginal is exactly the corresponding scheduled
adaptive trajectory law, every realized-behavior regret coordinate is
measurable, and the resulting process converges to zero in Mathlib
`TendstoInMeasure`.

The finite-window input is strengthened from a one-sided realized-regret bound
to an absolute bound using expected-regret nonnegativity and the already
compiled two-sided return deviation. The common event is the coordinate pullback
of the same measurable count/return union, so no new confidence share is added.
The convergence proof squeezes its distance-event probability between zero and
the existing doubled failure budget once the deterministic bound is below the
requested tolerance.

The coupling is explicitly `Measure.infinitePi`, so different schedule windows
are independent coordinates. It is not a nested implementation of one online
algorithm across horizons. The next theorem-level choice is either a natural
shared-stream coupling for pathwise/almost-sure statements or a stochastic
reward-kernel extension; anytime control, minimax rates, and complete UCB-VI
remain open.

## RL Episodewise Return-Concentration Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeEpisodewiseRealizedBehaviorConsistency`. It
replaces the coarse whole-batch proxy
`(episodes*horizon)^2` by the episodewise proxy
`episodes*horizon^2` and transports the sharper MGF through the adaptive
successor law, the strongly-adapted cumulative tail, the count-event union, and
the finite-window and indexed decaying-exploration source terminals.

Complete episode rows, and hence episode returns, are proved independent under
the mapped `iidEpisodeBatchMeasure`; stage records inside one episode are never
assumed independent. The cumulative proxy is
`rounds*episodes*horizon^2`, so the normalized radius is exactly
`horizon*sqrt(2*log(2/delta)/(episodes*rounds))`. It is bounded by the prior
decaying envelope and tends to zero. The terminal retains two confidence
shares, optimism, named violation containment and tail, and indexed changing
sample spaces. A stronger convergence mode still needs an explicit common
space. That explicit independent-coordinate common-space and
`TendstoInMeasure` consumer now compile downstream; a natural nested process,
stochastic rewards, anytime control, minimax rates, and complete UCB-VI remain
outside this theorem.

## RL Decaying-Exploration Realized Consistency Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeDecayingExplorationRealizedBehaviorConsistency`.
It proves exact closed forms for the whole-batch and cumulative return proxies,
then cancels the scheduled episode count from the normalized return radius.
Under the existing schedule, that radius is bounded by
`2*horizon/(n+2)` and tends to zero.

The realized average behavior-regret certificate is the compiled expected
behavior certificate plus this radius. It is nonnegative and tends to zero.
The count/return union uses two copies of `delta_n`; that `ENNReal` budget also
tends to zero. The all-window theorem combines their joint limit with, for
every indexed scheduled sample space, a measurable combined event, its tail,
realized violation containment/tail, roundwise optimism, and the realized
average bound.

The next theorem-level boundary is an explicit common-space embedding or
coupling if one-process convergence in probability, pathwise convergence, or
almost-sure consistency is required. A separate improvement may replace the
coarse whole-batch proxy by episode-level concentration. Neither follows from
the current dependent family; stochastic rewards, anytime guarantees, minimax
rates, and complete UCB-VI also remain open.

Independent review found no theorem defect. The review-driven harness repair
now preserves multiline result-level `letI` binders, so CLI and blueprint
retrieval expose the complete all-window statement. Numeric doubled-budget and
strict violation-membership canaries lock the two semantic definitions used by
the terminal theorem.

## RL Finite-Window Realized Behavior Regret Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeRealizedBehaviorRegret`. It defines actual
recorded successor-batch returns, identifies their prefix-kernel means with the
selected policies, and proves conditional whole-batch Hoeffding increments on
the adaptive trajectory filtration. A strongly-adapted finite-sum theorem gives
the explicit return-deviation event and tail.

The exact decomposition converts successor expected behavior regret into
realized behavior regret on the same trajectory. The reusable transport unions
the count and return events, while the concrete decaying-exploration endpoint
retains optimism and has failure budget `2*delta_n` in unsimplified ENNReal
form. Successor coordinates are exactly `1..rounds`; the initial batch at zero
is not charged.

The deterministic normalized-radius asymptotic and dependent all-window
realized consistency theorem now compile downstream. A common-space embedding
is still required for one-process probability, pathwise, or almost-sure
claims. The current proxy is sufficient but not sharp in the number of
episodes, and the theorem does not cover stochastic rewards, minimax rates, or
complete UCB-VI.

## RL Decaying-Exploration Behavior Consistency Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeDecayingExplorationBehaviorConsistency`.
Starting from a full-exploration path-support floor `baseVisitFloor`, it proves
the exact stagewise scaling of the state-action visit floor by
`explorationRate^(stage+1)` and the uniform horizon floor
`baseVisitFloor*explorationRate^horizon`.

The explicit finite-window schedule uses `q_n=n+2`,
`explorationRate_n=1/q_n`, `rounds_n=q_n^(horizon+4)`,
`visitFloor_n=baseVisitFloor/q_n^horizon`, and `delta_n=1/q_n`.
Its effective visit mass is exactly `baseVisitFloor*q_n^4`. Thus the existing
scheduled recommendation envelope is `O(q_n^-2)`, the exploratory behavior
charge is `O(q_n^-1)`, and the deterministic average behavior certificate and
`ENNReal` failure budget tend jointly to zero.

For every finite window, the source endpoint retains the measurable cumulative
count event, its `delta_n` tail, roundwise optimism, and an outer-measure bound
for the named behavior-regret violation set. This closes compatible decaying
exploration for expected behavior regret. A finite-window realized-regret
martingale transport now compiles downstream; reward-radius asymptotics and an
explicit common-space coupling remain open.
Do not infer violation-set measurability, one-process pathwise/probability/a.s.
convergence, stochastic rewards, minimax UCB-VI, or complete UCB-VI.

## RL Exploratory Behavior Regret Transport Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret`. It expands the
exploratory action PMF exactly as a uniform/selected mixture, proves the
bounded-reward remaining-value envelope, and transports the Bellman gap to
the actual exploratory policy. The resulting per-policy charge is
`explorationRate*rewardBound*horizon*(horizon+1)`.

The same charge lifts to cumulative expected regret once per round and to
average expected regret once per window. These are successor source policies
at coordinates `1..rounds`, centered on summaries through coordinates
`0..rounds-1`; the initial-table behavior at coordinate zero is excluded and a
compiled `policyAt` alignment theorem records this. The vanishing-delta source endpoint
names exploratory-behavior violation trajectories, contains them in the same
measurable cumulative-count bad event, inherits its outer-measure bound, and
retains optimism. For fixed positive exploration, the deterministic behavior
certificate tends to the charge rather than zero.

The compatible decaying-exploration schedule and support/calibration consumer
now compile downstream. The next narrow route is an explicit common-space
coupling or martingale transport toward realized regret. Do not claim zero behavior consistency at fixed exploration,
violation-set measurability, one-process convergence, stochastic rewards,
minimax UCB-VI, or complete UCB-VI.

## RL Vanishing-Delta High-Probability Average Consistency Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtHighProbabilityAverageConsistency`.
It chooses `delta_n=1/(n+2)`, `rounds=n+1`, and the existing explicit scheduled
batch size. Positivity and `delta_n<=1` feed the parent source theorem, while
the parent's delta-independent inverse-root envelope makes the varying-delta
average recommendation certificate tend to zero.

The module also proves `ENNReal.ofReal delta_n -> 0` and joint convergence of
the failure budget and certificate. Its named regret-violation set is included
in the measurable cumulative-count bad event and has outer measure at most
`delta_n`; its own measurability is not claimed. An all-window theorem accepts dependent Standard Borel witnesses
for every changing batch and trajectory type.

Both the fixed-rate exploratory-behavior transport and its compatible
decaying-exploration support/calibration consumer now compile. The remaining
route must define and justify a common sample-space embedding or a
realized-regret martingale transport. Do not infer pathwise,
in-probability, almost-sure, or anytime consistency from the dependent family;
do not claim stochastic rewards, realized regret, minimax UCB-VI, or complete
UCB-VI.

## RL Scheduled Average Consistency Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtAverageConsistency`. It sets
episodes per batch to
`ceil(max(normalizedThreshold,2*L/visitFloor))+1`, proves strict normalized
calibration and `L<episodes*visitFloor/2`, and bounds the scheduled average
recommendation guarantee by
`16*card(State)*horizon^2/(sqrt(visitFloor)*sqrt(rounds))`.

The envelope and scheduled scalar bound tend to zero along positive rounds.
For each finite window, the source theorem preserves the existing measurable
event, delta tail, optimism, and recommended-policy semantics. The source
statement remains finite-window because changing episodes changes the batch
trajectory type.

The downstream decaying-confidence family, fixed-exploration behavior transport,
and compatible decaying-exploration support/calibration consumer now compile.
The downstream finite-window realized-regret martingale transport now compiles.
Its normalized-radius dependent realized consistency consumer also compiles.
The next narrow route is an explicit common-space embedding if fixed-process
pathwise, in-probability, or almost-sure consistency is desired, or a separate
sharper within-batch concentration proof. Do not infer those stronger modes,
stochastic rewards, minimax UCB-VI, or complete UCB-VI from this scalar parent.

## RL Average Cumulative Inverse-Sqrt Rate Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtAverageRate`. It names the total
exploratory episode count `episodes*rounds`, divides the cumulative
recommended-policy expected regret and its normalized scalar bound by positive
`rounds`, and proves the exact total-sample expansion
`2*horizon * min 1
  (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor) /
    sqrt((episodes*rounds)*visitFloor/2))`.

The terminal preserves the normalized route's measurable event, delta tail,
and roundwise optimism without reopening any conditional law or martingale
proof. A three-round Unit witness uses 1000 episodes per batch, total count
3000, `delta=1/2`, and visit floor one.

The downstream explicit Nat schedule and scalar consistency theorem now
compile. Keep that scalar recommendation guarantee separate from exploratory
behavior, realized regret, stochastic reward estimation, one-process
convergence, minimax rates, and complete UCB-VI.

## RL Normalized Cumulative Inverse-Sqrt Rate Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtNormalizedRate`. Under normalized
deterministic rewards, it fixes budget one and chooses
`4*card(State)*horizon*sqrt(L)/sqrt(visitFloor)` as the statistical scale.
The single episode threshold
`32*card(State)^2*horizon^2*L/visitFloor^2 < episodes` implies both prior
explicit-rate calibration premises.

The final endpoint preserves the same event and tail and removes caller-visible
budget/scale parameters. Its recommendation-regret sum is bounded by
`2*horizon * min rounds
  (8*card(State)*horizon*sqrt(L)/sqrt(visitFloor)*sqrt(rounds) /
    sqrt(episodes*visitFloor/2))`.
A three-round Unit witness at `delta=1/2` and 1000 episodes compiles through the
full source terminal.

The downstream average-rate and explicit Nat-schedule modules now perform the
positive-round division, total-episode rewrite, calibration, and scalar
consistency proof. Keep those recommendation statements separate from
fixed-process convergence, behavior regret, realized regret, stochastic reward
estimation, and a complete UCB-VI theorem.

## RL Explicit Cumulative Inverse-Sqrt Rate Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtExplicitRate`. With
`L = log(2/localDelta)` and
`C = 2*card(State)*horizon*(rewardBound+budget)`, the module constructs the full
two-scale calibration from
`max (2*L/visitFloor^2) (2*C^2*L/(budget^2*visitFloor^2)) < episodes`
and `C^2*L <= scale^2*visitFloor`.

The same derivation proves every prefix lower margin exceeds half its
predictable visit floor. It sums the capped envelopes and replaces the
terminal's abstract finite sum by
`2*horizon * min (rounds*budget)
  (2*scale*sqrt(rounds)/sqrt(episodes*visitFloor/2))`.
The measurable event, delta allocation, optimism statement, and
recommended-policy expected-regret semantics are unchanged.

The downstream normalized route now fixes reward bound and budget to one,
chooses an admissible scale, and replaces both scalar premises by one episode
threshold. Do not identify either recommendation theorem with exploratory
behavior or realized online regret.

## RL Cumulative Inverse-Sqrt Calibration Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeInverseSqrtCalibration`. The concrete planner
radius is `budget` at zero counts and
`min budget (scale/sqrt(count))` afterward. The zero-count cap and statistical
decay scale are separate nonnegative parameters.
Exploratory path support supplies a uniform predictable visit floor for the
initial and every adaptive successor policy; the compiled cumulative
martingale event converts its prefix sum into a strict realized-count lower
margin.

One deterministic roundwise `CumulativeInverseSqrtPathCalibration`, with
separate cap and inverse-sqrt cover inequalities, now constructs the previously
abstract martingale cover and the selected-radius envelope. The concrete
endpoint returns the same measurable `delta` event,
roundwise optimism, and recommended-policy expected regret bounded by the
finite capped inverse-square-root envelope sum. A positive Unit-MDP canary
instantiates the full route with horizon one, 100 episodes, `budget = 1`, and
`scale = 3`.

The former one-scale design was rejected after independent review: tying the
zero-count value cap to the inverse-sqrt numerator makes even the zero-reward
Unit case asymptotically incompatible with the current two-sided tail. The
downstream explicit-rate module now derives a closed-form sufficient two-scale
condition and simplifies the finite envelope sum. Keep that rate statement
separate from stochastic rewards, exploratory behavior regret, realized
regret, minimax tuning, and complete UCB-VI.

## RL Cumulative Count-Martingale Confidence Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeCountMartingaleConfidence`. Adaptive visit and
joint-transition batch counts use their exact within-batch Bernoulli MGF,
measurable kernel-integral centers, the generated next-batch conditional law,
and `Filtration.piLE`. Fixed-prefix two-sided tails use the cumulative variance
proxy; a single finite round-coordinate union supplies one global `delta` event.

Outside that event, the cumulative empirical transition singleton error is
bounded by `2*confidenceRadius/visitCount` for positive realized visits and by
one at zero visits. Under the explicit deterministic
`AdaptiveCumulativeCountMartingaleCover`, this produces every round's
`CoordinateConfidence`, the existing global contract, optimism, and the
recommended-policy expected-regret terminal. The concrete exploratory source
has a direct endpoint with the same contracts.

The downstream inverse-square-root path-support route now calibrates a concrete
nonnegative antitone capped radius, constructs the finite next-state cover, and
derives a round-indexed selected-radius envelope. Its downstream explicit-rate
consumer now constructs the calibration and finite-sum bound; parameter tuning
is the next step. Keep this separate from
behavior/realized regret, stochastic rewards, minimax tuning, and complete
UCB-VI.

## RL Cumulative Count-Radius Update

The project now compiles
`FiniteHorizonAdaptiveCumulativeEmpiricalOptimisticRegret`. The adaptive
planner sums transition counts from every batch in the observed prefix,
normalizes those cumulative rows, chooses a count-radius optimistic table, and
uses that measurable table to generate the next exploratory iid batch. Prefix
extension, visit-count monotonicity, count-antitone radius shrinkage, the exact
selected radius, and a recursive value envelope at `radius 0` all compile.

The new global contract terminal keeps the statistical boundary explicit: one
measurable event and roundwise cumulative `CoordinateConfidence` witnesses
imply recommendation optimism and expected recommendation regret bounded by
`sum round, horizon * (2 * radiusEnvelope round)`. A Unit horizon-one canary
computes cumulative counts `1,2` and linear-decay radii `3,2`.

The downstream count-martingale route now builds that probability producer and
the empirical coordinate-confidence adapter. Its explicit deterministic cover
is the remaining calibration boundary: choose a concrete antitone radius and
prove a square-root/log selected-radius envelope before attempting a rate.
Keep recommended, exploratory behavior, and realized regret distinct;
stochastic rewards, minimax tuning, and complete UCB-VI remain later routes.

## RL Fixed-Bonus Occupancy Envelope Update

The project now compiles
`adaptiveEmpiricalOptimisticOccupancyRadiusSum_eq` and
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_explicitRecommendedExpectedRegret_of_pathSupport_episodeThreshold`.
Probability occupancy evaluates a constant cost exactly. Since the current
known-reward empirical optimistic plan uses reward radius zero and one fixed
transition bonus, the complete radius sum is
`rounds * (horizon * (2 * transitionBonus))`.

The existing path-support episode-threshold event therefore gives the explicit
recommended-policy expected-regret bound
`rounds * (horizon * (2 * rewardBound))` with no new failure event or delta
allocation. The Bool horizon-two, two-round, bonus-one canary evaluates this
bound to `8`.

This is deliberately not called a statistical rate: the fixed bonus cannot
shrink with more data. The downstream cumulative count-radius route now
provides the cross-round state, measurable planner/source, and decreasing
envelope consumer, and its adaptive cumulative concentration producer now
compiles. Concrete deterministic count-radius cover calibration and a summable
envelope are the open boundary. Stochastic rewards, behavior/realized regret,
arbitrary-MDP support, minimax analysis, and complete UCB-VI remain separate.

## RL Episode-Threshold Calibration Update

The project now compiles
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_episodeThreshold`.
With `q = 4*card(State)*horizon+1`, one explicit threshold
`q^2*log(2/localCoordinateDelta)/(2*visitFloor^2) < episodes` implies both the
strict common count margin and the prior finite-state/horizon half contraction.
The result constructs a positive reward-bound cover and `SourceCalibration`
before invoking the unchanged global terminal.

The Bool-state/Bool-action horizon-two canary computes `q=17`, local coordinate
delta `1/96`, and threshold `9248*log(192)`. The elementary bound
`log(192)<191` proves that `2^22` episodes exceed the threshold; the new route
then supplies margin, contraction, bonus-one cover, calibration, and endpoint.

The downstream fixed-bonus occupancy envelope now evaluates the abstract RHS
exactly. Next replace the fixed bonus by a radius driven by accumulated
cross-round statistics and prove its shrinking sum. Stochastic rewards,
exploratory behavior/realized regret, arbitrary-MDP support, and complete UCB-VI
remain separate.

## RL Explicit Count/Bonus Calibration Update

The project now compiles
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_explicitCalibration`.
One uniform state-action visit floor supplies every expected-count denominator.
The scalar radius `2*r/(episodes*visitFloor-r)` bounds all transition
coordinates, and the finite-state/horizon condition
`card(State)*uniformRadius*horizon <= 1/2` makes
`transitionBonus = rewardBound` a sufficient source-wide cover.

A Bool-state/Bool-action horizon-two canary uses visit floor `1/8`, `2^22`
episodes, and local delta `1/4`. It proves count radius below `30000`, uniform
transition radius at most `1/8`, the exact half contraction, positive source
cover with bonus one, full `SourceCalibration`, and the final global terminal.

The downstream episode-threshold route solves the symbolic square-root/log
condition, and the fixed-bonus envelope now evaluates the selected
occupancy-radius sum exactly. A genuine rate still needs accumulated statistics
and a shrinking bonus. Stochastic rewards, exploratory behavior/realized
regret, and complete UCB-VI remain separate.

## RL Explicit Path-Support Reachability Update

The project now compiles
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport`.
Callers provide true initial and transition singleton floors plus one selected
predecessor state/action for every positive-stage target. Lean recursively
constructs a policy-independent state envelope, proves it for every exploratory
table selected by the adaptive source, and invokes the prior calibration and
global-event theorem without an abstract `SourceStateReachability` premise.

A Bool-state/Bool-action horizon-two canary uses a uniform initial law and
deterministic `nextState = action` transitions. It proves floors `1/2` at stage
zero and `1/4` at stage one, source-wide reachability, a strict 16384-episode
count margin, zero bonus cover, full `SourceCalibration`, and the final terminal.

The downstream explicit calibration route now constructs a nonzero transition
bonus cover from a common visit floor and finite-state/horizon contraction, and
the episode-threshold route now discharges those scalar conditions. An
occupancy-radius regret rate is still missing. The current theorem still bounds
recommended optimistic-policy expected regret, not exploratory behavior or
realized regret.

## RL Exploratory Reachability Calibration Update

The project now compiles
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_stateReachability`.
The theorem replaces the former opaque `SourceCalibration` argument by three
explicit contracts: one state-only probability lower envelope shared by all
batch-generating policies, a strict local-delta count-radius inequality below
`episodes * stateLower * explorationRate/card(Action)`, and the unchanged
transition-bonus cover.

The route includes the ENNReal-to-Real action-floor bridge, exact visit and
expected-count lower bounds, policy/source calibration constructors, and the
terminal global-event consumer. A Bool-action source distinguishes an initial
false-centered mass `1/4` from successor true-centered mass `3/4`; a separate
concrete two-round Unit source checks the numeric margin, cover, calibration,
and full terminal.

The explicit path-support producer now compiles downstream. The remaining work
is to turn its recursive floor into reusable episode thresholds and discharge
the bonus-cover contract. This theorem still concerns recommended optimistic-
policy expected regret, not exploratory behavior or realized regret.

## RL Stage-Visit Factorization Update

The project now compiles
`stageVisitProbability_eq_stageStateProbability_mul_action`. The underlying
remaining-trace theorem uses a chronological coordinate map, proves the head
case from the generated action/state kernel, and carries the fixed action mass
through every earlier `compProd` layer. The full trajectory theorem then
integrates over the probability initial-state law.

A two-stage Bool-action canary gives true-action visit probability `0` at stage
zero and `1/2` at stage one, identifies remaining coordinate one with the
second chronological stage, and directly instantiates the recursive theorem
there. This is an
exact population identity, including zero-state-mass coordinates. Next prove a
narrow state-reachability-to-visit-margin consumer by multiplying an explicit
state-mass lower bound with the exploratory action floor; do not infer state
reachability or complete UCB-VI from factorization alone.

## RL Adaptive Exploratory Empirical-Optimistic Confidence Update

The project now compiles
`exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret`.
The behavior source uniformly explores around every latest optimistic table;
each action receives at least `explorationRate / card Action` mass. Its one
global count event produces coordinate confidence and true-MDP optimism for
every observed known-reward empirical plan.

`SourceCalibration` keeps the remaining statistical assumptions explicit for
every exploratory behavior policy: state-action expected-visit margins and a
coordinate-radius/value-envelope sum covered by the nonnegative fixed bonus.
The route bounds the finite sum of the optimistic policies recommended by the
batches, not the regret of the exploratory behavior policy itself.

Next derive state reachability and bonus calibration from an explicit schedule
or accumulated-count construction and turn the occupancy-radius sum into a
rate. Behavior-policy/realized regret, stochastic rewards, and complete UCB-VI
remain downstream.

## RL Adaptive Empirical-Optimistic Source Update

The project now compiles
`AdaptiveEmpiricalOptimisticSource.source_trajectoryMeasure_adaptiveSimultaneousCountConfidence`.
Observed batches are converted measurably into transition-count summaries,
normalized empirical transition kernels, known-reward/fixed-bonus optimistic
plans, and deterministic action tables. Table-indexed generated iid laws are
assembled with `Kernel.ofFunOfCountable` and comapped along the latest-batch
selector, so the resulting `AdaptiveEpisodeBatchSource` carries its exact law
by construction.

The same route exposes the latest empirical optimistic policy as the next
batch's regular conditional law and discharges selected count-event
measurability by a finite policy-table decomposition. External Bool
state/action canaries cover a genuine `3/4` versus `1/4` empirical row,
zero-count fallback, opposite transition summaries, and distinct selected
optimistic policies.

The downstream exploratory known-reward route now compiles under explicit
state-reachability/bonus calibration and bounds the expected regret of the
recommended optimistic policies. The source still uses only the latest batch
and does not establish exploratory behavior or realized cumulative UCB-VI
regret.

## RL Adaptive Episode-Batch Count Confidence Update

The project now compiles
`AdaptiveEpisodeBatchSource.trajectoryMeasure_adaptiveSimultaneousCountConfidence`.
An adaptive source may choose a different Markov policy from every finite batch
prefix, provided its history-indexed Markov kernel is exactly that policy's
generated iid batch law and the selected-policy count event is measurable.
The resulting Ionescu--Tulcea trajectory has one global-delta finite-horizon
count-confidence event without an independence premise.

The same module exposes the exact initial marginal, prefix `compProd`
recurrence, and selected-policy next-batch regular conditional law. The latter
has the explicit `StandardBorelSpace (EpisodeBatch mdp episodes)` contract;
the count-confidence endpoint only needs the Markov source law and event
measurability.

The concrete known-reward/latest-batch empirical-transition optimistic source
now compiles. Next transport adaptive reward consistency and calibrated
all-coordinate model confidence to that source, then extend the selector from
latest-batch to accumulated statistics. Only after those laws compile should
the route attack cumulative bonus rates or realized UCB-VI regret.

## RL IID Multibatch Cumulative Confidence Update

The project now compiles
`MarkovPolicy.iidEpisodeBatchFamily_allCoordinate_optimism_and_cumulativeExpectedRegret`.
For any positive finite number of independent fixed-policy training batches,
one product-space event of mass at most `delta` simultaneously supplies a full
confidence witness and global optimism for every batch-derived empirical model.
The sum of their optimistic-policy expected regrets is bounded by the finite sum
of the existing selected-radius occupancy terms.

The probability proof uses exact `Measure.pi` coordinate marginals, local
budget `delta / rounds`, finite-union normalization, and a.e. reward-support
pullback. It does not introduce a measurable selection of confidence data.

The next RL theorem route should replace the offline product by an adaptive
episode-history law in which later data and policies are generated from earlier
history, then prove a cumulative selected-radius/bonus rate. The current result
must not be called realized cumulative regret or complete UCB-VI.

## RL All-Coordinate Finite-Batch Confidence Update

The project now compiles
`MarkovPolicy.iidEpisodeBatch_allCoordinate_finiteBatchModel_confidence` and
`MarkovPolicy.iidEpisodeBatch_allCoordinate_optimism_and_expectedRegret`.
For one fixed policy and iid generated episode batch, a single simultaneous
count event controls every planning coordinate. Exact deterministic rewards,
the genuine positive lower count margin, a fixed transition budget, and an
explicit finite coordinate cover produce a complete empirical-model confidence
witness almost everywhere with the same global-delta failure bound.

The construction is noncircular: transition coordinate radii depend only on
expected counts and the shared count radius, while recursive optimistic values
use the separate linear envelope
`remaining * (rewardBound + transitionBudget)`. The immediate consumer gives
global optimism and a one-episode occupancy-form expected-regret bound.

The next RL route should introduce episode-indexed policy updates and sum the
selected radii/bonuses under an explicit adaptive data contract. Do not present
the current fixed-policy batch theorem as cumulative, anytime, minimax, or
complete UCB-VI regret.

## Explicit-Policy Canonical UCB Update

The project now compiles
`UCB.canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero_and_explicitPolicy`.
On the fresh canonical `Kernel.trajMeasure` process, the successor-action
conditional law is the deterministic kernel induced by
`realHistoryNextArm hK (c * sigma2)` almost everywhere on each finite-history
marginal. A single full-measure event records the initialization action and
all successor selector equalities, and the terminal retains the `c=4`
armwise-bounded expected-average convergence theorem on that same process.

The reward half now compiles as well: adaptive next-unused-coordinate branch
assembly identifies the reward conditional law with `nu action`, and complete
trajectory transport exposes that law on the fresh canonical process. Literal
LML import remains a separate toolchain boundary.

## Canonical-Kernel Recursive UCB Update

The project now compiles
`UCB.canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero`.
Canonical arm-stream split conditional laws are packaged as a
`Thompson.HistoryAlgorithm` and `Thompson.HistoryEnvironment`, then Mathlib
`Kernel.trajMeasure` independently regenerates the observable pair process.
Its coordinate action/reward traces satisfy every field of
`RealStationaryUCBSequence` and inherit the exact `c=4` armwise-bounded
logarithmic expected-regret envelope and vanishing `n+1` average.

The concrete theorem exposes only positive finite arms, per-arm probability
laws, and arm-dependent a.s. intervals. It exposes no sample space, traces,
conditional laws, means, MGFs, proxy ceiling, or trajectory law. The explicit
action-policy identification now compiles downstream; the stationary
selected-`nu` reward-kernel identification is the remaining narrow source
route. Literal LML import remains a separate toolchain boundary.

## Measure-Preserving External UCB Source Update

The project now compiles
`UCB.productNoiseArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero`.
A generic producer pulls the canonical UCB action/reward process through any
`MeasurePreserving source mu (armStreamMeasure nu)` and constructs every field
of `RealStationaryUCBSequence`. The concrete endpoint takes the first
projection from `ArmRewardStream K x Aux` under the product of the canonical
stream law with any auxiliary probability measure. Thus a genuinely different
external sample space may carry independent nuisance randomness without any
caller-supplied split conditional laws, action/reward traces, or trajectory
law.

The conditional-law proof transports the conditioning and joint pair maps
with Mathlib `Measure.map_map` and `MeasurePreserving.map_eq`, rewrites the
canonical joint law with `compProd_map_condDistrib`, and applies `condDistrib`
uniqueness. Armwise-bounded Real laws then inherit the exact `c=4`
nonnegative logarithmic expected-regret envelope and vanishing `n+1` average.
The downstream canonical-kernel trajectory now supplies a non-reparameterized
recursive generator. Explicit policy/environment kernel identification or a
compatible literal LML import remains. Independent review found no P0-P2, and the full
gate passed with root build 3483 jobs, Tests build 3485 jobs, and 14 CLI tests
with one skipped.

## External Stationary Armwise-Bounded UCB Consistency Update

The project now compiles
`UCB.realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero`.
For one fixed finite external measure and one fixed action/reward process, a
`RealStationaryUCBSequence` bundle identifies every finite-horizon expected
regret integral exactly with the canonical `c=4` arm-stream integral. The
external expected regret therefore inherits the same nonnegative logarithmic
envelope and vanishing `n+1` average from armwise-bounded Real arm laws.

The proof projects the bundle's complete observable trajectory law to the
action trace and applies Mathlib `IdentDistrib.integral_eq` to the measurable
regret functional. It does not add a horizon-indexed process, common interval,
caller mean/MGF/proxy ceiling, preassembled trajectory law, latent unused-arm
stream, or separate integrability premise. A measure-preserving external
product-source producer and a fresh canonical-kernel trajectory now consume
this theorem; explicit deterministic-policy/stationary-reward identification
or compatible literal LML import remains. Two independent review passes found no
P0-P2 issue and confirmed the exact scale, law, integral, instance,
fixed-process semantics, and complete declaration retrieval.

## Armwise-Bounded Real Arm-Law One-Policy Update

The project now compiles
`UCB.armStreamArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero`.
Every Real arm law keeps its own almost-sure interval and Hoeffding proxy; the
finite maximum is padded only for the common UCB tuning parameter. The proof
does not replace arm-dependent support by a common interval.

The kernel, identity-integral means, proxy family, recursive action, and
product measure are fixed across all horizons. The exact expected regret is
nonnegative, bounded by a fixed model coefficient times `1+log(n+1)`, and its
`n+1` normalization tends to zero. No caller mean, MGF, common bound, proxy
ceiling/positivity, default arm, horizon, delta, measurability, integrability,
or pointwise `lo arm < hi arm` is required. Zero-width arm intervals are valid;
an inverted interval makes that arm's probability support premise inconsistent.
Independent review found no P0-P2 issue and confirmed the exact armwise proxy,
fixed-policy, and fixed-measure semantics. Its external
`RealStationaryUCBSequence` expected-consistency consumer and its
measure-preserving product-source producer now compile.

## Bounded Real Arm-Law One-Policy Update

The project now compiles
`UCB.armStreamBoundedFiniteArmExpectedAverageRegret_tendsto_zero`. From a
positive finite arm count, one Real probability law per arm, and common a.s.
interval support, it internally constructs the countable-domain Markov kernel,
uses each law's identity integral as its arm mean, derives bounded centered
sub-Gaussian MGFs, and pads the finite maximum proxy to make UCB tuning
strictly positive.

The resulting theorem uses one fixed recursive `armStreamAction` and one fixed
`armStreamMeasure` for all horizons. Its expected `realKernelRegret` is
nonnegative, has a fixed coefficient times `1+log(n+1)` envelope, and divided
by `n+1` tends to zero. Callers provide no model mean, direct MGF, proxy
ceiling/positivity, default action, horizon, delta, integrability, or `lo<hi`.
Zero-width intervals are valid; if `lo>hi`, the probability support premise is
inconsistent for the nonempty arm family. The downstream armwise theorem now
removes the common-interval restriction. A concrete external sequence producer
and stronger probability modes remain separate.

## One-Policy Arm-Stream Expected Consistency Update

The project now compiles
`UCB.armStreamExpectedAverageRegret_tendsto_zero`. Unlike the sampled-successor
asymptotic family, this theorem uses the same recursive `armStreamAction` at
scale `4 * sigma2` and the same product `armStreamMeasure nu` for every horizon.
The exact expected `realKernelRegret` is nonnegative, `O(log(n+1))`,
`o(n+1)`, and its quotient by `n+1` tends to zero.

The supporting route identifies `indexTail 4` with a cubic NNReal p-series,
uniformly bounds `constSum 4 n` by one fixed tsum, transports that bound through
`ENNReal.toReal`, and assembles a finite-arm kernel coefficient without assuming
all gaps are positive. The public contract is `0<K`, a Markov Real arm kernel,
a nonzero common sub-Gaussian proxy, and centered MGF witnesses for every arm.
It does not prove pathwise, in-probability, almost-sure/Hannan, minimax, or
literal upstream-LML results. Common-bounded Real arm laws now instantiate this
fixed canonical process downstream.

## Armwise-Bounded Explicit Expected-Regret Update

The project now compiles
`UCB.selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedPseudoRegret_nonneg_and_le`.
For every horizon with `2*K <= T+1`, stationary finite-arm probability laws
with arm-dependent a.s. support and exact model means satisfy nonnegativity and
the explicit envelope
`selectedPolicySuccessorAsymptoticModelCoefficient model paddedProxy *
(1 + Real.log (T+1))`. A supporting direct-sub-Gaussian producer constructs
the practical pair measure, kernel law, and padded finite-arm proxy internally.

The public theorem needs neither a separate `0<T` nor pointwise
`lo arm < hi arm`: `model.hK` and the large-horizon premise imply positivity
of `T`; the bounded-MGF source accepts zero-width support, and proxy padding
separately supplies the positive UCB tuning parameter. Inverted intervals make
the probability-support premise inconsistent. The
result preserves sampled `(trajectory (t+1)).1` actions and
`delta_T=1/(T+1)` on a horizon-indexed policy/measure family. The separate
canonical arm-stream route now closes shared-measure one-policy expected
consistency; this practical sampled theorem itself remains horizon-indexed and
makes no pathwise, almost-sure/Hannan, minimax, or complete-UCB claim.

## Armwise-Bounded Finite-Arm Expected Consistency Update

The project now compiles
`UCB.selectedPolicySuccessorArmwiseBoundedFiniteArmExpectedAveragePseudoRegret_tendsto_zero`.
Stationary finite-arm probability laws may use separate support intervals
`Set.Icc (lo arm) (hi arm)`. The existing armwise bounded centered-kernel
producer supplies the exact Hoeffding MGF at each arm, and the practical
sampled parent proves the exact expected pseudo-regret is `O(log(T+1))`; its
`T+1` normalization tends to zero.

The public boundary has no common interval, direct MGF, pair law, centered
law, common ceiling, positivity, integrability, horizon, or delta premise. It
also needs no pointwise `lo arm < hi arm`: the bounded-MGF source accepts
zero-width support, while the direct parent pads the finite maximum genuine
proxy before UCB tuning. Inverted intervals make the probability-support
premise inconsistent. The endpoint still concerns the
sampled `(trajectory (t+1)).1` observable under a horizon-indexed
`delta_T=1/(T+1)` policy/measure family, not one-policy anytime, pathwise,
probability, almost-sure/Hannan, minimax, or complete-UCB consistency.

## Common-Bounded Finite-Arm Expected Consistency Update

The project now compiles
`UCB.selectedPolicySuccessorBoundedFiniteArmExpectedAveragePseudoRegret_tendsto_zero`.
For stationary finite-arm probability laws with a.e. measurable rewards,
common a.s. support in `Set.Icc lo hi`, and exact model means, it constructs
the centered Hoeffding MGF witnesses and proves the exact sampled-pair expected
pseudo-regret is `O(log(T+1))`; its `T+1` normalization tends to zero.

The route preserves the sampled successor action `(trajectory (t+1)).1`, the
fixed-action initial pair pushforward, and the horizon-indexed
`delta_T=1/(T+1)` family inherited from the direct-sub-Gaussian parent. It
does not require `lo < hi`: the parent pads the genuine finite-arm proxy by
one before using it as the positive UCB parameter. Direct MGF, pair-law,
centered-kernel, common-ceiling, positivity, integrability, horizon, and delta
premises are absent from the public boundary. The arm-dependent interval
consumer now compiles downstream.

## Practical Finite-Arm Expected Consistency Update

The project now compiles
`UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret_tendsto_zero`.
It instantiates the canonical sampled pair-trajectory asymptotic theorem from
stationary finite-arm probability laws, exact arm means, and direct centered
sub-Gaussian MGF witnesses.

The route pushes the default arm reward law forward by
`reward |-> (defaultAction,reward)` for pair coordinate zero, uses the
context-independent successor kernel, packages the centered law internally,
and chooses the finite arm maximum proxy padded by one. Thus no initial pair
law, centered-kernel law, measurable context/mean, common proxy ceiling,
proxy-positivity witness, horizon, or delta remains at the public boundary.
The exact sampled-successor expected family is `O(log(T+1))`, hence its
normalization by `T+1` tends to zero.

This is still a fixed-model horizon-indexed family with
`delta_T=1/(T+1)`, not one horizon-independent policy, anytime control,
pathwise/probability/almost-sure consistency, minimax regret, or the complete
UCB theorem. Both common-interval and armwise-interval bounded-law consumers
now derive the direct MGF witnesses downstream.

## Canonical Sampled-Successor Expected Consistency Update

The project now compiles
`UCB.selectedPolicySuccessorActionRewardTrajMeasureExpectedAveragePseudoRegret_tendsto_zero`.
For each horizon `T`, the canonical pair UCB policy uses
`delta_T = 1 / (T + 1)`, and the exact expected pseudo-regret observes sampled
successor actions `(trajectory (t + 1)).1`.

The route rewrites the finite-arm/time peeling argument to a polynomial,
proves its log budget is eventually at most `4*log(T+1)`, and bounds every
positive-gap 32/4/2 plus failure contribution by a fixed model coefficient
times `1+log(T+1)`. The named exact expected family is therefore
`O(log(T+1))`, hence `o(T+1)`, and its normalization tends to zero.

The asymptotic theorem requires one horizon-independent variance ceiling for
all contexts and arms so every member of the horizon-indexed policy family can
instantiate the parent fixed-horizon theorem. This is expected convergence of
a horizon-indexed family, not one-policy anytime control, pathwise or
in-probability convergence, almost-sure/Hannan consistency, minimax regret, or
a complete UCB theorem.

## Canonical Sampled-Successor Pseudo-Regret Update

The project now compiles
`UCB.integral_real_pseudoRegret_actionRewardTrajectorySuccessorAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel`.
The Real textbook pseudo-regret observable is stated directly on sampled pair
actions `actionRewardTrajectorySuccessorAction trajectory t =
(trajectory (t + 1)).1`.

The supporting a.e. theorem packages the canonical per-time sampled/policy
action law over every natural time with `ae_all_iff` and `funext`. The final
proof uses `integral_congr_ae` to transport the compiled reward-generated
action theorem on the same pair measure. This is deliberately not pointwise,
and coordinate zero is not charged. The explicit `32/4/2 + gap*(T*delta)`
Real RHS and all parent contracts, including variance only for `i < T - 1`,
are unchanged. Its fixed-model expected-average consistency consumer now
compiles above; anytime confidence and a complete UCB theorem remain separate.

## Canonical Pair-Trajectory Real/Bochner Update

The project now compiles
`UCB.integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel`.
It is the direct Real expectation consumer of the canonical action/reward pair
`trajMeasure` theorem below; it does not transport through the distinct
reward-only trajectory measure.

The wrapper derives finite-horizon pseudo-regret integrability internally,
uses pointwise gap nonnegativity to identify `ofReal (integral regret)` with
the compiled lintegral, and normalizes the finite ENNReal bound to the explicit
positive-gap Real sum. Its public RHS has no `ENNReal.toReal` and contains the
same `32/4/2` textbook budget plus `gap * (T * delta)`. The centered-kernel,
stationary-mean, positive-parameter, and horizon-local `i < T - 1` variance
contracts are unchanged. Its sampled-successor coordinate presentation now
compiles above; asymptotic normalization, anytime confidence, and a complete
UCB theorem remain separate.

## Canonical Generated-UCB Textbook Gap-Sum Update

The project now compiles
`UCB.lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel`.
It is the canonical pair-trajectory counterpart of the existing selected-law
textbook theorem and directly consumes the preceding canonical explicit
pseudo-regret endpoint.

The result filters to positive model gaps and replaces each gap-weighted
integer threshold by the named `32/4/2` textbook budget, while preserving the
`gap * T * ofReal(delta)` term. Its probability, variance, mean, and kernel-law
contracts are unchanged; there is no new selected-law/range or all-arm
positivity premise. Its canonical pair-surface finite-RHS Real/Bochner
consumer and sampled-successor presentation now compile above. Asymptotic
`O(log T)` normalization and expected-average consistency now compile in the
latest update; anytime confidence and complete UCB remain independent routes.

## Canonical Generated-UCB Pseudo-Regret Update

The project now compiles
`UCB.lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_actionRewardTrajMeasure_centeredKernel`.
This is the first concrete finite-arm pseudo-regret endpoint on the canonical
action/reward pair `trajMeasure`: the generated successor action at `t + 1`
is shifted to pseudo-regret coordinate `t`, and the prior per-arm expected
count theorem is summed only over arms with positive model gap.

Zero-gap arms vanish inside the generic finite-sum consumer. The conclusion is
the exact ENNReal sum of gap times the explicit integer pull threshold plus
gap times `T * ofReal(delta)`. The endpoint retains the horizon-local
`i < T - 1` variance contract and needs no caller score source,
selected-reward law, ranges, separate ambient/process integrability premise,
all-arm positivity, or delta upper bound. `CenteredRewardKernelLaw` still
contains its pointwise selected-law integrability and sub-Gaussian fields. The
textbook reciprocal-gap simplification now compiles above. The next narrow
consumer is the finite-RHS ENNReal-to-Real expectation wrapper; it must not be
conflated with anytime or asymptotic UCB regret.

## Canonical Generated-UCB Expected-Count Update

The project now compiles both the explicit-threshold chosen-arm pull-count tail
and
`UCB.lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_actionRewardTrajMeasure_centeredKernel`
on the canonical pair `trajMeasure`. For a positive-gap chosen arm, the ENNReal
expected successor count is bounded by the explicit integer threshold plus
`T * ENNReal.ofReal delta`.

This endpoint consumes the concrete generated large-gap event without a caller
law/source/range or integrability premise. The exact successor convention is
preserved: the observable is evaluated at `T + 1`, while only the `T` charged
successor indices enter the deterministic count ceiling and failure term. The
finite-arm positive-gap summation now compiles in the update above. The
remaining narrow presentation route is an ENNReal-to-Real expectation
conversion; it does not imply an anytime result.

## Concrete Pair-Trajectory UCB Update

The project now compiles
`UCB.measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel`.
It specializes the canonical action/reward history-step `trajMeasure` to the
finite-history generated UCB policy, constructs the concrete initialized
score-max source internally, and proves its strict random-width large-gap event
has mass at most `ENNReal.ofReal delta`.

The key transport is deliberately a.e.: sampled pair successor actions agree
with reward-history generated actions under the canonical trajectory measure,
then the shifted action functions identify the generated and sampled pull
counts, reward sums, empirical means, and confidence radii. The theorem keeps
the horizon-local `i < T - 1` variance contract and needs no caller source,
selected law, reward/mean ranges, or all-time variance. Its chosen-arm
expected-count, finite-arm explicit-threshold, and textbook gap-sum
pseudo-regret consumers now compile above. Real/Bochner presentation,
sampled-coordinate form, anytime confidence, and asymptotic normalization
remain separate.

## Conditional-Law Route Update

The conditional-reward/UCB route now compiles the canonical pair-trajectory
random-width large-gap theorem
`UCB.measure_actionRewardHistoryStepKernelFamily_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_trajMeasure`.
It consumes the compiled simultaneous finite-arm/time empirical-mean event and
the existing initialized score-max source over the sampled pair coordinates.

Any strict selected gap larger than twice the realized-count radius must lie in
the named simultaneous confidence failure, so the canonical `trajMeasure`
assigns it mass at most `ENNReal.ofReal delta`. Only the variance ceiling
through `i < T - 1` and stationary means on candidate arms are required. No
raw/mean range, external conditional law, event measurability, or all-time
variance premise is present. The concrete canonical generated-policy source
and its a.e. event transport now compile in the preceding update; this generic
source-explicit theorem remains reusable. Uniform-time confidence, expected
pull counts, and regret remain downstream.

## Current Route Update

The power-of-two forced route now compiles through
`OFUL-SCHEDULED-GENERATED-TRAJECTORY-POWER-OF-TWO-FORCED-HIGH-PROBABILITY-AVERAGE-PSEUDOREGRET-CONSISTENCY`.
It uses one horizon-independent policy and canonical measure, derives the
all-time confidence tail from the linear sub-Gaussian environment law, names
the exact scalar budget with its logarithmic forced-action charge, and proves
fixed-model growth `O(sqrt (horizon + 1) * log (horizon + 1))`. The exact
budget is now also compiled as `o(horizon + 1)`, its quotient tends to zero,
and complete pseudo-regret per round is bounded by that quotient outside the
unchanged fixed-`delta` violation event. The endpoint squeezes that normalized
regret to zero pathwise outside the event, defines the exact consistency-failure
set, proves its inclusion in the event, and inherits the same outer-measure
bound under the unchanged policy and canonical measure.

The fixed-confidence power-of-two route remains closed. The subsequently
selected route
`EXP3-DOUBLE-VARIANCE-SPARSE-BEST-ARM-EVENTUAL-REFINED-TAIL` now also compiles:
fixed model parameters eventually satisfy the four exact sparse EXP3 schedule
conditions, the best-arm threshold is definitionally rewritten to
`16 * gamma_T * T`, and the off-bad, residual, and practical outer-measure
tails are transported without changing their internally selected rates,
kernel, failure event, or horizon-indexed generated measure. This is not one
single-policy anytime control, convergence, or expected regret. The next run
should select one new unfinished theorem route from the refreshed index.

## Purpose

ABRL is the target-faithful autoformalization harness behind the Lean 4
BanditRLlib library. Its paper is titled *ABRL: A Target-Faithful
Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement
Learning Theory*. It is a proof
library plus a plain-file multi-agent harness for formalizing bandit and
reinforcement-learning theory.

The intended pipeline is:

```text
literature theorem or new proof target
-> theorem card and assumption ledger
-> exact Lean-facing statement
-> small proof-DAG leaves
-> compiled Lean certificate
-> synchronized Markdown and LaTeX explanation
-> reusable memory for the next theorem
```

The main rule is that natural-language sketches, source cards, theorem cards,
and proof weapons are not completed proofs.  A result becomes certified local
memory only after the relevant Lean declarations compile through the repository
gate:

```bash
python3 tools/bandit.py check
```

That gate is intended to run:

```bash
lake build
lake build Tests
```

and then scan for placeholders such as `sorry`, `admit`, `axiom`, and
`postulate`.

## Current Local Reality

The current local checkout is an early proof-engineering skeleton, not a
complete textbook-scale bandit/RL theorem library.

Already present:

- a Lean package with Mathlib pinned through Lake;
- core finite-bandit vocabulary;
- recursive definitions for pull counts, reward sums, finite-arm mean models,
  gaps, and pseudo-regret;
- compiled best-arm dominance and model-gap nonnegativity invariants for the
  local finite-bandit model;
- a first set of compiled finite-bookkeeping leaves;
- Mathlib-backed `Finset.range` wrappers for pull counts, selected reward
  sums, and pseudo-regret;
- a deterministic regret decomposition into an arm-indexed sum of
  `gap * pullCount`;
- deterministic Rat/Nat count-bound-to-regret scaffolds;
- Bochner and ENNReal expectation/pull-count/regret bridge leaves;
- measure, finite-history, history-filtration finite-pair/comap alignment,
  policy-measurability,
  reward-kernel, finite-prefix `partialTraj`, and conditional-expectation
  bridge surfaces;
- independent and strongly adapted conditional sub-Gaussian tail wrappers;
- a deterministic finite-action EXP3 potential surface with exponential-weight
  updates, nonnegativity, one-step increment algebra, and finite-horizon
  telescoping;
- a deterministic full-information exponential-weights/Hedge theorem with a
  second-order comparator bound and the `[0,1]` endpoint
  `log |A| / eta + eta*T`;
- a generic finite-action FTRL one-step minimizer wrapper over an explicit
  feasible predicate or finite-simplex predicate;
- a finite-simplex Tsallis power-sum/entropy/negative-entropy regularizer
  surface with `Real.rpow` and denominator well-definedness facts;
- a finite-horizon regularized be-the-leader theorem and Tsallis-FTRL
  comparator-regret decomposition exposing the exact stability sum plus
  `((powerSum p_0-powerSum q)/(1-alpha))/eta`;
- the deterministic Tsallis importance-weighted inverse-Hessian power moment:
  its sampled-coordinate identity, exact sampling-mass-weighted finite sum
  `sum_a loss(a)^2*p(a)^(1-alpha)`, and `[0,1]` power-sum upper bound;
- local exact/stationary final theorem routes for Explore-Then-Commit, UCB, and
  Thompson sampling, with literal upstream LML imports kept separate;
- task packets, proof obligations, conversion windows, research cards, and run
  logs.

Still missing or only carded:

- polished textbook-facing expectation APIs beyond the compiled bridge leaves;
- ambient trajectory-to-`condExpKernel` law identification, full adaptive
  policy predictability, posterior kernels, and full conditional-expectation
  contracts;
- Hoeffding/Chernoff and theorem-specific martingale tail instantiations
  beyond the compiled sub-Gaussian and Chebyshev/variance wrappers;
- optional-stopping/resource-feasibility/BwK routes beyond the compiled
  budget-exhaustion hitting-time wrapper;
- literal cross-toolchain imports of the upstream LML UCB/ETC/Thompson symbols
  and broader nonstationary/contextual adapters beyond the compiled local
  theorem routes;
- complete EXP3 bandit regret, the Hessian/KKT stability and remaining
  Tsallis-INF/FTRL route, OFUL/LinUCB, BwK, or
  finite-horizon RL theorem proofs;
- proof exports for closed textbook theorems.

The requested unfinished-work workflow is now available:

- `python3 tools/bandit.py unfinished` lists unfinished proof leaves and backlog
  rows.
- `docs/collaborator_unfinished_work_guide.md` explains the one-leaf workflow.
- `PULLCOUNT-LIST-RANGE`, `SUMREWARDS-LIST-RANGE`,
  `SUMREWARDS-LIST-FILTER`, and `PSEUDOREGRET-LIST-RANGE` are compiled local
  dependency-light bridges after the Lean gate passes.
- `PULLCOUNT-FINSET` is compiled locally as
  `pullCount_eq_finset_filter_card` in `BanditRLProof.MathlibWrappers`.
- `SUMREWARDS-FINSET` is compiled locally as
  `sumRewards_eq_finset_filter_sum` in `BanditRLProof.MathlibWrappers`.
- `PSEUDOREGRET-FINSET` is compiled locally as
  `pseudoRegret_eq_finset_sum` in `BanditRLProof.MathlibWrappers`.
- `ETC-EXPLOREARM-EQ-IFF-MOD` is compiled locally as
  `ETC.exploreArm_eq_iff_mod_eq_val` in `BanditRLProof.Algorithms.ETC`.
- `REGRET-PULLCOUNT` is compiled locally as
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount` in
  `BanditRLProof.RegretDecomposition`.
- `REGRET-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_finset_sum_gap_mul_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `REGRET-NAT-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `REGRET-UNIFORM-NAT-COUNT-BOUND` is compiled locally as
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` in
  `BanditRLProof.RegretCountBounds`.
- `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_K_eq_one` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-ADD-K-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_add_K_eq_add_one` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-MUL-K-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` is compiled locally as
  `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- `ETC-EXPLORATION-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` is compiled
  locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_exploreArm_of_lt` in
  `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_commitArm_of_ge` in
  `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` is compiled locally as
  `ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le`
  in `BanditRLProof.Algorithms.ETCTrace`.
- `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` is compiled locally as
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm` in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` is compiled locally as
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap`
  in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `PULLCOUNT-SUM-TIME` is compiled locally as
  `finset_sum_pullCount_eq_time` in
  `BanditRLProof.PullCountDecomposition`.
- `MEAS-FIN-ACTION` is compiled locally as
  `measurableSet_actionTrace_eval_eq` in
  `BanditRLProof.MeasureFoundation`.
- `MEAS-PULL-INDICATOR` is compiled locally as
  `measurable_actionTrace_eval_eq_indicator_const` in
  `BanditRLProof.MeasureFoundation`.
- `MEAS-REWARD` is compiled locally as
  `measurable_actionTrace_eval_eq_indicator_reward` in
  `BanditRLProof.MeasureFoundation`.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource`,
  a source-projection wrapper exposing the packaged practical base
  raw-range/measurable-mean-range bounded source from a uniform-variance
  source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the explicit
  generated random-pair map source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  is compiled locally as
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`,
  a source-consumer wrapper lowering the packaged uniform-variance source
  through its generated random-pair map source into the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the weaker
  definitional generated actual-action reward-coordinate source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the explicit
  generated actual-action reward-map source.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the definitional
  centered-source interface.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its base raw-range/measurable-mean-range source into the bounded
  centered-source interface.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged uniform-variance source
  through its bounded centered-source projection into the integrability-based
  centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource`,
  a source-projection wrapper exposing the packaged practical base
  raw-range/measurable-mean-range bounded source from a selected-history
  variance source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  explicit generated random-pair map source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  generated full finite-pair `partialTraj` source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  is compiled locally as
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`,
  a source-consumer wrapper lowering the packaged selected-history-variance
  source through its generated random-pair map source into the canonical
  history-step next-pair law.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  weaker definitional generated actual-action reward-coordinate source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  explicit generated actual-action reward-map source.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  bounded centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its bounded centered-source projection into the
  integrability-based centered-source interface.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  is compiled locally as
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`,
  a source-conversion wrapper lowering the packaged selected-history-variance
  source through its base raw-range/measurable-mean-range source into the
  definitional centered-source interface.
- `MEAS-HISTORY` is compiled locally as finite action/reward history product
  objects, trace-restriction maps, and coordinate measurability over
  `Finset.Iic` prefixes in `BanditRLProof.HistoryFiltration`; it now also
  exposes pair-coordinate finite trace prefixes and measurable reward
  projection from finite `(Action, Reward)` pair histories, plus the
  measurable successor-extension map for appending one next pair.
- `MEAS-SELECTED-REWARD-FINITE-SUM` is compiled locally as
  `measurable_finset_sum_indicator_reward` in
  `BanditRLProof.MeasurableSums`.
- `MEAS-SUMREWARDS` is compiled locally as
  `measurable_sumRewards` in
  `BanditRLProof.MeasurableLocalQuantities`.
- `MEAS-REGRET` is compiled locally as
  `measurable_pseudoRegret` in
  `BanditRLProof.MeasurableRegret`.
- `MEAS-PULLCOUNT` is compiled locally as
  `measurable_pullCount` in
  `BanditRLProof.MeasurablePullCount`.
- `MEAS-PULLCOUNT-CAST` is compiled locally as
  `measurable_natCast_pullCount` in
  `BanditRLProof.MeasurablePullCountCast`.
- `INT-FINITE-SUM` is compiled locally as
  `IntegrabilitySums.integrable_finset_sum` and
  `IntegrabilitySums.integrable_univ_sum` in
  `BanditRLProof.IntegrabilitySums`.
- `EXP-FINITE-SUM` is compiled locally as
  `ExpectationBochnerSums.integral_finset_sum` and
  `ExpectationBochnerSums.integral_univ_sum` in
  `BanditRLProof.ExpectationBochnerSums`.
- `EXP-REGRET-PULLCOUNT` is compiled locally as
  `integrable_real_pseudoRegret_of_integrable_pullCount` and
  `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount` in
  `BanditRLProof.ExpectationRegretPullCount`; this is the Real-valued Bochner
  decomposition, not a Rat-valued expectation theorem or final algorithmic
  regret theorem.
- `EXP-INDICATOR-PULL` is compiled locally as
  `lintegral_actionTrace_eval_eq_indicator_one` in
  `BanditRLProof.ExpectationFoundation`.
- `EXP-FINSET-INDICATOR-PULL` is compiled locally as
  `lintegral_finset_sum_actionTrace_eval_eq_indicator_one` in
  `BanditRLProof.ExpectationSums`.
- `EXP-PULLCOUNT-LINTEGRAL` is compiled locally as
  `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq` in
  `BanditRLProof.ExpectationPullCount`.
- `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` is compiled locally as
  `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` in
  `BanditRLProof.ExpectationWeightedPullCount`.
- `EXP-PULLCOUNT-LE-TIME` is compiled locally as
  `lintegral_natCast_pullCount_le_time` in
  `BanditRLProof.ExpectationPullCountBounds`.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME` is compiled locally as
  `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` in
  `BanditRLProof.ExpectationWeightedPullCountBounds`.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` is compiled locally as
  `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` in
  `BanditRLProof.ExpectationFiniteBanditBounds`.
- `EXP-MODEL-GAP-OFREAL-BOUND` is compiled locally as
  `lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`
  in `BanditRLProof.ExpectationFiniteBanditModelBounds`.
- `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` is compiled locally as
  `ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg` in
  `BanditRLProof.ScalarENNReal`.
- `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is compiled locally as
  `ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`
  in `BanditRLProof.ScalarPseudoRegret`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`
  in `BanditRLProof.ExpectationPseudoRegretOfRealBounds`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`
  in `BanditRLProof.ExpectationPseudoRegretRatBounds`.
- `FINITE-BANDIT-GAP-BESTARM` is compiled locally as
  `FiniteBanditModel.gap_bestArm` in `BanditRLProof.Core`.
- `FINITE-BANDIT-BESTARM-DOMINATES` is compiled locally as
  `FiniteBanditModel.mean_le_bestArm_mean` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `FINITE-BANDIT-GAP-NONNEG` is compiled locally as
  `FiniteBanditModel.gap_nonneg` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
  `FINITE-BANDIT-MAXGAP-NONNEG` are compiled locally as
  `FiniteBanditModel.maxGap`, `FiniteBanditModel.gap_le_maxGap`, and
  `FiniteBanditModel.maxGap_nonneg` in
  `BanditRLProof.FiniteBanditModelInvariants`.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` is compiled locally as
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time`
  in `BanditRLProof.ExpectationPseudoRegretRatBounds`.

## Main Content Structure

### Lean Library

- `BanditRLProof/Core.lean`: core finite-bandit vocabulary.
  - `ActionTrace`
  - `RewardTrace`
  - `pullCount`
  - `sumRewards`
  - `FiniteBanditModel`
  - `bestArm`
  - `bestMean`
  - `gap`
  - `FiniteBanditModel.gap_bestArm`
  - `PolicySketch`
  - `CertificateStatus`

- `BanditRLProof/FiniteBanditModelInvariants.lean`: model-semantic
  invariants for the local finite-bandit selector.
  - `FiniteBanditModel.mean_le_bestArm_mean`
  - `FiniteBanditModel.gap_nonneg`
  - `FiniteBanditModel.maxGap`
  - `FiniteBanditModel.gap_le_maxGap`
  - `FiniteBanditModel.maxGap_nonneg`

- `BanditRLProof/Regret.lean`: regret-facing surfaces.
  - `pseudoRegret`
  - `RegretBoundCard`
  - `RegretObligation`

- `BanditRLProof/LeafLemmas.lean`: currently compiled dependency-light leaves.
  - pull-count update lemmas;
  - pull-count monotonicity and upper bounds;
  - zero/count segment lemmas;
  - reward-sum segment lemmas;
  - pseudo-regret zero and segment-stability lemmas.

- `BanditRLProof/MathlibWrappers.lean`: first Mathlib interop layer.
  - `pullCount_eq_finset_filter_card`;
  - `sumRewards_eq_finset_filter_sum`;
  - `pseudoRegret_eq_finset_sum`;
  - imports `Mathlib.Data.Finset.Card`;
  - imports `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and
    `Mathlib.Algebra.Field.Rat` for `Finset.sum` over `Rat`;
  - uses `Finset.range_add_one`, `Finset.filter_insert`, and
    `Finset.sum_range_succ`.

- `BanditRLProof/RegretDecomposition.lean`: deterministic regret consumer
  leaves.
  - `pseudoRegret_eq_finset_sum_gap_mul_pullCount`;
  - imports `Mathlib.Data.Fintype.Basic` and `Mathlib.Data.Nat.Cast.Basic`;
  - uses `Finset.sum_fiberwise'`, `Finset.sum_const`, and `nsmul_eq_mul'`.

- `BanditRLProof/RegretCountBounds.lean`: deterministic count-bound-to-regret
  scaffolds.
  - `pseudoRegret_le_finset_sum_gap_mul_count_bound`;
  - `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`;
  - `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`;
  - imports ordered finite-sum and ordered Rat APIs;
  - uses `pseudoRegret_eq_finset_sum_gap_mul_pullCount`,
    `FiniteBanditModel.gap_nonneg`, `Finset.sum_le_sum`, and
    `mul_le_mul_of_nonneg_left`.

- `BanditRLProof/PullCountDecomposition.lean`: deterministic finite-action
  count partition leaves.
  - `finset_sum_pullCount_eq_time`;
  - imports `Mathlib.Data.Fintype.Basic`;
  - uses `pullCount_eq_finset_filter_card` and
    `Finset.card_eq_sum_card_fiberwise`.

- `BanditRLProof/MeasureFoundation.lean`: first probability-facing
  measurability canaries.
  - `measurableSet_actionTrace_eval_eq`;
  - `measurable_actionTrace_eval_eq_indicator_const`;
  - `measurable_actionTrace_eval_eq_indicator_reward`;
  - imports `Mathlib.MeasureTheory.MeasurableSpace.Basic`;
  - uses `MeasurableSet.singleton`, measurable preimages,
    `measurable_const`, reward-evaluation measurability hypotheses, and
    `Measurable.indicator`.

- `BanditRLProof/MeasurableSums.lean`: finite-sum measurability bridge for
  selected-reward indicator contributions.
  - `measurable_finset_sum_indicator_reward`;
  - imports `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `Finset.induction_on`, `Finset.sum_insert`, and `Measurable.add`.

- `BanditRLProof/MeasurableLocalQuantities.lean`: measurability bridge from
  selected-reward finite sums to local recursive quantities.
  - `measurable_sumRewards`;
  - imports `Mathlib.Algebra.BigOperators.Group.Finset.Indicator`;
  - uses `sumRewards_eq_finset_filter_sum`,
    `Finset.sum_indicator_eq_sum_filter`, and
    `measurable_finset_sum_indicator_reward`.

- `BanditRLProof/MeasurableRegret.lean`: pseudo-regret random-variable
  measurability bridge before expectation.
  - `measurable_pseudoRegret`;
  - imports `Mathlib.Data.Fintype.Basic` and
    `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `measurable_of_finite`, `Measurable.comp`, finite-set induction, and
    `pseudoRegret_eq_finset_sum`.

- `BanditRLProof/MeasurablePullCount.lean`: pull-count random-variable
  measurability bridge before expected pull-count identities.
  - `measurable_pullCount`;
  - imports `Mathlib.MeasureTheory.Group.Arithmetic`;
  - uses `measurableSet_actionTrace_eval_eq`, `Measurable.ite`,
    `Measurable.add`, and `pullCount_succ`.

- `BanditRLProof/MeasurablePullCountCast.lean`: scalar-casted pull-count
  measurability bridge before expected pull-count identities.
  - `measurable_natCast_pullCount`;
  - imports `Mathlib.Data.Nat.Cast.Basic`;
  - uses scalar induction, `Measurable.ite`, `Measurable.add`, and
    `pullCount_succ`.

- `BanditRLProof/ExpectationFoundation.lean`: first lower-integral canary for
  action-event indicators.
  - `lintegral_actionTrace_eval_eq_indicator_one`;
  - imports `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`;
  - uses `MeasureTheory.lintegral_indicator_one` and
    `measurableSet_actionTrace_eval_eq`.

- `BanditRLProof/ExpectationSums.lean`: lower-integral finite-sum bridge for
  action-event indicators.
  - `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`;
  - imports `Mathlib.MeasureTheory.Integral.Lebesgue.Add`;
  - uses `MeasureTheory.lintegral_finset_sum`,
    `measurable_actionTrace_eval_eq_indicator_const`, and
    `lintegral_actionTrace_eval_eq_indicator_one`.

- `BanditRLProof/ExpectationPullCount.lean`: lower-integral pull-count identity.
  - `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`;
  - imports `Mathlib.Data.Nat.Cast.Basic`;
  - uses `pullCount_succ`, `Finset.sum_range_succ`, and
    `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`.

- `BanditRLProof/ExpectationRegretPullCount.lean`: Bochner/Real expected-regret
  decomposition into finite gap-weighted expected pull counts.
  - `integrable_real_pseudoRegret_of_integrable_pullCount`;
  - `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount`;
  - imports `Mathlib.MeasureTheory.Integral.Bochner.Basic`,
    `BanditRLProof.ExpectationBochnerSums`, and
    `BanditRLProof.RegretDecomposition`;
  - uses the deterministic `pseudoRegret_eq_finset_sum_gap_mul_pullCount`,
    `ExpectationBochnerSums.integral_univ_sum`, `Integrable.const_mul`, and
    `MeasureTheory.integral_const_mul`.

- `BanditRLProof/ConditionalExpectationReward.lean`: narrow
  `condExpKernel`-to-`condExp` zero bridge and explicit history-step
  integral/map-law consumers for centered reward variables.
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero`;
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq`;
  - `ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`;
  - `ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen`;
  - `ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet`;
  - `ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable`;
  - `ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable`;
  - `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen`;
  - `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc`;
  - `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - `RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk`;
  - `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq`;
  - `Policy.generatedActionTraceSucc`;
  - `Policy.generatedActionTraceSucc_succ_eq`;
  - `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`;
  - `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc`;
  - `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`;
  - `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`;
  - `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq`;
  - `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq`;
  - `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`;
  - imports `Mathlib.Probability.Independence.Conditional` and
    `BanditRLProof.RewardKernel`;
  - uses `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel` and
    `MeasureTheory.ae_eq_of_ae_eq_trim`, plus
    `RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero`
    and Mathlib `integral_map`, `condExpKernel_ae_eq_trim_condExp`,
    `condExp_of_stronglyMeasurable`, `ae_all_iff`, and
    `mem_ae_iff_prob_eq_one`, plus `measurable_pi_lambda`,
    `History.measurable_reward_mem_historyFiltration_of_lt`,
    `History.measurable_action_mem_historyFiltration_of_lt`, and
    `Measure.map_congr` plus
    `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply`
    and `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`;
    it consumes but does not construct the trajectory-law conditional-kernel
    identification.

- `BanditRLProof/Algorithms/ETC.lean`: Explore-Then-Commit interface and
  obligation names.

- `BanditRLProof/Algorithms/ETCTrace.lean`: fixed-commit ETC phase-switching
  trace boundary for exploration and commit phases.

- `BanditRLProof/Algorithms/ETCTraceCountLemmas.lean`: deterministic
  pull-count transfer facts for the fixed-commit ETC trace.

- `BanditRLProof/Algorithms/UCB.lean`: UCB interface, index-state surface, and
  obligation names.

- `BanditRLProof/Algorithms/Thompson.lean`: Thompson sampling and Bayesian
  regret obligation names, a posterior-action identity ledger, and a compiled
  Mathlib `condDistrib` transport theorem for the probability-matching route.

- `BanditRLProof/Algorithms/ThompsonCanonicalSampler.lean`: canonical
  prior-likelihood-posterior one-step sampler, marginal transports, and a
  premise-free Thompson probability-matching theorem.

- `BanditRLProof/Algorithms/ThompsonReferencePolicy.lean`: fixed-reference
  posterior policy, `compProd` action sampler, posterior-preservation transport,
  and finite action/reward-prefix probability matching from posterior
  invariance.

- `BanditRLProof/Algorithms/ThompsonAlgorithmDensity.lean`: common-history
  density law source, base-density/`compProd` commutation, posterior invariance,
  and generic plus finite-prefix reference-policy probability matching from
  marginal/joint change-of-algorithm laws.

- `BanditRLProof/Algorithms/ThompsonBayesRegretDecomposition.lean`:
  measurable history/action score interface, conditional-law score-expectation
  transport, initial best-action marginal identification, and the exact
  finite-horizon Bayesian mean-regret decomposition on the actual recursive
  uniform-reference Thompson trajectory.

- `BanditRLProof/Algorithms/ThompsonClippedUCBScore.lean`: the pinned LML
  zero-pull/clipped empirical-mean score on finite pair histories, measurable
  `[l,u]` bounds, history-to-trace transport, automatic score/mean
  integrability, and the concrete actual-trajectory Bayesian-regret
  decomposition.

- `BanditRLProof/Algorithms/ThompsonStationaryReward.lean`: measurable
  stationary reward-kernel sampling into an independent latent arm stream,
  arbitrary-action adaptive-count sub-Gaussian tails, and deterministic
  next-unused feedback for the Thompson trajectory transport route.

- `BanditRLProof/RL/FiniteHorizonMDP.lean`: the first Mathlib-backed RL layer:
  finite state/action MDP data, a Markov transition kernel, measurable Real
  reward, measurable one-step continuation values, and the Bellman action-value
  operator. Policy evaluation and its finite generated-trajectory value
  identity now compile downstream; optimality, occupancy, and regret remain.

- `BanditRLProof/RL/FiniteHorizonPolicy.lean`: stage-indexed Markov action
  kernels, policy-induced state kernels, the measurable policy Bellman
  operator, backward policy evaluation, terminal value, and the chronological
  theorem `MarkovPolicy.valueAt_bellman`.

- `BanditRLProof/RL/FiniteHorizonTrajectory.lean`: finite vectors of sampled
  `(action,nextState)` steps, recursively generated Markov trajectory kernels,
  measurable and automatically integrable cumulative reward, the statewise
  return/value induction, and the initial-law theorem equating expected return
  with `policy.valueAt 0`.

- `BanditRLProof/RL/FiniteHorizonOptimality.lean`: finite Bellman-Q argmax,
  measurable deterministic greedy kernels on finite discrete states, backward
  optimal value, universal Markov-policy dominance, and an attaining policy.
  The next RL route is occupancy/value-difference/regret; optimism and UCB-VI
  are not implied by policy optimality alone.

- `BanditRLProof/Literature.lean`: LML theorem-card registry.

- `BanditRLProof/Automation.lean`: harness/task/gate types.

- `BanditRLProof/OpenProblems.lean`: open problem registry.

### Workflow And Memory

- `tasks/`: task packets such as `BRL-UCB-PORT-001`,
  `BRL-ETC-PORT-001`, `BRL-TS-BAYES-001`, and
  `BRL-OP-RL-BELLMAN-001`.
- `proof-obligations/`: task-local leaf ledgers.
- `conversion-windows/`: mappings between paper/theorem-card prose and local
  Lean surfaces.
- `proof-blueprints/`: generated snapshots that combine task context,
  obligations, retrieval cards, and local declarations.
- `research-wiki/`: theorem cards, paper cards, Mathlib routes, proof
  techniques, scenario taxonomy, and open problems.
- `runs/`: prompt decks, run logs, handoff notes, and trial summaries.
- `tools/bandit.py`: plain-file CLI for task creation, memory refresh,
  blueprint refresh, retrieval, declaration search, proof export, run-cycle
  prompt generation, and checks.

## Why Not Start With A Broad Theorem

Broad goals such as "prove UCB regret", "formalize Tsallis-INF", or "build the
RL Bellman theory" currently depend on many missing layers at once:

- finite-sum bridges;
- probability and measure theory imports;
- measurability and integrability contracts;
- concentration inequalities;
- algorithm-specific algebra;
- final regret decomposition.

Starting there would likely produce more planning prose instead of a compiled
Lean result.  The repository's own design says lower work should target exactly
one small unfinished leaf at a time.

## Recommended Next Step

The deterministic dependency-light baseline is now closed:

```text
PULLCOUNT-LIST-RANGE       compiled-local
SUMREWARDS-LIST-RANGE      compiled-local
SUMREWARDS-LIST-FILTER     compiled-local
PSEUDOREGRET-LIST-RANGE    compiled-local
ETC-EXPLOREARM-ADD-K       compiled-local
ETC-EXPLOREARM-EQ-IFF-MOD  compiled-local
PULLCOUNT-FINSET           compiled-local
SUMREWARDS-FINSET          compiled-local
PSEUDOREGRET-FINSET        compiled-local
REGRET-PULLCOUNT           compiled-local
REGRET-COUNT-BOUND         compiled-local
REGRET-NAT-COUNT-BOUND     compiled-local
REGRET-UNIFORM-NAT-COUNT-BOUND compiled-local
ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT compiled-local
ETC-ROUND-ROBIN-ADD-K-COUNT compiled-local
ETC-ROUND-ROBIN-MUL-K-COUNT compiled-local
ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT compiled-local
ETC-EXPLORATION-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-COMMIT-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT compiled-local
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT compiled-local
ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET compiled-local
ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND compiled-local
ETC-WRONG-COMMIT-PROBABILITY-DESIGN theorem-card-only
ETC-MEAS-COMMITARM-NE-BESTARM compiled-local
ETC-MEAS-EMPMEAN-GE-EMPMEAN compiled-local
ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM compiled-local
ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT compiled-local
ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET compiled-local
ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL compiled-local
ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL compiled-local
ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL compiled-local
ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET compiled-local
ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL compiled-local
ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND compiled-local
ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS compiled-local
ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS compiled-local
ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND compiled-local
ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE compiled-local
ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND compiled-local
ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND compiled-local
ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND compiled-local
ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT compiled-local
ETC-BOUNDED-REWARD-INFINITEPI-SOURCE compiled-local
ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE compiled-local
ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND compiled-local
ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE compiled-local
ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY compiled-local
ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER compiled-local
PULLCOUNT-SUM-TIME         compiled-local
MEAS-FIN-ACTION            compiled-local
MEAS-PULL-INDICATOR        compiled-local
MEAS-REWARD                compiled-local
MEAS-HISTORY               compiled-local
MEAS-SELECTED-REWARD-FINITE-SUM compiled-local
MEAS-SUMREWARDS            compiled-local
MEAS-REGRET                compiled-local
MEAS-PULLCOUNT             compiled-local
MEAS-PULLCOUNT-CAST        compiled-local
EXP-INDICATOR-PULL         compiled-local
EXP-FINSET-INDICATOR-PULL  compiled-local
EXP-PULLCOUNT-LINTEGRAL    compiled-local
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL compiled-local
EXP-PULLCOUNT-LE-TIME      compiled-local
EXP-WEIGHTED-PULLCOUNT-LE-TIME compiled-local
EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN compiled-local
EXP-MODEL-GAP-OFREAL-BOUND compiled-local
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS compiled-local
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG compiled-local
FINITE-BANDIT-GAP-BESTARM compiled-local
FINITE-BANDIT-BESTARM-DOMINATES compiled-local
FINITE-BANDIT-GAP-NONNEG compiled-local
FINITE-BANDIT-MAXGAP compiled-local
FINITE-BANDIT-GAP-LE-MAXGAP compiled-local
FINITE-BANDIT-MAXGAP-NONNEG compiled-local
EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP compiled-local
```

The first deliberate Mathlib-backed wrappers, deterministic regret consumer,
deterministic count partition leaf, and measurable action-event/indicator
canaries are now closed:

```text
Leaf: PULLCOUNT-FINSET
Goal: connect recursive `pullCount` to a filtered `Finset.range` cardinality.
Status: compiled-local.

Leaf: PSEUDOREGRET-FINSET
Goal: connect recursive `pseudoRegret` to a `Finset.range` sum of selected gaps.
Status: compiled-local.

Leaf: SUMREWARDS-FINSET
Goal: connect recursive `sumRewards` to a filtered `Finset.range` sum.
Status: compiled-local.

Leaf: REGRET-PULLCOUNT
Goal: reindex pseudo-regret as an arm sum of `gap * pullCount`.
Status: compiled-local.

Leaf: REGRET-COUNT-BOUND
Goal: convert per-arm pull-count bounds into a gap-weighted pseudo-regret
upper bound.
Status: compiled-local.

Leaf: REGRET-NAT-COUNT-BOUND
Goal: convert Nat-valued per-arm pull-count bounds into the gap-weighted
pseudo-regret upper bound after casting budgets to Rat.
Status: compiled-local.

Leaf: REGRET-UNIFORM-NAT-COUNT-BOUND
Goal: convert a uniform Nat-valued pull-count bound into
`pseudoRegret <= (sum gaps) * B`.
Status: compiled-local.

Leaf: ETC-EXPLOREARM-EQ-IFF-MOD
Goal: characterize `ETC.exploreArm spec t = a` by the modular equality
`t % K = a.val`.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT
Goal: prove each arm is pulled exactly once in the first round-robin ETC
exploration cycle.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-ADD-K-COUNT
Goal: prove each full-cycle extension of the ETC round-robin exploration
prefix adds exactly one pull of each arm.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-MUL-K-COUNT
Goal: prove `m` full ETC round-robin exploration cycles pull each arm exactly
`m` times.
Status: compiled-local.

Leaf: ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT
Goal: specialize the multiple-cycle theorem to the configured ETC exploration
horizon `spec.explorationPulls * K`.
Status: compiled-local.

Leaf: ETC-EXPLORATION-REGRET-BOUND
Goal: bound the pure round-robin ETC exploration prefix pseudo-regret by
`(sum gaps) * spec.explorationPulls`.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND
Goal: bound the fixed-commit ETC trace pseudo-regret at the configured
exploration horizon by `(sum gaps) * spec.explorationPulls`.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE
Goal: define a fixed-commit ETC phase-switching trace and prove it agrees with
`ETC.exploreArm` throughout the configured exploration prefix.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-COMMIT-PHASE
Goal: prove the fixed-commit ETC phase-switching trace equals the supplied
commit arm after the configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE
Goal: prove the fixed-commit ETC phase-switching trace equals the selected
best arm after the configured exploration horizon when the supplied commit arm
is that selected best arm.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT
Goal: transfer pull counts from `ETC.actionWithCommit` to `ETC.exploreArm` on
any prefix contained in the configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT
Goal: specialize the fixed-commit ETC trace pull-count transfer to the
configured exploration horizon.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT
Goal: prove the one-step post-commit pull-count recurrence for the fixed-commit
ETC trace.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT
Goal: prove the closed-form post-exploration suffix pull count for the
fixed-commit ETC trace.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT
Goal: prove that every non-commit arm keeps its exploration-horizon pull count
after the fixed-commit ETC trace enters the commit phase.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT
Goal: prove that the commit arm has exploration-horizon count plus every
post-exploration suffix pull.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET
Goal: prove that, when the fixed commit arm is the selected best arm, the
post-exploration suffix adds no pseudo-regret.
Status: compiled-local.

Leaf: ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND
Goal: prove that, when the fixed commit arm is the selected best arm, any
post-exploration suffix horizon satisfies the exploration-horizon regret
budget.
Status: compiled-local.

Leaf: PULLCOUNT-SUM-TIME
Goal: prove finite-action pull counts sum to the time horizon.
Status: compiled-local.

Leaf: MEAS-FIN-ACTION
Goal: prove measurable action evaluations yield measurable equality events.
Status: compiled-local.

Leaf: MEAS-PULL-INDICATOR
Goal: prove measurable action-equality events yield measurable constant-valued
pull indicators.
Status: compiled-local.

Leaf: MEAS-REWARD
Goal: prove selected-reward action indicators are measurable without choosing an
expectation or scalar algebra route.
Status: compiled-local.

Leaf: MEAS-SELECTED-REWARD-FINITE-SUM
Goal: prove finite sums of selected-reward indicator contributions are
measurable without choosing an expectation route.
Status: compiled-local.

Leaf: MEAS-SUMREWARDS
Goal: prove local recursive selected-reward accumulators are measurable by
connecting `sumRewards` to the selected-reward finite-sum bridge.
Status: compiled-local.

Leaf: MEAS-REGRET
Goal: prove local pseudo-regret is a measurable random variable before choosing
an expectation or probability-measure route.
Status: compiled-local.

Leaf: MEAS-PULLCOUNT
Goal: prove local recursive pull counts are measurable before choosing an
expected pull-count or scalar-cast route.
Status: compiled-local.

Leaf: MEAS-PULLCOUNT-CAST
Goal: prove scalar-casted local pull counts are measurable before choosing an
expected pull-count route.
Status: compiled-local.

Leaf: EXP-INDICATOR-PULL
Goal: prove the `ENNReal` lower integral of an action-equality pull-event
indicator equals the measure of that event.
Status: compiled-local.

Leaf: EXP-FINSET-INDICATOR-PULL
Goal: prove the `ENNReal` lower integral of a finite sum of action-equality
pull-event indicators equals the finite sum of event measures.
Status: compiled-local.

Leaf: EXP-PULLCOUNT-LINTEGRAL
Goal: prove the `ENNReal` lower integral of scalar-casted recursive
`pullCount` equals the finite sum of action-event measures.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LINTEGRAL
Goal: prove the `ENNReal` lower integral of a finite weighted sum
`gap a * pullCount a n` equals the corresponding weighted finite sum of
action-event measures.
Status: compiled-local.

Leaf: EXP-PULLCOUNT-LE-TIME
Goal: under a probability measure, prove the `ENNReal` lower integral of a
scalar-casted recursive pull count is bounded by the horizon.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LE-TIME
Goal: under a probability measure, prove the `ENNReal` lower integral of a
finite weighted pull-count sum is bounded by the weighted horizon budget.
Status: compiled-local.

Leaf: EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN
Goal: specialize the weighted probability budget bound to
`(Finset.univ : Finset (Fin K))`.
Status: compiled-local.

Leaf: EXP-MODEL-GAP-OFREAL-BOUND
Goal: instantiate the finite-arm weighted budget bound with
`ENNReal.ofReal (((model.gap a : Rat) : Real))`.
Status: compiled-local.

Leaf: OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
Goal: under explicit nonnegativity of real weights, prove `ENNReal.ofReal`
commutes with finite weighted Nat-count sums.
Status: compiled-local.

Leaf: OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
Goal: under explicit nonnegativity of model gaps, prove pointwise Rat-valued
`pseudoRegret` has the same `ENNReal.ofReal` image as the finite-arm weighted
pull-count expression.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND
Goal: under explicit gap nonnegativity, bound the lower integral of
`ENNReal.ofReal` pseudo-regret by the model-gap horizon budget.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
Goal: expose the same lower-integral pseudo-regret bound with the natural
Rat-level gap nonnegativity contract.
Status: compiled-local.

Leaf: EXP-REGRET-PULLCOUNT
Goal: prove the Real-valued Bochner expected pseudo-regret identity
`E[pseudoRegret] = sum_a gap a * E[pullCount a]` under explicit per-arm
Real-cast pull-count integrability.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-BESTARM
Goal: expose the definitional fact that the selected best arm has zero local
model gap.
Status: compiled-local.

Leaf: FINITE-BANDIT-BESTARM-DOMINATES
Goal: prove every arm mean is at most the mean of the local model's selected
`bestArm`, as a prerequisite for deriving model-gap nonnegativity.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-NONNEG
Goal: prove every local `FiniteBanditModel.gap` value is Rat-nonnegative from
best-arm dominance and the local `gap` definition.
Status: compiled-local.

Leaf: FINITE-BANDIT-MAXGAP
Goal: expose the maximum local arm gap over the finite arm set as a deterministic
model constant.
Status: compiled-local.

Leaf: FINITE-BANDIT-GAP-LE-MAXGAP
Goal: prove every local `FiniteBanditModel.gap` value is bounded by
`FiniteBanditModel.maxGap`.
Status: compiled-local.

Leaf: FINITE-BANDIT-MAXGAP-NONNEG
Goal: prove the finite maximum gap is Rat-nonnegative.
Status: compiled-local.

Leaf: EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP
Goal: remove the explicit `hgap` argument from the `ENNReal.ofReal`
lower-integral pseudo-regret bound by using `FiniteBanditModel.gap_nonneg`.
Status: compiled-local.
```

Closed statement:

```lean
theorem pullCount_eq_finset_filter_card
    {Action : Type u} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a t =
      ((Finset.range t).filter fun s => action s = a).card := by
  -- induction on t
  -- use Finset.range_add_one and Finset.filter_insert
  -- split on action t = a
```

These support:

- ETC round-robin counts;
- UCB pull-count bounds;
- final algorithm regret theorems.

## Suggested Immediate Plan

1. Keep the local gate passing:

   ```bash
   python3 tools/bandit.py check
   ```

2. When route judgment is needed, run two local reviewer agents and record a
   combined local review artifact before choosing probability foundations or an
   algorithm-specific leaf.

3. Do not enter probability/concentration until measurable and integrable
   contracts are written as exact leaves.

4. After every compiled leaf, update:
   - `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
   - `docs/completion_gap_audit.md`;
   - relevant proof-obligation ledgers;
   - retrieval indexes through `python3 tools/bandit.py reference-index`.

5. Periodically run the local two-agent review workflow after a meaningful
   batch, for example after a route-card or compiled leaf changes the
   probability/concentration frontier.

Current ETC boundary:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` is compiled locally, and
  it implements the Extended Pro recommendation to choose Candidate B from
  `reports/extended_pro_after_commitarm_suffix_count_candidate_prompt_2026-06-29.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_commitarm_suffix_count_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` is compiled locally, and
  it implements the second Extended Pro recommendation to choose Candidate C
  from
  `reports/extended_pro_after_suffix_budget_regret_candidate_prompt_2026-06-30.md`.
- The second recorded reviewer response is
  `reports/extended_pro_after_suffix_budget_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` is compiled locally, and it
  implements the third Extended Pro recommendation from
  `reports/extended_pro_after_coarse_suffix_regret_candidate_prompt_2026-06-30.md`.
- The third recorded reviewer response is
  `reports/extended_pro_after_coarse_suffix_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` is compiled locally, and
  it implements the fourth Extended Pro recommendation from
  `reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`.
- The fourth recorded reviewer response is
  `reports/extended_pro_after_phase_split_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` is compiled locally, and it
  implements the Extended Pro recommendation from
  `reports/extended_pro_after_gap_bestarm_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_gap_bestarm_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` is compiled locally, and
  it implements the Extended Pro recommendation from
  `reports/extended_pro_after_bestarm_suffix_no_regret_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_bestarm_suffix_no_regret_response_2026-06-30.md`.
- `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` is compiled locally, and it
  implements the Extended Pro recommendation from
  `reports/extended_pro_after_bestarm_suffix_regret_bound_candidate_prompt_2026-06-30.md`.
- The recorded reviewer response is
  `reports/extended_pro_after_bestarm_suffix_regret_bound_response_2026-06-30.md`.
- Do not prove the generic constant-arm suffix lemma, simplify the
  suffix-budget RHS, add empirical means/commit argmax, or move into
  probability, concentration, filtration, conditional expectation, or final ETC
  theorem facts before another reviewer/Extended Pro decision.

## Question For Extended Pro

Please review this plan as a Lean/formal-methods proof-engineering strategy.

Context:

- This repository aims to formalize bandit/RL theory in Lean 4.
- Current local code has compiled dependency-light finite-prefix bridges for
  pull counts, reward sums, filtered reward sums, and pseudo-regret.
- `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and `PSEUDOREGRET-FINSET` now
  compile as Mathlib-backed wrappers.
- `REGRET-PULLCOUNT` now compiles as a deterministic consumer leaf.
- `PULLCOUNT-SUM-TIME` now compiles as a deterministic finite-action count
  partition leaf.
- `MEAS-FIN-ACTION` now compiles as the first probability/measure canary.
- `MEAS-PULL-INDICATOR` now compiles as the second probability/measure canary.
- `MEAS-REWARD` now compiles as the selected-reward indicator measurability
  canary.
- `MEAS-SELECTED-REWARD-FINITE-SUM` now compiles as a selected-reward finite-sum
  measurability bridge.
- `MEAS-SUMREWARDS` now compiles as a local recursive reward-sum measurability
  bridge.
- `MEAS-REGRET` now compiles as a local pseudo-regret random-variable
  measurability bridge.
- `MEAS-PULLCOUNT` now compiles as a local pull-count random-variable
  measurability bridge.
- `MEAS-PULLCOUNT-CAST` now compiles as a scalar-casted pull-count
  measurability bridge.
- `COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` now compiles as a narrow
  `condExpKernel`-to-ordinary-`condExp` zero bridge for arbitrary real
  variables and succ-indexed centered rewards; the broad `COND-EXPECT-REWARD`
  row remains open until the trajectory-law conditional-kernel identification
  and adaptive-policy assembly are supplied.
- `COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER` now compiles under
  explicit trim-a.e. law/integral-equality hypotheses, using the history-step
  centered-reward zero integral to feed the existing `condExpKernel` bridge;
  the broad `COND-EXPECT-REWARD` route remains open because the equality
  hypotheses are not yet constructed from `partialTraj`.
- `COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER` now compiles
  under explicit reward-coordinate pushforward equality and frozen-past
  a.e. hypotheses, reducing that structural law-identification interface to
  the existing integral consumer through Mathlib `integral_map`; the broad
  route remains open until those hypotheses are proved from the trajectory law.
- `COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED` now compiles as a deterministic
  bridge from a finite-history frozen-past hypothesis to the centered-target
  a.e. equality required by the map-law consumer; the broad route remains open
  until the history frozen-past theorem and `condExpKernel` trajectory-law
  identification are proved.
- `COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL` now compiles as the
  conditional-kernel frozen-past route: conditioning-measurable events have
  0/1 real mass under the conditional kernel, countable-valued
  conditioning-measurable variables are frozen under that kernel, and finite
  reward histories measurable at `F i` are frozen under
  `condExpKernel mu (F i)`.  The route is now fed by the concrete
  finite-history measurability hookup below; trajectory reward-law
  identification remains open.
- `COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP` now compiles as the
  concrete finite reward-history measurability hookup: coordinate
  measurability at `F i` yields frozen finite histories, and the generated
  `History.historyFiltrationSucc` specialization supplies those coordinates
  from the local history filtration.  The broad route still needs the
  `partialTraj`/history-to-`condExpKernel` reward-law identification and
  final adaptive theorem assembly.
- `COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP` now compiles as the
  finite action/reward pair-history frozen-past hookup under
  `[Countable Action]`: coordinate measurability at `F i` freezes the whole
  `History.finitePairHistoryOfTrace`, and the generated
  `History.historyFiltrationSucc` specialization supplies both action and
  reward coordinate measurability.  This supports the future pair-law
  identification; it does not prove the `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP` now compiles as the
  successor-extension bridge for pair traces: `History.extendPairHistorySucc`
  appends one `(Action, Reward)` pair to a finite pair prefix, the actual
  `i + 1` trace prefix decomposes through it, and under generated
  `History.historyFiltrationSucc`/`condExpKernel` the random extended trace is
  a.e. the frozen old prefix extended by the random next pair.  This is still
  structural support, not the full joint `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP` now compiles as the
  succ-indexed map-law consumer with the frozen-past side condition discharged
  from finite-history coordinate measurability, plus a generated
  `History.historyFiltrationSucc` specialization.  The broad route still
  needs the reward-coordinate pushforward identity from `condExpKernel` to
  `RewardKernel.historyStepKernelFamily`, i.e. the trajectory reward-law
  identification.
- `COND-EXPECT-REWARD-PAIR-MAP-CONSUMER` now compiles as the pair-law route
  into the map-law consumer: a `condExpKernel` next-step `(Action × Reward)`
  pushforward identity into `RewardKernel.actionRewardHistoryStepKernelFamily`
  marginalizes through `Prod.snd` into the reward-coordinate map law.  The
  remaining hard step is proving that pair-law identity from the finite-prefix
  `partialTraj` trajectory law.
- `COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP` now compiles as the
  generated `History.historyFiltrationSucc` specialization of the pair-law
  consumer: timewise action/reward measurability supplies the next coordinate
  measurability, and local history-filtration coordinate APIs supply reward
  prefix measurability.  The remaining hard step is still the actual
  `partialTraj`/history-to-`condExpKernel` action/reward pair-law identity.
- `COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP` now compiles
  as the concrete trace-pair and reward-projection specialization of that
  generated-history pair-law consumer: the pair history is
  `fun j => (action omega j, reward omega j)`, and the pair-context/state
  wrappers project the reward prefix before calling the original
  reward-history context/state.  The remaining hard step is still the actual
  generated-history `condExpKernel` pair-law identity.
- `COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP` now compiles as the
  local projection-measurability hookup: `History.pairHistoryRewardProjection`
  is measurable, so projected pair-context/state measurability follows from
  the original reward-history context/state measurability.  The remaining hard
  step is still the actual generated-history `condExpKernel` pair-law
  identity.
- `COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP` now compiles as the
  named finite pair-trace specialization: `History.finitePairHistoryOfTrace`
  is the `Finset.Iic`-indexed pair-coordinate prefix used in the remaining
  pair-law equality, aligning the conditional-expectation consumer with
  `RewardKernel.actionRewardPartialTrajectoryKernel`.  The remaining hard step
  is still the actual generated-history `condExpKernel` pair-law identity.
- `COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER` now compiles as
  the partialTraj finite-pair-trace consumer: an explicit generated-history
  `condExpKernel` law for the extended pair trace projects through
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply` into
  a reusable next-pair map-law adapter, then into the centered-reward consumer.
  The actual `partialTraj`/history-to-`condExpKernel` law remains open.
- `COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP` now
  compiles as the project-notation canonical wrapper: the Mathlib
  `trajMeasure` full-prefix `condExpKernel` law is restated with
  `History.finitePairHistoryOfTrace` for the old and successor pair prefixes.
  This aligns the canonical source theorem with the theorem-card shape, while
  still not transporting the law to an arbitrary generated
  `Omega`/`History.historyFiltrationSucc` process.
- `COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT`
  now compiles as the explicit source-contract for that remaining law shape:
  `GeneratedActionPartialTrajectoryPairLawSource` stores the full finite-pair
  `partialTraj`/`condExpKernel` equality over
  `generatedActionFromRewardHistory`, and
  `generatedActionRandomPairDefinitionalMapSource_of_partialTrajectoryPairLawSource`
  feeds it into the existing definitional generated random-pair map source.
  This names the exact input expected from future disintegration work without
  proving the theorem-card law.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION` now
  compiles as the source-projection theorem for that same law: a
  `GeneratedActionPartialTrajectoryPairLawSource` exposes its full finite-pair
  `partialTraj`/`condExpKernel` field as a named theorem matching the
  theorem-card law shape, and it now also projects to the weaker
  `GeneratedActionDefinitionalActualRewardMapSource`,
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource`, and explicit
  `GeneratedActionActualRewardMapSource` interfaces.  This lets downstream
  selected-reward, mean-zero, and conditional-MGF routes share the same
  packaged partialTraj source without unpacking its fields manually, while
  still leaving the actual disintegration/trajectory-law proof open.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP`
  now compiles as a source constructor from the narrower frozen-prefix
  extension-map law.  Future trajectory-law work can prove the extension-map
  `partialTraj`/`condExpKernel` equality, then this wrapper builds the full
  `GeneratedActionPartialTrajectoryPairLawSource` through the existing
  extension-to-full-trace adapter.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW`
  now compiles as the next upstream source constructor: a generated next-pair
  `condExpKernel` law identified with
  `RewardKernel.actionRewardHistoryStepKernelFamily` builds the same
  `GeneratedActionPartialTrajectoryPairLawSource` via the next-pair-to-extension
  and extension-to-full-source adapters.  This makes the remaining law target
  closer to the canonical `trajMeasure` next-pair route.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW`
  now compiles as the split-law source constructor: the generated action
  conditional a.e. law plus the policy-selected reward-coordinate
  `condExpKernel` map law build the same
  `GeneratedActionPartialTrajectoryPairLawSource` through the split next-pair
  law builder and existing source adapters.  This narrows the next proof target
  to the two split laws while keeping the theorem-card law open.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW`
  now compiles as the selected-reward source constructor and theorem wrapper:
  for
  `generatedActionFromRewardHistory`, the generated-trace action-freezing API
  supplies the action side automatically, so the policy-selected
  reward-coordinate `condExpKernel` map law alone builds the same
  `GeneratedActionPartialTrajectoryPairLawSource` and directly exposes the
  full finite-pair `partialTraj`/`condExpKernel` law.  The remaining upstream
  proof target is still the selected reward-coordinate law under the generated
  history filtration.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE`
  now compiles as a source-conversion wrapper: an existing
  `GeneratedActionRandomPairDefinitionalMapSource` projects to the
  policy-selected reward-coordinate law and then builds
  `GeneratedActionPartialTrajectoryPairLawSource`.  This connects the older
  definitional random-pair source surface to the newer partialTraj source
  route without changing the theorem-card status.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE`
  now compiles as the practical source-conversion wrapper for that same
  source contract: `GeneratedActionPartialTrajectoryPairLawSource`, measurable
  mean, centered reward-kernel law, raw reward range bounds, and deterministic
  mean range bounds build
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  This lets downstream raw-range/mean-range consumers use the named source
  directly, while still leaving the theorem-card pair-law proof open.
  The finite-pair comap selected-reward law can now enter at this base source
  layer too, with either the generated-history trim filter or the direct
  comap-trim filter, constructing the full finite-pair source internally before
  packaging the raw-range/measurable-mean-range source.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO`
  now compiles as the matching source-level mean-zero consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity
  directly yields ordinary succ-indexed conditional mean-zero for the centered
  generated reward.  It removes manual `hcontext`/`hstate`/full-law threading
  for this route, while still consuming rather than proving the underlying
  `partialTraj`/`condExpKernel` law.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE`
  now compiles as the global-variance companion: the same generated
  `partialTraj` pair-law source plus a pointwise bound
  `varianceProxy context action <= varianceCeiling` builds the packaged
  uniform-variance practical source.  It prepares the conditional-MGF route
  without proving the underlying `partialTraj`/`condExpKernel` law.
  The finite-pair comap selected-reward law can now enter at this source layer
  as well, constructing the full finite-pair source internally before packaging
  the uniform-variance practical source, with either the generated-history
  trim filter or the direct comap-trim filter accepted as the law surface; the
  selected-reward law and global ceiling remain explicit caller obligations.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-COND-MGF`
  now compiles as the source-level uniform MGF consumer: the same generated
  `partialTraj` pair-law source plus raw/mean range regularity and a global
  variance ceiling directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness.  It removes the need for
  downstream callers to manually pass `hcontext`, `hstate`, and the full
  finite-pair partialTraj law, while still leaving the theorem-card law open.
  The finite-pair comap selected-reward law can now be consumed directly into
  the same witness by first constructing the generated selected-reward source
  and full finite-pair `partialTraj` source; this still assumes the selected
  reward law rather than proving transport from canonical `trajMeasure`.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF`
  now compiles as the coarser-proxy source-level uniform MGF consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity, a
  global variance ceiling, and `varianceCeiling <= c` directly yields the
  succ-indexed `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `c`.
  It is still a consumer of the supplied full finite-pair law, not a proof of
  that law or of the proxy domination.
  The finite-pair comap selected-reward law can now enter this coarser-proxy
  route directly as well, by constructing the full finite-pair source
  internally; `varianceCeiling <= c` remains an explicit caller obligation.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE`
  now compiles as the selected-history companion: the same generated
  `partialTraj` pair-law source plus
  `varianceProxy (context i history) ((policy i).action (state i history)) <=
  varianceCeiling i` builds the packaged history-variance practical source.
  This is still a source conversion, not a proof of the trajectory-law card.
  The finite-pair comap selected-reward law can now enter at this source layer
  too, constructing the full finite-pair source internally before packaging the
  selected-history-variance practical source, with either the generated-history
  trim filter or the direct comap-trim filter accepted as the law surface;
  selected-history ceilings remain explicit caller obligations.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-COND-MGF`
  now compiles as the selected-history source-level MGF consumer: the same
  generated `partialTraj` pair-law source plus raw/mean range regularity and
  selected-history variance ceilings directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy
  `varianceCeiling i`.  It removes the same manual `hcontext`/`hstate`/law
  threading for the history-variance route while still consuming the packaged
  source law.
  The finite-pair comap selected-reward law now has the same direct entry into
  this selected-history-variance witness by constructing the full finite-pair
  source internally, with either the generated-history trim filter or the
  direct comap-trim filter accepted as the law surface; selected-history
  ceilings and the selected-reward law are still assumed inputs.
- `COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF`
  now compiles as the coarser-proxy selected-history source-level MGF
  consumer: the same generated `partialTraj` pair-law source plus raw/mean
  range regularity, selected-history variance ceilings, and
  `varianceCeiling i <= c` directly yields the succ-indexed
  `ProbabilityTheory.HasCondSubgaussianMGF` witness at proxy `c`.  It still
  consumes the supplied full finite-pair law and the proxy domination.
  The finite-pair comap selected-reward law can now enter this coarser-proxy
  selected-history route directly by constructing the full finite-pair source
  internally, with either the generated-history trim filter or the direct
  comap-trim filter accepted as the law surface; `varianceCeiling i <= c`
  remains an explicit caller obligation.
- `COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP` now compiles as
  the reward-coordinate adapter for that same full finite-pair-trace law:
  after projecting the `partialTraj` law to the next `(Action, Reward)` pair,
  it maps through `Prod.snd`, uses
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`, and rewrites
  the policy-selected action to the actual successor action under either an
  explicit action equality or `Policy.generatedActionTraceSucc`.  It still
  assumes the full finite-pair trace `condExpKernel`/`partialTraj` law.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER` now compiles as the
  extension-map partialTraj consumer: `Measure.map_congr` turns the generated
  successor decomposition into a pushforward equality, and a reusable adapter
  lifts any extension-map `partialTraj` law back to the full `i + 1` finite
  pair-trace law.  The centered consumer can still assume the narrower
  frozen-prefix extension-map law; the actual `partialTraj`/history-to-
  `condExpKernel` law remains open.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP` now compiles as the
  reward-coordinate adapter for that narrower extension-map law: it lifts the
  frozen-prefix extension-map law to the full finite-pair trace law, reuses the
  finite-pair-trace reward-map projection, and has a generated-action wrapper
  that supplies the successor action equality from `Policy.generatedActionTraceSucc`.
  The extension-map `condExpKernel`/`partialTraj` law remains assumed.
- `COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP` now compiles as the
  direct next-pair reward-coordinate adapter: an explicit
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair map law is
  projected through `Prod.snd` and
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`, then the
  policy action is rewritten to the actual successor action.  The
  finite-pair-history specialization aligns pair histories with reward-history
  context/state, and the generated-action wrapper removes the explicit
  successor equality when `Policy.generatedActionTraceSucc` is available.  The
  next-pair `condExpKernel` law itself remains assumed.
- `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP`
  now compiles as the selected-reward canonical `trajMeasure` law in project
  finite-pair-history notation: it rewrites the `Preorder.frestrictLe n`
  conditioning prefix to `History.finitePairHistoryOfTrace` and returns
  `RewardKernel.selectedMeasure` at that prefix.  This is only the canonical
  Mathlib trajectory source; the ambient `Omega`/`History.historyFiltrationSucc`
  transport step remains open.
- `COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP`
  now compiles as the reward-history projection of that canonical law, and
  `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT`
  now packages the corresponding generated ambient selected-reward law as an
  explicit source that converts into `GeneratedActionPartialTrajectoryPairLawSource`.
  The source still consumes the ambient reward-law field; it does not prove the
  trajectory-to-`condExpKernel` transport.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW`
  now compiles as the source constructor from the Mathlib-facing finite-prefix
  comap conditioning shape into
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource`.  It uses
  `History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace` and now
  accepts both the existing generated-history trim filter and a direct
  comap-trim filter at the selected-source, partialTraj-source, and theorem
  wrapper layers, so future selected-reward transport can target the comap
  sigma-algebra and directly enter the generated-history source route.  The
  same comap law now also constructs the full
  `GeneratedActionPartialTrajectoryPairLawSource` directly and exposes the
  theorem-card-shaped full finite-pair `partialTraj`/`condExpKernel` law
  without requiring callers to manually build and project the source.  It still
  consumes the selected-reward law.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW`
  now compiles as the source-projection theorem for that contract: a
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource` directly exposes
  the theorem-card-shaped full `finitePairHistoryOfTrace` partialTraj law over
  `generatedActionFromRewardHistory`.  This narrows the Lean-facing surface for
  downstream consumers but still assumes the selected-reward law field.
- `COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`
  now compiles as the upstream source conversion from the definitional
  actual-action reward-coordinate source to that selected-reward
  finite-pair-history source.  The proof only unfolds
  `generatedActionFromRewardHistory` and projects pair histories to reward
  histories; it still assumes the actual-action reward-coordinate law.
- `COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE`
  now compiles as the practical source conversion route: the definitional
  raw-range/measurable-mean-range generated random next-pair package, plus its
  uniform-variance and selected-history-variance wrappers, projects directly
  to `GeneratedActionSelectedRewardFinitePairHistoryLawSource` through the
  full finite-pair `partialTraj` source projection.  This lets the selected
  source mean-zero and conditional-MGF consumers start from the practical
  package surface; it still assumes the packaged random next-pair law.
- `COND-EXPECT-REWARD-PRACTICAL-SOURCE-VIA-SELECTED-FINITEPAIRHISTORY-COND-MGF`
  now compiles as the route-specific theorem surface for that composition:
  the practical base source reaches ordinary conditional mean-zero, and the
  practical uniform-variance/history-variance wrappers reach succ-indexed
  `HasCondSubgaussianMGF` witnesses, by first constructing the selected
  finite-pair-history source and then applying the selected-source consumers.
  This records the selected finite-pair-history route end-to-end while still
  consuming the packaged random next-pair law and variance/proxy contracts.
- `COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO`
  now compiles as the direct mean-zero consumer for that source contract:
  once the generated selected-reward finite-pair-history law is supplied, the
  existing full finite-pair source route plus raw/mean range regularity yields
  ordinary succ-indexed conditional mean-zero.  The finite-pair comap
  selected-reward law can now be consumed directly into the same mean-zero
  surface with either the generated-history trim filter or the direct
  comap-trim filter, after the local comap-to-source adapter constructs the
  source internally.
  The same selected-reward finite-pair-history source now also has direct
  conditional-MGF consumers: with raw/mean range regularity it feeds
  succ-indexed `HasCondSubgaussianMGF` witnesses under either a global
  variance ceiling, a coarser global proxy, selected-history variance
  ceilings, or a coarser selected-history proxy.  These wrappers reuse the
  packaged full finite-pair `partialTraj` source route and still consume the
  selected-reward law plus variance/proxy contracts.
  The uniform-variance conditional MGF consumer now accepts the same direct
  comap-trim law surface, provided raw/mean range regularity and a global
  variance ceiling are supplied.
  Its coarser-proxy companion now accepts the same direct comap-trim law
  surface when a deterministic domination proof `varianceCeiling <= c` is
  supplied.
  The selected-history-variance conditional MGF consumer now accepts the same
  direct comap-trim law surface under the time-indexed selected-history
  variance ceiling contract.
- `POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP` now compiles as the RewardKernel
  side of that route: the one-step action/reward `partialTraj` measure equals
  `Measure.map (History.extendPairHistorySucc history)` of
  `RewardKernel.actionRewardHistoryStepKernelFamily`.  This removes one
  Mathlib decomposition gap but still does not prove the generated-history
  `condExpKernel` law.
- `COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP` now compiles as the
  law builder from an explicit conditional next-pair pushforward identity into
  the extension-map `partialTraj` identity.  It connects the pair-map law shape
  to the extension-map law shape, but the next-pair `condExpKernel` identity is
  still the open mathematical step.
- `COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP` now also
  exposes generated-action reward-coordinate, actual-action pair-product, and
  fully random next-pair law shapes as full finite-pair-trace `partialTraj` law
  adapters before applying the centered conditional mean-zero consumers.  The
  generatedActionFromRewardHistory actual-action reward-coordinate surface now
  also has a source constructor and theorem wrapper that expose the same full
  finite-pair `partialTraj` law without passing an explicit action trace or
  generated-trace equality.  The pair/reward law source and ambient
  trajectory-to-`condExpKernel` identification remain open.
- `COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER` now compiles as the next
  decomposition: the full next-pair `condExpKernel` law follows from a
  conditional action a.e. equality to the policy-selected action plus a
  reward-coordinate selected-measure law.  This isolates the remaining
  predictability/action-freezing and reward-law sources.
- `COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW` now compiles as a
  canonical pair-law adapter:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`
  rewrites a generated-action random next-pair source law stated with
  `Measure.map (Prod.mk actualAction) selectedMeasure` into the standard
  `RewardKernel.actionRewardHistoryStepKernelFamily` form over
  `History.finitePairHistoryOfTrace`.  It keeps the random next-pair law as an
  explicit hypothesis but removes manual `Prod.mk`/selected-measure rewriting
  from downstream consumers.
- `COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP` now compiles as the action
  side of that split: a countable next action measurable at `F i`, plus
  trim-a.e. equality to the policy-selected action, yields the conditional
  action a.e. equality consumed by the split-law builder.  Policy
  predictability and the reward-coordinate law remain open.
- `COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP` now compiles as
  the generated-history version of that action side: visible finite pair
  histories, measurable `pairState`, and pointwise policy-generation equality
  produce the conditional action a.e. equality.  The reward-coordinate law is
  still separate.
- `COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE` now compiles as a
  shifted generated-trace source for that pointwise policy-generation equality:
  `action (i+1)` is definitionally selected by `policy i` from the finite
  pair-history state when the action trace equals `Policy.generatedActionTraceSucc`.
- `COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP` now
  compiles as the generated-action plus actual/random-pair reward-law route:
  an actual-action pair-product law marginalizes through `Prod.snd` to the
  actual-action reward-coordinate law, and a fully random next-pair law first
  freezes the action coordinate via `Measure.map_congr`.  The resulting law is
  rewritten to the policy-selected action, fed to the split-law builder, pushed
  through the extension-map `partialTraj` bridge, exposed as reusable
  full-trace law adapters, and consumed for succ-indexed conditional mean-zero
  under integrability.  The generatedActionFromRewardHistory actual-action
  reward-coordinate law is now also exposed directly as
  `GeneratedActionPartialTrajectoryPairLawSource` and as the theorem-card-shaped
  full finite-pair `partialTraj` law, with no explicit action trace/equality
  argument at the call site.  The pair/reward-law source and ambient
  trajectory-to-`condExpKernel` identification remain open.
- `COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT` now
  compiles in `BanditRLProof.ConditionalRewardLawSource` as the narrower
  reward-coordinate source package: `GeneratedActionActualRewardMapSource`
  stores the shifted generated-action equality plus only the actual next-action
  reward-coordinate `condExpKernel` map law.  Its consumers reuse the existing
  actual reward-map route to expose the full finite-pair-trace `partialTraj`
  law and succ-indexed conditional mean-zero.  This reduces the future law
  construction target below the full random next-pair law, but still assumes
  the reward-coordinate law, integrability, and ambient `condExpKernel`
  trajectory identification.
- `COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the actual reward-coordinate source-level canonical pair-law
  consumer: `GeneratedActionActualRewardMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `History.finitePairHistoryOfTrace`, with reward-history `context/state`
  lifted through `History.pairHistoryRewardProjection`.  This exposes the
  canonical pair-law surface from the weaker actual reward-coordinate source,
  but still assumes that source law and the ambient trajectory-to-`condExpKernel`
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`
  now compiles as the definitional generated-action version of that narrower
  source: `GeneratedActionDefinitionalActualRewardMapSource` fixes the action
  trace to `generatedActionFromRewardHistory`, derives `haction` from
  measurable reward-history state extractors and timewise reward measurability,
  converts to `GeneratedActionActualRewardMapSource`, and reuses its
  finite-pair-trace `partialTraj` and conditional mean-zero consumers.  The
  actual reward-coordinate law, integrability, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional actual reward-coordinate source-level
  canonical pair-law consumer: `GeneratedActionDefinitionalActualRewardMapSource`
  yields `RewardKernel.actionRewardHistoryStepKernelFamily` over
  `generatedActionFromRewardHistory`, deriving action measurability from the
  source's reward-history state measurability and reusing the explicit
  actual-source pair-law wrapper.  This keeps the source surface free of
  explicit `action`/`haction`, but still assumes the definitional
  reward-coordinate law and the ambient trajectory-to-`condExpKernel`
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW`
  now has a standalone card and canary for the definitional actual
  reward-coordinate source-level full finite-pair-trace `partialTraj`
  consumer:
  `actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`
  yields the `RewardKernel.actionRewardPartialTrajectoryKernel` law over
  `generatedActionFromRewardHistory`.  The theorem was already compiled as
  part of the source contract; the new leaf makes the full-trace law reusable
  independently from the canonical history-step pair-law consumer.  It still
  assumes the definitional reward-coordinate source law and the ambient
  trajectory-to-`condExpKernel` identification.
- `COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT` now compiles in
  `BanditRLProof.ConditionalRewardLawSource` as a reusable source package:
  `GeneratedActionRandomPairMapSource` stores the shifted generated-action
  equality plus each step's random next-pair `condExpKernel` map law, and the
  consumers expose both the full finite-pair-trace `partialTraj` law and
  succ-indexed conditional mean-zero.  This packages the remaining law
  assumption; it does not construct the pair/reward law source, prove
  integrability, or identify the ambient trajectory law with `condExpKernel`.
- `COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as a source-level canonical pair-law consumer:
  `GeneratedActionRandomPairMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `History.finitePairHistoryOfTrace`, with reward-history `context/state`
  lifted through `History.pairHistoryRewardProjection`.  This removes repeated
  unpacking of the source fields before downstream pair-law consumers while
  still leaving the random-pair source law and ambient `condExpKernel`
  trajectory identification explicit.
- `COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE` now
  compiles as a source-conversion layer: a generated random next-pair source
  can be weakened into `GeneratedActionActualRewardMapSource` by freezing the
  generated action coordinate under `condExpKernel` and marginalizing through
  `Prod.snd`.  The definitional variant converts
  `GeneratedActionRandomPairDefinitionalMapSource` into
  `GeneratedActionDefinitionalActualRewardMapSource` using the source's
  state-measurability field.  This does not construct the random-pair law.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the centered source map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairCenteredSource` exposes the
  source's packaged `GeneratedActionRandomPairMapSource` directly.  This is a
  named interface wrapper; it does not construct the random next-pair law or
  the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the centered-source projection layer:
  `generatedActionActualRewardMapSource_of_randomPairCenteredSource` weakens
  `GeneratedActionRandomPairCenteredSource` into
  `GeneratedActionActualRewardMapSource` by reusing the centered source's
  packaged random-pair map source and state-measurability field.  The centered
  kernel law and integrability fields remain assumptions carried by the
  stronger source.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the bounded-centered source map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  Its a.e. measurability and interval-bound evidence remain available for
  integrability consumers but are not needed by this weaker map-source
  interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the bounded-centered projection layer:
  `generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource`
  weakens `GeneratedActionRandomPairBoundedCenteredSource` into
  `GeneratedActionActualRewardMapSource` by reusing the bounded source's
  packaged random-pair map source and state-measurability field.  Its a.e.
  measurability and interval-bound evidence remain assumptions for
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT` now compiles
  as the narrower generated-action source layer:
  `GeneratedActionRandomPairDefinitionalMapSource` defines the action trace as
  `generatedActionFromRewardHistory`, derives timewise action measurability
  from measurable reward-history state extractors plus timewise reward
  measurability, converts to `GeneratedActionRandomPairMapSource`, and reuses
  the full finite-pair-trace and conditional mean-zero consumers.  The random
  next-pair law, integrability, and ambient `condExpKernel` trajectory
  identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional source-level canonical pair-law consumer:
  `GeneratedActionRandomPairDefinitionalMapSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `generatedActionFromRewardHistory`, avoiding explicit `action`/`haction`
  parameters before the canonical pair-law surface.  The definitional random
  next-pair law and ambient `condExpKernel` trajectory identification remain
  open assumptions.
- `COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT` now also compiles in
  `BanditRLProof.ConditionalRewardLawSource`: `GeneratedActionRandomPairCenteredSource`
  packages context/state measurability, the centered reward-kernel law, the
  generated random-pair source, and per-step ambient centered-reward
  integrability.  Its consumers expose the full finite-pair-trace `partialTraj`
  law and succ-indexed conditional mean-zero without a separate `h_integrable`
  argument.  The law source and integrability fields are still assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairCenteredSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by projecting its packaged
  random-pair map source plus context/state measurability.  This keeps the
  centered law and integrability fields available for later consumers while
  still leaving random-pair law construction and ambient `condExpKernel`
  trajectory identification open.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT` now
  compiles as the definitional generated-action centered source:
  `GeneratedActionRandomPairDefinitionalCenteredSource` removes explicit
  `action` and `haction` inputs from the centered source layer by reusing
  `generatedActionFromRewardHistory` plus
  `GeneratedActionRandomPairDefinitionalMapSource`.  Its conversion
  `generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`
  enters the existing centered-source route, and its consumers expose the full
  finite-pair-trace `partialTraj` law plus succ-indexed conditional mean-zero.
  The definitional random-pair law and centered integrability fields are still
  assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the definitional centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairDefinitionalCenteredSource` directly yields the
  `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law over
  `generatedActionFromRewardHistory`, again without explicit `action`/`haction`
  parameters.  It remains a source consumer, not a construction of the
  random-pair law.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY`
  now compiles as a named integrability projection:
  `centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource`
  exposes the definitional centered source's packaged per-step ambient
  centered-reward integrability without requiring downstream callers to unpack
  the structure field directly.  This is a projection of an assumed field, not
  a boundedness-derived integrability proof.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the direct random-pair map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionRandomPairMapSource` over `generatedActionFromRewardHistory`
  by projecting the packaged definitional map source.  The centered
  reward-kernel law and integrability fields are intentionally unused by this
  weaker map-source interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as a source-conversion leaf:
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionDefinitionalActualRewardMapSource` by projecting the
  packaged definitional random-pair map source.  The centered reward-kernel law
  and integrability fields remain available for stronger centered-source
  consumers but are intentionally unused by this weaker reward-coordinate
  interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the explicit generated-action counterpart:
  `generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource`
  weakens `GeneratedActionRandomPairDefinitionalCenteredSource` into
  `GeneratedActionActualRewardMapSource` whose action trace is
  `generatedActionFromRewardHistory`.  It first reuses the definitional
  actual-map projection and then the existing definitional-to-explicit actual
  reward-map conversion.
- `COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT` now compiles
  in the same module as the bounded/a.e.-measurable variant:
  `GeneratedActionRandomPairBoundedCenteredSource` replaces the direct
  centered-integrability field with per-step `AEMeasurable` evidence and a.e.
  interval bounds, derives integrability via Mathlib `Integrable.of_mem_Icc`,
  converts to `GeneratedActionRandomPairCenteredSource`, and exposes the same
  finite-pair-trace and conditional mean-zero consumers.  The random pair law,
  a.e. bound evidence, and ambient `condExpKernel` trajectory identification
  remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the bounded-centered-source canonical pair-law consumer:
  `GeneratedActionRandomPairBoundedCenteredSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairCenteredSource_of_boundedCenteredSource` and the
  centered-source pair-law route.  It preserves the bounded/a.e. regularity
  path while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT` now also
  compiles in `BanditRLProof.ConditionalRewardLawSource`:
  `GeneratedActionRandomPairRawMeanBoundedSource` replaces direct centered
  a.e. measurability and centered interval bounds with separate raw-reward and
  selected-mean a.e. measurability plus interval bounds.  It derives centered
  a.e. measurability via `AEMeasurable.sub`, derives centered bounds by
  interval subtraction, converts to `GeneratedActionRandomPairBoundedCenteredSource`,
  and exposes integrability plus the same finite-pair-trace and conditional
  mean-zero consumers.  The random pair law, raw/mean bound evidence, and
  ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw/mean bounded canonical pair-law consumer:
  `GeneratedActionRandomPairRawMeanBoundedSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource` and
  the bounded-centered pair-law route.  It keeps the raw-reward/selected-mean
  regularity path aligned with the canonical next-pair law while still leaving
  the random next-pair law and ambient `condExpKernel` trajectory
  identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw/mean bounded map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw/mean bounded projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its raw reward and
  selected mean a.e. measurability/bound fields remain assumptions for the
  centered-bound and integrability consumers but are not needed by this weaker
  interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT` now
  compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` removes the explicit
  raw-reward `AEMeasurable` field by deriving Rat-to-Real raw-reward
  a.e. measurability from the existing timewise reward trace measurability
  `hreward`.  It then converts to `GeneratedActionRandomPairRawMeanBoundedSource`
  and reuses the raw/mean bounded consumers.  Raw reward bounds, selected mean
  a.e. measurability/bounds, the random pair law, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/mean-bounded canonical pair-law consumer:
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` directly exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering through
  `generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`
  and then the raw/mean bounded pair-law route.  This keeps the
  reward-measurability-from-`hreward` source layer aligned with the canonical
  next-pair law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/mean-bounded map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/mean-bounded projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawBoundMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its raw reward bounds
  and selected mean a.e. measurability/bound fields remain assumptions for
  centered-bound and integrability consumers but are not needed by this weaker
  interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` removes the
  selected-mean `AEMeasurable` field by deriving Rat-to-Real selected-mean
  a.e. measurability from a measurable mean surface composed with finite
  reward histories, context/state extractors, and the measurable policy action.
  It then converts to `GeneratedActionRandomPairRawBoundMeanBoundedSource` and
  reuses its consumers.  Raw reward bounds, selected mean bounds, the random
  pair law, and ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/measurable-mean canonical pair-law consumer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` directly
  exposes `RewardKernel.actionRewardHistoryStepKernelFamily` by lowering
  through
  `generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`
  and then the raw-bound/mean-bounded pair-law route.  This keeps the
  measurable selected-mean source layer aligned with the canonical next-pair
  law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`
  weakens `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its measurable mean
  surface, raw reward bounds, and selected mean bound fields remain assumptions
  for centered-bound and integrability consumers but are not needed by this
  weaker interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` removes
  the selected-mean a.e. bound field by deriving the generated selected-mean
  interval bound from a deterministic pointwise range bound on the mean
  surface.  It then converts to
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` and reuses
  its consumers.  Raw reward bounds, mean measurability, deterministic mean
  range bounds, the random pair law, and ambient `condExpKernel` trajectory
  identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean-range map-source projection:
  `generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`
  exposes the source's packaged `GeneratedActionRandomPairMapSource` directly.
  This is a named interface wrapper; it does not construct the random
  next-pair law or the ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-bound/measurable-mean-range canonical pair-law
  consumer: `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`
  directly exposes `RewardKernel.actionRewardHistoryStepKernelFamily` by
  lowering through
  `generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`
  and then the raw-bound/measurable-mean pair-law route.  This keeps the
  deterministic selected-mean range-bound layer aligned with the canonical
  next-pair law while still leaving the random next-pair law and ambient
  `condExpKernel` trajectory identification as assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-bound/measurable-mean-range projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its measurable mean
  surface, raw reward bounds, and deterministic mean range bounds remain
  assumptions for centered-bound and integrability consumers but are not
  needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the next narrower source layer:
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` removes
  the raw reward a.e. bound field by deriving the generated raw reward
  interval bound from a deterministic pointwise range bound on the reward
  trace.  It then converts to
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource` and
  reuses its consumers.  Mean measurability, deterministic raw reward and
  mean range bounds, the random pair law, and ambient `condExpKernel`
  trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the raw-range/measurable-mean-range canonical pair-law
  consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`
  lowers through
  `generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`
  and reuses the raw-bound/measurable-mean-range history-step pair-law route.
  This exposes the canonical `RewardKernel.actionRewardHistoryStepKernelFamily`
  next-pair law directly from the deterministic raw reward and mean range
  source layer while still assuming the random next-pair law source and
  ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the raw-range/measurable-mean-range projection layer:
  `generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` into
  `GeneratedActionActualRewardMapSource` by reusing the source's packaged
  random-pair map law and state-measurability field.  Its deterministic raw
  reward and mean range fields remain assumptions for centered-bound and
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
  now compiles as the practical definitional generated-action version of that
  top source layer:
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  removes explicit `action` trace and `haction` inputs by using
  `generatedActionFromRewardHistory` plus
  `GeneratedActionRandomPairDefinitionalMapSource`.  It converts to
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` and
  reuses the existing integrability, full finite-pair-trace `partialTraj`
  law, and conditional mean-zero consumers.  The definitional random-pair law,
  mean measurability, deterministic raw reward and mean range bounds, and
  ambient `condExpKernel` trajectory identification remain open.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the practical definitional canonical pair-law consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  lowers through
  `generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  and reuses the explicit raw-range history-step pair-law route.  This exposes
  `RewardKernel.actionRewardHistoryStepKernelFamily` directly over
  `generatedActionFromRewardHistory` while preserving the implicit action
  surface of the practical top source.  It still assumes the definitional
  random next-pair law and ambient `condExpKernel` trajectory identification.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as a named map-source projection:
  `generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  directly into the explicit `GeneratedActionRandomPairMapSource` whose action
  trace is `generatedActionFromRewardHistory`.  This keeps the lower map-law
  route available without first building the full explicit raw-range source.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the matching partialTraj-source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens the same practical definitional raw-range source directly into
  `GeneratedActionPartialTrajectoryPairLawSource` by projecting the packaged
  definitional random-pair map source and context measurability.  This is a
  source-surface conversion only; it still assumes the packaged random next-pair
  law and does not prove the ambient `partialTraj`/`condExpKernel` trajectory
  identification.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY`
  now compiles as the top definitional regularity layer:
  `centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  and
  `centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  expose centered successor reward a.e. measurability and the deterministic
  centered interval bound directly from the practical definitional source.
  The proof route lowers through the existing explicit raw-range source
  conversion and reuses the raw-range regularity consumers.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the practical bounded-centered source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  directly into `GeneratedActionRandomPairBoundedCenteredSource` over
  `generatedActionFromRewardHistory`.  It packages the existing generated
  random-pair map-source projection with the centered successor reward
  a.e. measurability and interval-bound evidence, so later bounded-source
  integrability and tail routes can consume one named source contract.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the direct centered-source projection:
  `generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  lowers the same practical definitional source through the bounded-centered
  wrapper and into `GeneratedActionRandomPairCenteredSource` over
  `generatedActionFromRewardHistory`.  This exposes the existing
  integrability-based centered-source consumers from the top practical source
  contract without repeating the bounded-integrability construction at each
  call site.
- `COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the definitional centered-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`
  packages the same practical definitional source directly into
  `GeneratedActionRandomPairDefinitionalCenteredSource`.  It preserves the
  generated action trace as an implicit `generatedActionFromRewardHistory`
  surface while reusing the bounded-derived integrability theorem, so the newer
  definitional centered-source consumers can be reached without first exposing
  an explicit action trace.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the selected-history variance-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the definitional
  centered-source projection above.  This gives downstream centered-source
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the selected-history variance random-pair map projection:
  `generatedActionRandomPairMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated random-pair map-source projection.  This gives full next-pair law
  and partialTraj consumers a direct interface from the selected-history
  variance source while keeping the random next-pair law and time-indexed
  variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the selected-history variance full finite-pair
  `partialTraj` source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the raw-range-to-
  `partialTraj` source conversion.  This gives full finite-pair consumers a
  direct interface from the selected-history variance source while keeping the
  random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the selected-history variance history-step pair-law
  consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource`
  first exposes the generated random-pair map source and then reuses the
  source-level canonical history-step consumer.  This gives history-step
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the selected-history variance definitional actual
  reward-map projection:
  `generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the existing
  definitional actual reward-coordinate projection.  This gives definitional
  reward-coordinate consumers a direct interface from the selected-history
  variance source while keeping the random next-pair law and time-indexed
  variance ceilings as source assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the selected-history variance actual-reward-map projection:
  `generatedActionActualRewardMapSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated actual reward-map projection.  This gives reward-coordinate law
  consumers a direct interface from the selected-history variance source while
  keeping the random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the selected-history variance bounded-source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource`
  first forgets the history-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the bounded-centered
  projection.  This preserves deterministic centered reward bounds for
  bounded-integrability and tail consumers while keeping the selected-history
  variance ceiling as part of the source package.
- `COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the selected-history variance centered-source projection:
  `generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource`
  first lowers the history-variance wrapper to the bounded centered-source
  projection and then reuses the existing integrability-based centered-source
  conversion.  This gives downstream mean-zero and centered-source consumers a
  direct interface from the selected-history variance source while keeping the
  random next-pair law and time-indexed variance ceilings as source
  assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
  now compiles as the uniform variance random-pair map projection:
  `generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated random-pair map-source projection.  This gives full next-pair law
  and partialTraj consumers a direct interface from the uniform variance
  source while keeping the random next-pair law and global variance ceiling as
  source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE`
  now compiles as the uniform variance partialTraj-source projection:
  `generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the base source to
  `GeneratedActionPartialTrajectoryPairLawSource` conversion.  This gives full
  finite-pair `partialTraj` source consumers a direct interface from the
  uniform variance source while keeping the random next-pair law and global
  variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
  now compiles as the uniform variance canonical pair-law consumer:
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource`
  first exposes the generated random-pair map source and then reuses the
  generic random-pair-source history-step consumer.  This gives history-step
  law consumers a direct interface from the uniform variance source while
  keeping the random next-pair law and global variance ceiling as source
  assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the uniform variance definitional actual reward-map
  projection:
  `generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the existing
  definitional actual reward-coordinate projection.  This gives definitional
  reward-coordinate consumers a direct interface from the uniform variance
  source while keeping the random next-pair law and global variance ceiling as
  source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the uniform variance actual-reward-map projection:
  `generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the explicit
  generated actual reward-map projection.  This gives reward-coordinate law
  consumers a direct interface from the uniform variance source while keeping
  the random next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
  now compiles as the uniform variance-source projection:
  `generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the same definitional
  centered-source projection.  This gives downstream centered-source consumers
  a direct interface from the uniform variance source while keeping the random
  next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
  now compiles as the uniform variance bounded-source projection:
  `generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource`
  first forgets the uniform-variance wrapper to its packaged practical
  raw-range/measurable-mean-range source and then reuses the bounded-centered
  projection.  This preserves deterministic centered reward bounds for
  bounded-integrability and tail consumers while keeping the global variance
  ceiling as part of the source package.
- `COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE`
  now compiles as the uniform variance centered-source projection:
  `generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource`
  first lowers the uniform-variance wrapper to the bounded centered-source
  projection and then reuses the existing integrability-based centered-source
  conversion.  This gives downstream mean-zero and centered-source consumers a
  direct interface from the uniform variance source while keeping the random
  next-pair law and global variance ceiling as source assumptions.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the definitional raw-range projection layer:
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  into `GeneratedActionDefinitionalActualRewardMapSource` by reusing the
  source's packaged definitional random-pair map source.  Its deterministic
  raw reward and mean range fields remain assumptions for centered-bound and
  integrability consumers but are not needed by this weaker interface.
- `COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
  now compiles as the explicit generated-action projection layer:
  `generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  into `GeneratedActionActualRewardMapSource` whose action trace is
  `generatedActionFromRewardHistory`.  It first reuses the definitional
  actual-map projection and then the existing definitional-to-explicit actual
  reward-map conversion; the raw reward and mean range fields remain available
  for stronger centered-bound/integrability consumers.
- `POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP` now compiles as the Mathlib-backed
  `partialTraj` one-step next-coordinate marginal wrapper: the reward-history
  and action/reward pair trajectory kernels from `n` to `n + 1` push forward
  along coordinate `n + 1` to their configured history-step kernels.  This
  supplies the trajectory-kernel side of the future `condExpKernel` pair-law
  identification, not the conditional-kernel identity itself.
- `EXP-INDICATOR-PULL` now compiles as an `ENNReal` lower-integral
  action-event indicator canary.
- `EXP-FINSET-INDICATOR-PULL` now compiles as an `ENNReal` lower-integral
  finite-sum bridge for action-event indicators.
- `EXP-PULLCOUNT-LINTEGRAL` now compiles as an `ENNReal` lower-integral
  identity for scalar-casted recursive pull counts.
- `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` now compiles as an `ENNReal`
  lower-integral weighted pull-count bridge.
- `EXP-PULLCOUNT-LE-TIME` now compiles as an `ENNReal` probability-measure
  pull-count budget bound.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME` now compiles as an `ENNReal`
  probability-measure weighted pull-count budget bound.
- `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` now compiles as a `Fin K`/`Finset.univ`
  specialization of the weighted probability budget bound.
- `EXP-MODEL-GAP-OFREAL-BOUND` now compiles as an `ENNReal.ofReal` surrogate
  bound for `FiniteBanditModel.gap : Fin K -> Rat`.
- `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` now compiles as a scalar
  `ENNReal.ofReal` faithfulness lemma under explicit nonnegativity.
- `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` now compiles as a pointwise
  scalar/model pseudo-regret faithfulness bridge under explicit model-gap
  nonnegativity.
- `EXP-OFREAL-PSEUDOREGRET-BOUND` now compiles as an `ENNReal.ofReal`
  lower-integral pseudo-regret bound under explicit model-gap nonnegativity.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` now compiles as a
  Rat-level nonnegativity contract adapter for that lower-integral bound.
- `EXP-REGRET-PULLCOUNT` now compiles as a Real-valued Bochner expected-regret
  decomposition into finite gap-weighted expected pull counts under explicit
  per-arm pull-count integrability.
- `FINITE-BANDIT-GAP-BESTARM` now compiles as
  `FiniteBanditModel.gap_bestArm`, proving the selected best arm has zero
  local gap.
- `FINITE-BANDIT-BESTARM-DOMINATES` now compiles as
  `FiniteBanditModel.mean_le_bestArm_mean`, proving every arm mean is at most
  the selected best-arm mean.
- `FINITE-BANDIT-GAP-NONNEG` now compiles as
  `FiniteBanditModel.gap_nonneg`, proving the model-derived Rat-level gap
  nonnegativity contract.
- `FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
  `FINITE-BANDIT-MAXGAP-NONNEG` now compile as the finite max-gap model
  invariant layer.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` now compiles as a no-explicit-`hgap`
  `ENNReal.ofReal` lower-integral pseudo-regret bound.
- Probability, measure theory, concentration inequalities, and full regret
  theorem routes are mostly theorem cards or retrieval cards.
- `python3 tools/bandit.py unfinished` is now the local unfinished-work entry
  point.
- The local `python3 tools/bandit.py check` gate passes.

Plan to evaluate:

1. Treat the dependency-light finite-prefix baseline as closed.
2. Treat `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and
   `PSEUDOREGRET-FINSET` as closed Mathlib wrapper canaries.
3. Treat `REGRET-PULLCOUNT` as the first closed deterministic consumer leaf.
4. Treat `PULLCOUNT-SUM-TIME` as the first closed deterministic count
   partition leaf.
5. Treat `MEAS-FIN-ACTION` as the first closed probability/measure canary.
6. Treat `MEAS-PULL-INDICATOR` as the second closed probability/measure
   canary.
7. Treat `MEAS-REWARD` as the selected-reward indicator measurability canary.
8. Treat `MEAS-SELECTED-REWARD-FINITE-SUM` as the selected-reward finite-sum
   measurability bridge.
9. Treat `MEAS-SUMREWARDS` as the local recursive reward-sum measurability
   bridge.
10. Treat `MEAS-REGRET` as the local pseudo-regret random-variable
    measurability bridge.
11. Treat `MEAS-PULLCOUNT` as the local pull-count random-variable
    measurability bridge.
12. Treat `MEAS-PULLCOUNT-CAST` as the scalar-casted pull-count measurability
    bridge.
13. Treat `EXP-INDICATOR-PULL` as the first lower-integral
    indicator/event-measure canary.
14. Treat `EXP-FINSET-INDICATOR-PULL` as the lower-integral finite-sum bridge
    for action-event indicators.
15. Treat `EXP-PULLCOUNT-LINTEGRAL` as the lower-integral pull-count identity.
16. Treat `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` as the lower-integral weighted
    pull-count bridge.
17. Treat `EXP-PULLCOUNT-LE-TIME` as the probability-measure pull-count
    budget bound.
18. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME` as the probability-measure weighted
    pull-count budget bound.
19. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` as the `Fin K`/`Finset.univ`
    specialization.
20. Treat `EXP-MODEL-GAP-OFREAL-BOUND` as the `ENNReal.ofReal` surrogate
    model-gap bound.
21. Treat `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` as the scalar
    `ENNReal.ofReal` faithfulness leaf under explicit nonnegativity.
22. Treat `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` as the pointwise
    scalar/model bridge under explicit gap nonnegativity.
23. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND` as the `ENNReal.ofReal`
    lower-integral pseudo-regret bound under explicit gap nonnegativity.
24. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` as the Rat-level
    gap nonnegativity contract adapter for that lower-integral bound.
25. Treat `FINITE-BANDIT-GAP-BESTARM` as the canonical zero-gap fact for the
    selected best arm.
26. Treat `FINITE-BANDIT-GAP-NONNEG` as the model-invariant source for the
    explicit gap-nonnegativity contract used by the lower-integral bound.
27. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` as the no-explicit-`hgap`
    `ENNReal.ofReal` lower-integral pseudo-regret bound.
28. Treat `REGRET-COUNT-BOUND` as the deterministic scaffold converting
    per-arm pull-count bounds into a pseudo-regret bound.
29. Treat `REGRET-NAT-COUNT-BOUND` as the deterministic adapter for
    Nat-valued count bounds produced by future algorithm lemmas.
30. Treat `REGRET-UNIFORM-NAT-COUNT-BOUND` as the deterministic adapter for
    uniform Nat-valued count bounds.
31. Treat `ETC-EXPLOREARM-EQ-IFF-MOD` as the compiled modular selector helper
    for future ETC count theorems.
32. Treat `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` as the first compiled ETC
    round-robin count scaffold.
33. Treat `ETC-ROUND-ROBIN-ADD-K-COUNT` as the compiled full-cycle extension
    recurrence for ETC pull counts.
34. Treat `ETC-ROUND-ROBIN-MUL-K-COUNT` as the compiled multiple-full-cycle
    ETC count theorem.
35. Treat `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` as the configured
    exploration-horizon count adapter.
36. Treat `ETC-EXPLORATION-REGRET-BOUND` as the deterministic exploration-only
    ETC pseudo-regret scaffold.
37. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` as the fixed-commit ETC
    trace boundary on the exploration prefix.
38. Treat `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` as the fixed-commit ETC trace
    boundary after the exploration horizon.
39. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the fixed-commit
    ETC trace boundary after the exploration horizon when the commit arm is
    the selected best arm.
40. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` as the
    exploration-prefix pull-count transfer for the fixed-commit ETC trace.
41. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` as the configured
    exploration-horizon pull count for the fixed-commit ETC trace.
42. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` as the
    deterministic fixed-commit ETC trace regret scaffold at the exploration
    horizon.
43. Treat `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` as the one-step
    post-commit pull-count recurrence for the fixed-commit ETC trace.
44. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` as the closed-form
    post-exploration suffix pull count for the fixed-commit ETC trace.
45. Treat `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` as the
    non-commit-arm post-exploration pull-count stability corollary.
46. Treat `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` as the commit-arm
    post-exploration pull-count corollary.
47. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` as the compiled
    count-budget pseudo-regret scaffold for the fixed-commit ETC trace.
48. Treat `ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` as the compiled
    coarse uniform post-exploration suffix regret bound.
49. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` as the compiled
    post-horizon phase-split pseudo-regret equality.
50. Treat `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` as the compiled
    phase-split exploration-plus-suffix-gap regret bound.
51. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` and
    `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` as the compiled
    optimal-commit deterministic suffix facts.
52. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the compiled
    trace fact that a best-arm commit stays on the selected best arm after the
    exploration horizon.
53. Treat `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as a theorem-card-only /
    missing-leaf design, not a local Lean proof.
54. Treat `ETC-MEAS-COMMITARM-NE-BESTARM` as the first compiled
    wrong-commit event measurability leaf.
55. Treat `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` as the compiled pure
    set-inclusion event-reduction leaf.
56. Treat `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` as the
    compiled arbitrary-measure monotonicity wrapper for the wrong-commit event
    reduction.
57. Treat `ETC-MEAS-EMPMEAN-GE-EMPMEAN` as the compiled pairwise
    empirical-mean comparison-event measurability canary.
58. Treat `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` as the compiled
    finite existential wrong-mean event measurability wrapper.
59. Treat `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` as the
    compiled finite-union probability upper-bound wrapper.
60. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` as the compiled
    final elementary event-probability assembly wrapper.
61. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` as the compiled
    abstract non-best pairwise-tail consumer wrapper.
62. Treat `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` as the compiled
    if-zeroed nonbest pairwise-tail consumer wrapper.
63. Treat `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled filtered-sum pairwise-tail consumer wrapper.
64. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the compiled
    deterministic Nat denominator-positivity leaf for fixed-commit ETC
    exploration counts.
65. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` as the
    compiled Rat denominator-positivity adapter for fixed-commit ETC
    exploration counts.
66. Treat `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` as the
    compiled Rat nonzero-denominator adapter for fixed-commit ETC exploration
    counts.
67. Treat `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` as the compiled
    deterministic fixed-commit exploration-horizon empirical-mean definition
    and denominator rewrite.
68. Treat `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled numerator-measurability bridge for fixed-commit ETC empirical
    means under stochastic reward traces.
69. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`
    as the compiled full empirical-mean measurability wrapper under an
    explicit Rat division-by-constant measurability contract.
70. Treat `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` as the compiled
    Rat division-by-constant measurability wrapper under
    `[MeasurableSingletonClass Rat]`.
71. Treat `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` as the
    compiled no-`hdiv_const` empirical-mean measurability theorem consuming
    the Rat wrapper.
72. Treat `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` as the compiled
    coordinate-shaped empirical-mean measurability wrapper selected by
    Extended Pro.
73. Treat `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` as the compiled deterministic
    abstract commit-oracle argmax consumer for the wrong-commit event
    reduction.
74. Treat `ETC-COMMIT-ORACLE-PROB-WRAPPER` as the compiled
    oracle-specialized abstract pairwise-tail probability consumer selected by
    Extended Pro.
75. Treat `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` as the compiled
    oracle-specialized filtered-sum pairwise-tail probability consumer selected
    by Extended Pro.
76. Treat `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` as the compiled
    oracle-specialized if-zeroed nonbest pairwise-tail probability consumer
    selected by Extended Pro.
77. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` as the compiled
    oracle-selected wrong-event measurability wrapper under direct composed
    choice measurability, selected by Extended Pro.
78. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` as the compiled
    Mathlib-backed countable score-vector oracle-choice measurability bridge
    selected by Extended Pro as an immediately compilable candidate.
79. Treat `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` as the compiled Mathlib
    Pi-space coordinate-to-vector empirical-mean measurability bridge selected
    by Extended Pro.
80. Treat `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-choice measurability
    composition wrapper selected by Extended Pro.
81. Treat `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` as the
    compiled coordinatewise empirical-mean-to-oracle-wrong-event measurability
    composition wrapper selected by Extended Pro.
82. Treat `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` as the
    compiled concrete argmax-oracle filtered-sum pairwise-tail consumer wrapper.
    `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally, packaging the
    fixed-commit ETC empirical-mean pairwise-tail assumption and its concrete
    argmax consumer.  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is also compiled
    locally, removing the common positive empirical-mean denominator and
    reducing pairwise empirical-mean comparison to fixed-horizon reward-sum
    comparison.  `TAIL-HOEFFDING-BOUNDED` is now compiled locally as the
    generic bounded-centered Hoeffding MGF source with interval variance
    proxy.  `TAIL-SUBGAUSS-SUM` is now compiled locally as a Mathlib
    import wrapper for independent sub-Gaussian finite-sum tails, and
    `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is compiled locally as its ENNReal-valued
    event-probability boundary wrapper.  `TAIL-COND-SUBGAUSS` is also compiled
    locally as a Mathlib-backed strongly adapted conditional sub-Gaussian
    finite-prefix wrapper and ENNReal boundary adapter.  The ETC pairwise tail contract itself
    is now producible from explicit abstract sub-Gaussian witnesses through
    `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS`.  The generic empirical-mean
    comparison event-shape adapter is now compiled as
    `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT`.  The concrete
    centered reward-difference bridge is now compiled as
    `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET`, and the concrete centered-diff
    sub-Gaussian producer specialization is compiled as
    `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF`.  The exact witness package
    consumed by that producer is now compiled as
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT`.  The canonical
    exponential tail helper is now compiled as
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL`.  The canonical
    wrong-commit probability bound consuming that tail is now compiled as
    `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND`.  The deterministic
    reward-coordinate independence and centered reward sub-Gaussian transfers,
    plus the reward-coordinate-law wrong-commit bound, are now compiled as
    `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS`,
    `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS`, and
    `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND`.  The ETC-shaped
    bounded-reward Hoeffding source now reuses the generic `Concentration`
    wrapper, and the corresponding strong all-arm bounded-reward
    wrong-commit bound is compiled as
    `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
    `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND`.  The action-matched
    reward-sub-Gaussian and bounded-reward wrong-commit wrappers are now
    compiled as
    `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` and
    `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND`.  The exact
    action-matched source contract package is now compiled as
    `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT`.  The fixed product-coordinate
    source and its direct wrong-commit probability bound are now compiled as
    `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
    `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE`.
    The same fixed-product wrong-commit bound now also has a standalone
    `Measure.real` bridge from the finite `ENNReal` tail budget under
    `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND`.
    The pointwise wrong-commit regret assembly bridge is now compiled as
    `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE`.
    The abstract lower-integral wrong-commit regret assembly is now compiled
    as `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY`.
    The concrete finite-argmax/infinitePi lower-integral regret assembly is now
    compiled as `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY`.
    The fixed product-coordinate bad-gap lower-integral endpoint now also has
    a named `ETC.fixedProductArgmaxAction` wrapper and named `ENNReal.ofReal`
    RHS budget under `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER`.
    The conservative sum-gap suffix adapter for that assembly is now compiled
    as `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The fixed product-coordinate conservative sum-gap lower-integral endpoint
    now also has a named `ETC.fixedProductArgmaxAction` wrapper and named
    `ENNReal.ofReal` RHS budget under
    `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER`.
    The sharper max-gap suffix adapter is now compiled as
    `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY`.
    The polished fixed product-coordinate max-gap wrapper is now compiled as
    `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER`.
    The Bochner/Real finite-argmax/infinitePi expected-regret assembly now also
    exposes the bad-gap endpoint through the named `ETC.fixedProductArgmaxAction`
    API, aligned with the existing sum-gap and max-gap Real wrappers, under
    `ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY`.
    `ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET` now removes the
    public `baseCommitArm` artifact from the fixed-product max-gap Real endpoint:
    bounds and means are stated directly at `ETC.exploreArm`, while the existing
    wrapper is reused with `model.bestArm` only as an internal seed.  This closes
    the canonical fixed-product theorem surface, not the adaptive/LML ETC
    theorem; the next required transport is an action-dependent environment law
    aligned with the random post-exploration commit trace.
    `ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE` is now compiled as the first
    direct support leaf for that transport: it proves fixed-commit exploration
    scores depend only on reward coordinates below the exploration horizon. The
    next narrow route remains construction and alignment of a history-derived
    commit policy, not an expected-regret theorem.
    `ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION` now provides the exact
    generated-state score reconstruction needed by that next route: a history
    through time `t` determines the exploration argmax scores when the
    exploration horizon is at most `t + 1`. The remaining narrow task is an
    action equality for a measurable finite-history ETC policy.
    `ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT` now compiles that policy
    and function-level action equality. The next narrow task is no longer a
    deterministic ETC wrapper: it is an action-dependent reward-law source for
    the generated trace, to be consumed by the already compiled conditional
    expectation and conditional-MGF surfaces.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW` now supplies the
    full generated finite-pair law for the canonical Markov-kernel trajectory.
    The next narrow task is measure/kernel transport and finite-bandit
    regularity identification, not another generated-policy construction.
    `ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN` now also
    reaches the conditional-MGF layer for rewards centered at `model.mean`.
    `ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL` now constructs the raw
    context-independent Markov reward kernel from per-arm probability laws and
    proves selected-measure equality.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF` now also constructs the
    centered model-mean law from common bounded arm laws and feeds it through
    the canonical trajectory conditional-MGF theorem.
    `ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL` now adds the true time-zero
    term and proves the complete selected centered-reward finite-sum tail.
    `ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT` now constructs the required
    fixed-exploration masked pairwise process through the existing witness
    package and proves the actual empirical-mean wrong-commit finite-union bound
    under canonical `trajMeasure`.
    `ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET` now also compiles the
    Real probability conversion, measurable commit/wrong event, integrability,
    and generated-action Bochner expected-regret endpoint.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET` now factors the
    integrand through the `m*K` exploration rewards and transports the bound to
    any external reward law with the same finite-prefix pushforward.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET` now derives
    that pushforward identity from the initial reward marginal and successor
    `condDistrib` laws only through exploration, then transports the integral
    back to the original sample space.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET`
    now rewrites those hypotheses directly as stationary laws of the scheduled
    exploration arms, with no caller-visible context/state/policy kernel or
    trajectory measure. The next narrow law work is a concrete environment or
    LML `IsAlgEnvSeq` bridge to these conditional laws.
    `ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET`
    now accepts constant scheduled-arm laws with the exact LML feedback
    conditioning-variable shape and projects them to reward prefixes. The next
    seed-specific action-dependent kernel plus a.e. action transport is now
    compiled by the action-dependent full-history endpoint. The law route is
    complete without an LML dependency; a direct `IsAlgEnvSeq` wrapper is
    optional. The exact LML route next needs Real
    rewards/models, arbitrary common-sub-Gaussian laws, argmax tie semantics,
    and per-arm gap-weighted expected pull-count bounds; the local max-gap union
    theorem must not be presented as the exact `Bandits.ETC.regret_le` port.
83. Do not start final adaptive ETC/UCB theorem work from the compiled
    lower-integral surrogate.  The current narrow option is a deliberately
    split derivation of conditional witness fields from a concrete reward law:
    the shifted-history `StronglyAdapted` field, zero-summand MGF source,
    sampled-arm MGF transfer, reward-level conditional witness contract,
    independence-based conditional MGF and mean-zero wrappers, reward-only past
    independence bridge, full fixed-action history independence bridge,
    exact-mean zero-integral source, and bounded-source conditional mean-zero
    wrapper are now compiled; bounded rewards now also imply raw reward
    integrability locally, and fixed deterministic `actionWithCommit`
    centered rewards now instantiate a finite-prefix martingale-difference
    witness, while global succ-indexed martingale-difference witnesses now
    produce a Mathlib partial-sum `Martingale`.  CondExpKernel reward-law
    identification and final adaptive assembly remain beyond the fixed-action
    boundary.

Current review conclusion:

- Extended Pro judged the deterministic fixed-commit ETC layer saturated enough
  for now.
- The current required route-review mechanism is local two-agent review, not
  ChatGPT Extended Pro.
- The latest local two-agent review selected
  `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`; that leaf now
  compiles locally in `BanditRLProof.Algorithms.ETCArgmaxOracle`.
- `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` is now compiled locally.
- `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `IID-REWARD-FAMILY` now compiles locally in
  `BanditRLProof.IndependenceFoundation` as generic infinite-product
  coordinate-transform independence plus a reward-trace specialization.
- `TAIL-HOEFFDING-BOUNDED` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian` as
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`.
- `TAIL-SUBGAUSS-SUM` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `TAIL-COND-SUBGAUSS` now compiles locally in
  `BanditRLProof.ConcentrationSubGaussian`.
- `MEAS-HISTORY` now compiles locally in
  `BanditRLProof.HistoryFiltration` as finite action/reward history product
  objects over `Finset.Iic` prefixes, with measurable trace restrictions and
  measurable coordinate projections, including pair-coordinate trace prefixes
  and reward projection from finite `(Action, Reward)` pair histories.  It now
  also names the measurable successor-extension map for pair histories.
- `FILTRATION-HISTORY` now compiles locally in
  `BanditRLProof.HistoryFiltration`.
- `HISTORY-FILTRATION-FINITEPAIR-COMAP` now compiles locally in
  `BanditRLProof.HistoryFiltration`: finite pair histories are measurable at
  later generated-history filtration levels, and
  `History.historyFiltration ... (n + 1)` is exactly the comap of
  `History.finitePairHistoryOfTrace ... n`; the shifted
  `History.historyFiltrationSucc ... n` form is also named.  This is the
  sigma-algebra bridge between the local generated-history filtration and
  Mathlib finite-prefix conditioning surfaces; it does not prove reward-law or
  trajectory-law transport.
- `ADAPTED-ACTION` now compiles locally in
  `BanditRLProof.HistoryFiltration` as a countable/discrete past-coordinate
  measurability canary, with a reward-coordinate companion theorem.
- `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` now compiles locally in
  `BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail`.
- `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` now compiles locally in
  `BanditRLProof.Algorithms.ETCSumRewardsDiff`.
- `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` now compiles locally in
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, using
  `History.historyFiltrationSucc` from `BanditRLProof.HistoryFiltration`.
- `ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT` now compiles locally
  in `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`.
- `ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `MART-DIFF-REWARD` now compiles locally in
  `BanditRLProof.MartingaleDifference`, including centered reward process
  builders from adaptedness, integrability, and succ-indexed conditional
  mean-zero contracts, plus the abstract Mathlib partial-sum `Martingale`
  wrapper, and
  `ETC-CENTERED-REWARD-MART-DIFF-BOUNDED-SOURCE` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `TAIL-UNION-FINITE` now compiles locally in
  `BanditRLProof.ProbabilityUnionBound` as reusable explicit-`Finset` and
  `[Fintype]` finite-union outer-measure wrappers, including a nonempty-Finset
  equal-share `delta/card` normalizer; this is a probability assembly leaf, not
  a concentration theorem.
- `TAIL-SUMMABILITY-UCB` now compiles locally in
  `BanditRLProof.UCBSummability` as an abstract finite-arm finite-horizon
  bad-event summability wrapper consuming per-arm/per-time ENNReal tail bounds;
  UCB log/sqrt side conditions and the final regret theorem remain separate.
- `EXP3-POTENTIAL` now compiles locally in `BanditRLProof.Exp3Potential` as
  a deterministic finite-action exponential-weights potential surface with
  update unfolding, nonnegativity, one-step increment algebra, and
  finite-horizon telescoping.
- `EXP3-HEDGE-DETERMINISTIC-REGRET` now compiles locally in
  `BanditRLProof.Exp3HedgeRegret`: positive cumulative-loss weights are
  normalized on a nonempty finite arm set, the quadratic exponential bound and
  one-step log-potential inequality are proved, and telescoping yields a
  second-order comparator theorem for arbitrary nonnegative losses under
  `eta > 0`, plus `log |A| / eta + eta*T` for `[0,1]` losses.
- `EXP3-IMPORTANCE-WEIGHTED-MOMENTS` now compiles locally in
  `BanditRLProof.Exp3ImportanceWeighted`: the sampled-coordinate estimator has
  exact finite-sum armwise cancellation and mixed-loss identities, while its
  probability-weighted mixed square is exactly `sum_a loss(a)^2` and at most `|A|` for
  losses in `[0,1]`. These are deterministic weighted-sum identities.
- `EXP3-CONDITIONAL-MOMENT-TRANSPORT` now compiles locally in
  `BanditRLProof.Exp3ConditionalMoments`: an explicit normalized finite Dirac
  action law and an actual history-conditional `condDistrib` equality yield
  armwise unbiasedness plus exact mixed-loss and mixed-square Bochner-integral
  identities.
- `EXP3-GENERATED-ACTION-PROCESS` now compiles locally in
  `BanditRLProof.Exp3ActionProcess`: measurable history-indexed finite
  probability vectors generate a Markov kernel and canonical `compProd`
  history/action measure; the sampled action's `condDistrib` is a.e. that
  policy, and canonical armwise/mixed first- and second-moment wrappers consume
  the previous transport without external law premises.
- `EXP3-SCORE-REGULARITY` now compiles locally in
  `BanditRLProof.Exp3ScoreRegularity`: measurable supported `[0,1]` losses and a
  uniform positive probability floor imply measurable armwise/mixed first- and
  second-moment scores, pointwise reciprocal-floor bounds, and generated-law
  integrability. Its canonical consumers remove manual `hprob`, `hscore`, and
  `hIntegrable` premises from all three one-round moment identities.
- `EXP3-EXPLORATION-MIXED-RECURSIVE-TRAJECTORY` now compiles locally in
  `BanditRLProof.Exp3RecursiveTrajectory`: any measurable cumulative score on
  inclusive finite action/loss histories generates normalized exploration-mixed
  probabilities with floor `gamma / |A|`, a stochastic history algorithm, a
  complete adaptive trajectory kernel, and the exact successor-action
  conditional law given each finite prefix.
- `EXP3-SAMPLED-HISTORY-SCORE-RECURSIVE-TRAJECTORY` now compiles locally in
  `BanditRLProof.Exp3SampledHistoryScore`: the score starts from the initial
  action law and recursively adds each observed chosen-action Real loss divided
  by the exact preceding exploration-mixed probability. Its coordinate
  measurability, concrete probability floor, stochastic history algorithm,
  complete trajectory kernel, and exact successor-action conditional law all
  compile without arbitrary `score/hscore` inputs.
- `EXP3-PREDICTABLE-ADVERSARY` now compiles locally in
  `BanditRLProof.Exp3PredictableAdversary`: jointly measurable initial and
  history-dependent successor loss vectors are fixed before the current
  action, bounded in `[0,1]`, and realized as chosen-coordinate Dirac feedback.
  A prior-mixture transport preserves the concrete sampled EXP3 policy after
  conditioning on `(Env, prefix)`, closing the action-reactive-adversary gap.
- `EXP3-PREDICTABLE-OBSERVED-MOMENTS` and
  `EXP3-PREDICTABLE-FINITE-HORIZON-MOMENTS` now compile locally in
  `BanditRLProof.Exp3PredictableMoments`: initial and successor generated
  rewards equal their selected predictable losses almost surely, every actual
  time has the observed armwise first and mixed-square second moment identity
  on the common trajectory law, and both identities sum over
  `Finset.range horizon` with explicit integrability. The next theorem boundary
  is the sampled-history-score/Hedge-potential coupling, followed by
  exploration-bias control and `eta`/`gamma` optimization. This is not final
  EXP3 regret.
- `FTRL-ONE-STEP` now compiles locally in `BanditRLProof.FTRLOneStep` as
  a deterministic finite-action regularized-objective minimizer wrapper
  yielding the one-step linear-loss inequality under `0 < eta`; the new
  finite-horizon regularized be-the-leader theorem consumes it downstream.
  Convexity and minimizer existence remain separate.
- `TSALLIS-REGULARIZER` now compiles locally in
  `BanditRLProof.TsallisRegularizer` as a finite-simplex `Real.rpow`
  power-sum, entropy, and negative-entropy regularizer surface with nonzero
  denominator and nonnegative power-sum facts; its exact finite-horizon
  penalty now compiles downstream.
- `TSALLIS-FTRL-STABILITY-PENALTY-REGRET-DECOMPOSITION` now compiles locally in
  `BanditRLProof.TsallisFTRLRegret`.  `FTRL.cumulativeLoss`, linear-loss
  finite-sum transport, and explicit cumulative `IsRegularizedMinimizer`
  certificates prove regularized be-the-leader and the generic pathwise
  stability/penalty decomposition.  The public Tsallis theorem states the
  full finite-horizon comparator regret bound with stability
  `sum_t (<p_t,l_t>-<p_(t+1),l_t>)` and power-sum penalty
  `((powerSum p_0-powerSum q)/(1-alpha))/eta`.  Contracts are finite arms,
  `eta>0`, `alpha!=1`, simplex comparator, and explicit minimizers through
  `T`; no stochastic, measurability, unbiasedness, convexity, or existence
  premise is hidden.  The `alpha=1/2` stationarity-based stability consumer
  and canonical minimizer/update construction below now close its deterministic
  one-step term, while the canonical cumulative selector closes finite-horizon
  instantiation.  Conditional estimator transport, expected stability
  assembly, self-bounding, and tuning remain.
- `TSALLIS-HALF-INTERIOR-STATIONARITY-ONE-STEP-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLOneStepStability`.  The public endpoint assumes the
  current distribution and every sampled-action update are strictly positive
  finite-simplex points satisfying the explicit half-Tsallis stationarity
  equations.  Equal simplex sums trap the multiplier displacement, negative
  half-power antitonicity and a scalar curvature lemma control the pathwise
  linear-loss difference, and the previous power-moment leaf yields the finite
  sampling-law bound `2*eta*powerSum arms (1/2) prob` for `[0,1]` losses.
  This is a valid but looser bound for the local FTRL decomposition term, not
  the paper's conjugate-potential Lemma 11/19 verbatim: matching regularizer
  scaling uses `eta_local=eta_paper/2`, under which this coefficient is twice
  the comparable Lemma 11 coefficient.
  This is not by itself a minimizer existence/interiority proof, conditional
  expectation, horizon theorem, or final Tsallis-INF regret result.  The
  minimizer-to-stationarity, interiority, and existence/selection layers below
  now discharge those deterministic prerequisites.
- `TSALLIS-HALF-MINIMIZER-STATIONARITY-TRANSPORT` now compiles in
  `BanditRLProof.TsallisFTRLStationarity`.  A two-coordinate zero-sum shift
  preserves simplex feasibility near every strictly positive point.  Mathlib's
  finite-sum and square-root derivative APIs plus
  `IsLocalMin.hasDerivAt_eq_zero` turn a half-Tsallis
  `IsRegularizedMinimizer` into pairwise gradient equality and a common
  `HalfTsallisInteriorStationary` multiplier.  Conversely, the square-root
  supporting-line inequality reconstructs global minimality, yielding an iff
  theorem.  The downstream sampling-law stability wrapper now accepts current
  and sampled-update minimizer certificates and chooses multipliers internally.
  The bridge assumes finite-simplex feasibility and strict positivity but no
  sign condition on `eta`; the stability consumer keeps its prior `eta>0` and
  `[0,1]` loss contracts.  Root import, focused build, an abstract iff canary,
  a nonzero-loss `Fin 1` minimizer consumer, and a distinct-coordinate
  nonuniform `Fin 2` pairwise canary all compile.  This module itself assumes
  interiority; the next two leaves close interiority and concrete
  minimizer/update existence.
- `TSALLIS-HALF-MINIMIZER-INTERIORITY` now compiles in
  `BanditRLProof.TsallisFTRLInteriority`.  A zero supported coordinate is ruled
  out by transferring sufficiently small mass from a positive donor: the new
  square-root term contributes order `sqrt(t)`, while the donor loss and fixed
  linear score change are order `t`.  The theorem
  `Tsallis.isRegularizedMinimizer_pos` needs no eta sign condition, and the
  public minimizer-shaped sampling-law stability theorem no longer asks for
  `hprobPos` or `hnextPos`; it derives positivity and multipliers internally.
  Root import, focused builds, the abstract positivity canary, and a
  positivity-free nonzero-loss `Fin 1` consumer compile.  The next leaf closes
  concrete minimizer existence/selection; conditional/horizon transport still
  remains and no final Tsallis-INF theorem is claimed.
- `TSALLIS-HALF-MINIMIZER-EXISTENCE-SELECTION` now compiles in
  `BanditRLProof.TsallisFTRLMinimizerExistence`.  Because
  `FTRL.finiteSimplex arms` does not constrain ambient coordinates outside
  `arms`, the proof minimizes on Mathlib's compact `stdSimplex Real ↥arms` and
  zero-extends the result.  Continuity of the half-Tsallis objective and
  `IsCompact.exists_isMinOn` yield a global explicit-simplex minimizer for every
  nonempty finite arm set, arbitrary Real score, and arbitrary Real eta.
  `halfTsallisMinimizer` and `halfTsallisUpdatedMinimizer` package stable
  noncomputable choices, and the public one-step bound now selects both current
  and importance-weighted updated minimizers internally.  Root import, focused
  build, existence canary, and parameter-free one-step canary compile.  These
  This module alone does not prove the choices measurable as functions of
  history. The downstream canonical-selector leaf now proves supported
  coordinate measurability from strict convexity, compact-ultrafilter
  continuity, and Borel composition; deterministic finite-horizon assembly
  also compiles separately.
- `TSALLIS-HALF-CANONICAL-FINITE-HORIZON-DECOMPOSITION` now compiles in
  `BanditRLProof.TsallisFTRLFiniteHorizonSelection`.  The canonical sequence is
  `halfTsallisMinimizer` applied to `FTRL.cumulativeLoss loss t`; its pointwise
  certificates instantiate the existing alpha=1/2 finite-horizon
  power-sum-penalty theorem with no caller minimizer sequence or certificate.
  Separate successor theorems align `t+1` with appended round loss and with
  `halfTsallisUpdatedMinimizer` under the realized importance-weighted-loss
  identity.  Root/focused and external canary builds compile.  Next work is
  not another deterministic minimizer wrapper: it is measurable or explicit
  history selection plus conditional action-law/expectation transport of the
  one-step sampling average into the expected stability sum.  Self-bounding,
  tuning, and final Tsallis-INF regret remain open.
- `TSALLIS-HALF-CONDITIONAL-ACTION-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLConditionalStability`. The generic theorem
  transports an identified conditional action law to the finite current
  half-Tsallis law and integrates the compiled pointwise minimizer stability
  inequality. Generated `Exp3.actionProcessMeasure` and canonical
  history-selector consumers remove the conditional-law and minimizer
  certificates from callers. This closes one-round conditional transport,
  not the stochastic horizon: coordinate measurability of the
  `Classical.choose` selector and measurable/integrable updated-score
  producers remain explicit prerequisites consumed by the expected
  finite-horizon theorem below.
- `TSALLIS-HALF-EXPECTED-FINITE-HORIZON-STABILITY` now compiles in
  `BanditRLProof.TsallisFTRLExpectedStability`. Per-round condDistrib
  identities recover the realized joint laws and regularity, finite-sum
  Bochner transport assembles the horizon, and exact score recursion rewrites
  sampled-action updates as the actual `p_(t+1)` selector. Thus the expected
  displayed successor stability sum is bounded by the integrated half-power
  budget under explicit policy-law, measurability, integrability, and score
  recursion contracts. Downstream modules now construct the canonical
  trajectory, discharge selector regularity, and consume this theorem in the
  compiled estimated-to-environment regret endpoint. Self-bounding,
  comparator specialization, tuning, and final regret remain open.
- `ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses` and
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `INT-REWARD-BOUNDED` /
  `ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` now compiles locally across
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail`.
- `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` now compiles locally in
  `BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail`.
- `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` now compiles locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence`.
- `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` and
  `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` now compile locally in
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`.
- `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
  `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` now compile locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` and
  `ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND` now compile locally
  in `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`.
- `ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` now compiles locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`.
- `ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
  `ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` now compile locally in
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE` now compiles
  locally in `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`.
- `ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` now compiles locally in
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.
- `ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally in
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` now compiles locally
  in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` now compiles
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` now compiles
  locally in `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` now compiles locally in
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`.
- `MEAS-POLICY` now compiles locally in
  `BanditRLProof.PolicyMeasurability` as a measurable policy/state composition
  surface with arbitrary-filtration and generated-history-filtration
  specializations.
- `POLICY-GENERATED-ACTION-TRACE-MEASURABILITY` now compiles locally in
  `BanditRLProof.PolicyMeasurability` as policy-generated action-trace
  coordinate measurability from a time-indexed measurable state process.
- `KERNEL-REWARD` now compiles locally in `BanditRLProof.RewardKernel` as a
  Mathlib-backed reward-kernel contract surface: arm/context-indexed Markov
  reward laws, selected-measure probability, event-probability measurability,
  and policy/state selected-measure wrappers are available.
- `POSTERIOR-KERNEL` now compiles locally in
  `BanditRLProof.PosteriorKernel` as a Mathlib-backed posterior-kernel contract
  surface: histories index probability measures over environments, measurable
  and countable-history selector constructors are available, and a
  prior/likelihood/posterior surface is named. The canonical subroute now also
  wraps Mathlib `posterior likelihood prior` and proves it equals
  `condDistrib env history` whenever the source environment/history pair law is
  `prior ⊗ₘ likelihood`; arbitrary posterior surfaces, actual trajectory laws,
  Thompson sampling, and Bayesian regret remain separate.
- `TS-POSTERIOR-ACTION-IDENTITY-LEDGER` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: a posterior kernel, Thompson action
  kernel, measurable environment-to-best-action map, and event-level
  probability-matching equality are packaged as a source contract, with
  event-level and singleton action-probability consumers.  This still consumes
  the posterior action law; it does not prove Bayes' rule, construct the
  posterior sampler, import LML, or prove Bayesian regret.
- `TS-POSTERIOR-BEST-ACTION-MEASURABILITY` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: for countable singleton-measurable
  environment spaces, any `bestAction : Env -> Action` is measurable by
  Mathlib `measurable_of_countable`, and the posterior-action identity ledger
  can be built without a separate best-action measurability proof.  This
  discharges the finite/countable best-action regularity side condition, but
  the posterior action-law identity itself remains assumed.
- `TS-POSTERIOR-ACTION-CONDDISTRIB` now compiles locally in
  `BanditRLProof.Algorithms.Thompson`: the Thompson action conditional law is
  identified with `posterior.kernel.map bestAction`, the supplied posterior
  kernel/environment `condDistrib` equality is mapped through `bestAction`, and
  Mathlib `condDistrib_comp` yields the conditional law of the random best
  action. This generic local counterpart of pinned LML
  `Bandits.TS.hasCondDistrib_action` still accepts the posterior equality as a
  premise; downstream canonical pair-law and algorithm-density leaves now
  produce it. Concrete recursive density-law construction, global trace
  coupling, regret decomposition, and concentration remain open.
- `TS-CANONICAL-POSTERIOR-PAIR-LAW` now compiles locally across
  `BanditRLProof.PosteriorKernel` and `BanditRLProof.Algorithms.Thompson`:
  Mathlib's canonical posterior compProd identity and conditional-distribution
  uniqueness produce the environment posterior from an exact pair pushforward;
  the generic Thompson theorem then needs only the next-action law
  `condDistrib nextAction history = canonicalPosterior.map bestAction`.
  Canonical `Env × History` product sources discharge the pair law directly.
  The canonical sampler leaf below discharges the remaining action law.
- `TS-CANONICAL-SAMPLER-PROB-MATCH` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonCanonicalSampler`: the mapped canonical
  posterior is lifted to the environment/history pair and composed with the
  canonical joint law. `Measure.fst_compProd` and a finite-measure
  history/action marginal transport construct both generic law premises, so
  the one-step theorem has no pair-law or action-law hypothesis. The downstream
  reference-policy and algorithm-density leaves connect this one-step logic to
  process-facing history laws.
- `TS-REFERENCE-POSTERIOR-POLICY-SAMPLER` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonReferencePolicy`: following the pinned LML
  non-circular policy design, a fixed reference-process posterior is mapped
  through `bestAction`; the actual next action is sampled with `compProd` after
  a history `Kernel.comap`. The module proves the history/action law, the action
  `condDistrib`, preservation of every measurable base marginal, and
  preservation of the environment posterior after adjoining the action. Its
  finite action/reward-prefix endpoint therefore needs only
  reference-versus-actual posterior invariance. The downstream
  algorithm-density leaf now produces that invariance from matching marginal
  and joint density laws.
- `TS-ALGORITHM-DENSITY-POSTERIOR-INVARIANCE` now compiles locally in
  `BanditRLProof.Algorithms.ThompsonAlgorithmDensity`: an
  `AlgorithmDensityPosteriorSource` records that the actual history marginal
  and actual history/environment joint law are the corresponding reference
  laws weighted by one measurable history density. The generic
  `compProd_withDensity_left` lemma commutes that density through the reference
  posterior composition product; `condDistrib` uniqueness proves posterior
  invariance, and generic plus finite-pair endpoints immediately close
  reference-policy probability matching without posterior or action-law
  assumptions.
- `TS-CONDITIONAL-HISTORY-DENSITY-SOURCE` now compiles in the same module:
  equal actual/reference environment marginals and one a.e. conditional-history
  kernel density law construct both `AlgorithmDensityPosteriorSource`
  pushforward equalities using `condDistrib_comp_map`, `compProd`,
  `withDensity`, and coordinate swap. Generic and finite-pair consumers close
  probability matching directly. The recursive finite-history process theorem,
  its environment-indexed `condDistrib id` transport, and the four-family
  conditional split-source constructor now compile downstream. The canonical
  trajectory leaf now builds each fixed-environment pair `trajMeasure`, proves
  its combined and split process laws, identifies the full conditional sample
  law of `prior compProd trajectoryKernel`, and closes finite-prefix probability
  matching for supplied Markov trajectory-kernel families with canonical
  pointwise values. `ThompsonMeasurableTrajectory` now constructs those
  environment-indexed Markov kernels directly from jointly measurable feedback
  data using Mathlib `Kernel.traj`. The fixed-environment support theorem and
  projected prefix/next composition-product identity now prove the shifted pair
  `condDistrib` law; projective-limit uniqueness gives pointwise canonical
  equality, and the endpoint closes finite-prefix probability matching with no
  supplied kernel or process-law premise. `ThompsonRecursiveSampler` now also
  couples those policies into one non-circular uniform-reference Thompson
  `HistoryAlgorithm`, transports the fixed-environment action law through the
  prior, discharges finite-action AC by uniform full support, and proves
  probability matching for the same trajectory's successor action.
  `ThompsonBayesRegretDecomposition` transports that probability matching
  through arbitrary measurable history/action scores, and
  `ThompsonClippedUCBScore` now instantiates the exact pinned clipped score,
  proves its finite-history/trace identity and range regularity, and closes all
  decomposition integrability contracts. `ThompsonStationaryReward` now maps
  stationary environment/action reward kernels to independent latent arm
  streams, proves arbitrary-action adaptive-count upper/lower tails, and
  exposes the table through measurable next-unused deterministic feedback.
  The deterministic-support route now compiles as well: every canonical
  trajectory reward equals `rewardFromArmStream` almost everywhere, generic
  `IdentDistrib` wrappers retain arbitrary algorithm randomness, and the
  stationary environment-indexed augmented trajectory kernel has fixed-arm
  upper/lower adaptive-count tails. Next mix these pointwise laws through the
  augmented prior and derive measurable clipped-confidence events. The two
  concentration expectations and final Bayesian regret inequality remain
  separate.
- `POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` now compiles locally in
  `BanditRLProof.RewardKernel`: a measurable policy plus a context/action
  Markov reward kernel gives a context/state Markov reward kernel, with
  measurable event probabilities.
- `POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` now compiles locally in
  `BanditRLProof.RewardKernel`: time-indexed measurable policies plus
  measurable context/state extractors from `Finset.Iic` reward histories give
  Mathlib `partialTraj` finite-prefix reward-history kernels.
- `KERNEL-POLICY-BIND` now compiles locally in `BanditRLProof.RewardKernel`:
  deterministic policy action kernels product with selected reward kernels to
  produce one-step `(Action × Reward)` kernels, and Mathlib `partialTraj`
  assembles finite-prefix action/reward pair trajectory kernels.  The one-step
  and history-step action/reward kernels also expose selected-reward marginal
  wrappers, and one-step `partialTraj` extensions expose their next-coordinate
  step-kernel marginal.
- `KERNEL-REWARD-MAP-LAW-TRANSFER` now compiles locally in
  `BanditRLProof.RewardKernel`: the one-step and history-step action/reward
  kernels push forward along `Prod.snd` to the selected reward measure.  This
  is the measure-level counterpart of the selected-reward event marginals and
  matches the map-law shape consumed by the `COND-EXPECT-REWARD` route.
- The fixed-action bounded/source conditional-MGF route now assembles
  `CenteredRewardCondSubGaussianWitnesses`, the pairwise tail contract, and the
  argmax wrong-commit probability consumer.  The canonical-tail variant now
  removes the explicit tail-domination hypothesis for this fixed
  `actionWithCommit` route, and the infinite-product source specialization is
  also compiled.  The policy/state, policy-generated action-trace,
  finite-history product measurability, reward-kernel regularity, one-step
  policy/reward Markov-kernel composition, finite-prefix reward-history
  `partialTraj`, finite-prefix action/reward pair trajectory kernels,
  selected-reward event and `Measure.map` marginal wrappers, one-step
  `partialTraj` next-coordinate marginal wrappers, and kernel-level
  centered-reward law transfer are compiled; the next layer is
  `partialTraj`/history-to-`condExpKernel`
  reward-law identification, Bayes-rule posterior identification, and final adaptive theorem assembly if moving beyond fixed
  product-coordinate
  `actionWithCommit`.
- The next direction is not another broad deterministic suffix simplification.
- The next proof-design layer is wrong-commit probability, starting with
  event reduction and measurability leaves.
- `research-wiki/open-problems/etc-wrong-commit-probability-design.md` is the
  current theorem card for that bridge.
- Extended Pro then chose `ETC.measurableSet_commitArm_ne_bestArm`; that leaf
  now compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`;
  that pure event-reduction leaf now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`; that
  measure monotonicity wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose `ETC.measurableSet_empMean_ge_empMean`; that
  pairwise empirical-mean comparison-event measurability canary now compiles
  locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`; that finite
  existential wrong-mean event measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`; that finite-union
  probability upper-bound wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`; that final
  elementary event-probability assembly now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`; that abstract
  pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`; that if-zeroed
  nonbest pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`; that
  filtered-sum pairwise-tail consumer wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then chose
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`; that
  deterministic Nat-level denominator-positivity leaf now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`; that
  Rat denominator adapter now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero`;
  that Rat nonzero-denominator adapter now compiles locally in
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Extended Pro then chose `ETC.empMeanAtExploration` and
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`; that
  deterministic empirical-mean API now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMean`.
- Extended Pro then chose
  `ETC.measurable_sumRewards_actionWithCommit_exploration`; that
  numerator-measurability bridge now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`.
- Extended Pro then chose
  `ETC.measurable_empMeanAtExploration_of_measurable_div_const`; that full
  empirical-mean measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability` under an explicit
  Rat division-by-constant measurability contract.
- Extended Pro then chose `measurable_rat_div_const`; that Rat
  division-by-constant measurability wrapper now compiles locally in
  `BanditRLProof.RatMeasurability` under `[MeasurableSingletonClass Rat]`.
- `ETC.measurable_empMeanAtExploration` now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `measurable_rat_div_const` to remove the explicit `hdiv_const` argument.
- Extended Pro then chose
  `ETC.measurable_empMeanAtExploration_coordinates`; that coordinate-shaped
  empirical-mean measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`.
- The next plausible leaf from that same Extended Pro response,
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`, now
  compiles locally in `BanditRLProof.Algorithms.ETCMeasurability` as an
  abstract commit-oracle argmax consumer.
- Extended Pro then selected Candidate A,
  `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`; that
  oracle-specialized pairwise-tail probability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate B,
  `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`; that
  oracle-specialized filtered-sum probability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`; that
  oracle-specialized if-zeroed nonbest probability wrapper now compiles
  locally in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC.measurableSet_commitOracle_ne_bestArm`; that oracle-selected
  wrong-event measurability wrapper now compiles locally in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate C,
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`, and its local compiled
  candidate `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`
  now compiles in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`; the local declaration
  `ETC.measurable_empMeanVector_of_forall_measurable` now compiles in
  `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`; the local
  declaration
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean` now
  compiles in `BanditRLProof.Algorithms.ETCMeasurability`.
- Extended Pro then selected Candidate A,
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`; the local
  declaration
  `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`
  now compiles in `BanditRLProof.Algorithms.ETCMeasurability`.

## Reward-Only Canonical Conditional Law Increment

- `RewardKernel.instIsMarkovKernel_historyStepKernelFamily` now exposes the
  existing reward-history step-family Markov proof to Mathlib trajectory APIs.
- `ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure`
  now proves the selected-reward `condExpKernel.map` law on the canonical
  reward-only Ionescu-Tulcea trajectory measure.  The proof uses Mathlib
  `Kernel.condDistrib_trajMeasure`, the compiled countable-target bridge, and
  `RewardKernel.historyStepKernelFamily_apply`; it does not consume a packaged
  generated random-pair law.
- The contracts are standard Borel/countable reward regularity, a probability
  initial reward measure, and measurable policy context/state inputs.  The
  leaf is project-local and compiled with an external canary.
- The reward-prefix/generated finite-pair-prefix alignment is now compiled:
  the two prefixes induce equal comap measurable spaces,
  `History.historyFiltrationSucc` reduces to the reward-prefix comap, and the
  canonical selected-reward law is exposed on the generated finite-pair
  surface.
- `ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim`
  now proves the required trim strengthening soundly: singleton event
  probabilities on both sides are conditioning-measurable, so Mathlib
  `ae_eq_trim_of_measurable` applies before countable singleton extensionality.
  This is not a reversal of `ae_of_ae_trim`.
- The trim bridge is specialized to the reward-only `historyStepKernelFamily`
  trajectory measure, transported through the generated finite-pair comap,
  and consumed by
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_trajMeasure`.
  The canonical reward-only process therefore constructs
  `GeneratedActionSelectedRewardFinitePairHistoryLawSource` without an assumed
  selected-reward law.
- `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure`
  now converts that selected source through the deterministic generated-action
  split, and
  `historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_trajMeasure`
  proves the full theorem-shaped successor finite-pair conditional law on the
  canonical reward-only process.  This endpoint no longer assumes an ambient
  selected-reward, random-pair, or partialTraj source.
- `historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure`
  now consumes this full law together with `CenteredRewardKernelLaw` and
  explicit ambient centered-reward integrability to prove the canonical
  successor conditional mean-zero theorem.  It does not require the practical
  source's pointwise raw bounds, which are generally unsuitable for the full
  ambient space `Nat -> Rat`.
- `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure`
  now reaches the canonical concentration interface.  Measurable mean derives
  centered measurability, a finite-history ceiling derives trim-a.e. variance
  domination, and the integrated target-law transfer derives all-real ambient
  exponential integrability from the selected kernel MGF laws.  The theorem no
  longer accepts an ambient `h_integrable_exp` premise.
- The transfer is compiled generically in
  `hasCondSubgaussianMGF_of_condExpKernel_map_eq`: target-wise integrability and
  the common MGF ceiling feed `Measure.integrable_comp_iff`, with the inner norm
  integral bounded over the finite trim measure.  The same strengthening is
  exposed by centered, bounded, definitional, and practical raw-range source
  consumers.
- `generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted`
  now proves the zero-initialized successor centered-reward process adapted to
  generated shifted history.  The index-zero value is deterministic zero, so
  Mathlib's unconditional first-summand contract is discharged without adding
  an artificial initial reward law.
- `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure`
  combines that adaptedness, the canonical successor conditional-MGF witnesses,
  and `condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` into a canonical
  ENNReal Azuma-Hoeffding bound for the `Finset.range n` sum of centered rewards
  at indices `1..n-1`.
- `historyStepKernelFamily_centeredRewardSuccProcess_average_tail_ennreal_trajMeasure`
  now turns that sum tail into a canonical aggregate average tail: `m > 0`
  rewrites `eps <= sum / m` to `m * eps <= sum`, and `Finset.range (m + 1)`
  still contains exactly successors `1..m` because index zero is deterministic.
  It is deliberately not an arm-wise empirical-mean or confidence-radius
  theorem.  The complete-trace ambient transport route now compiles as
  `historyStepKernelFamily_selectedMeasure_condExpKernel_map_of_identDistrib_trajMeasure_trim`
  and
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_identDistrib_trajMeasure`:
  ambient reward-trace `IdentDistrib` with canonical `trajMeasure` transports
  the prefix/next joint law, recovers the ambient conditional distribution,
  and constructs the generated selected source that feeds the existing full
  `partialTraj` converter.  The recursive entry route now compiles as
  `historyStepKernelFamily_identDistrib_trajMeasure_of_condDistrib`,
  `historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_of_condDistrib`,
  and `historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_of_condDistrib`:
  an initial reward marginal and all successor `condDistrib` laws determine the
  complete trajectory law, selected source, and full generated `partialTraj`
  source.  The generic uniqueness proof now lives in the foundation module
  `BanditRLProof.RewardTraceLaw`.  This route now reaches a concrete ambient
  concentration theorem:
  `centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource`
  derives the conditional MGF directly from the full source without raw/mean
  range bounds;
  `historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_of_condDistrib`
  specializes it to recursive laws; and
  `historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_of_condDistrib`
  derives ambient probability from the initial law, proves strong adaptedness,
  and returns the ENNReal Azuma-Hoeffding sum tail.  The next route is to derive
  those recursive conditional laws from a concrete algorithm/environment or
  align this tail with an arm/sample-count confidence surface; the `COND-EXPECT-REWARD`
  conversion-window and proof-obligation files mentioned by the retrieval
  index are currently absent and must be restored before their metadata is
  used.  The arbitrary-ambient `partialTraj` theorem-card row and final
  adaptive theorem remain open.

## ETC Next Leaf

The canonical bounded-Rat per-arm expected-regret endpoint and its external
exploration-prefix transport now compile. Equal prefix pushforwards through
`m*K-1` give equal generated ETC regret integrals, so the external law inherits
the same gap-weighted armwise tails without a max-gap union, full trajectory
equality, or suffix laws. An initial reward marginal plus successor
`condDistrib` laws now derive this prefix identity and return the per-arm RHS
directly on the original sample space. The scheduled exploration-arm wrapper
also compiles: it fixes the irrelevant context to `Unit`, rewrites the local
step kernel to the stationary arm law, and exposes no local kernel plumbing.
The full action/reward-history constant-law adapter now also compiles: it
projects complete pair-history/next-action conditions to reward prefixes and
extracts the initial marginal without changing the per-arm RHS. The raw
action-selected feedback-kernel adapter now also compiles, using a.e. scheduled
exploration actions and preserving the per-arm conclusion. This closes the
dependency-light bounded-Rat law route. The canonical concentration layer now
also compiles from direct per-arm centered `HasSubgaussianMGF` witnesses at a
common proxy: it builds the kernel law, generated/fixed-filtration reward
witnesses, and exact pairwise empirical-mean tail contract without bounded
support. That contract now also feeds concrete non-best commit fibers, named
finite Real tails, and the canonical gap-weighted per-arm Bochner expected-
regret theorem, with no max-gap collapse or arm union. Its exploration-prefix,
generic initial/successor conditional-law, and scheduled exploration-arm
consumers now also compile on arbitrary external reward processes. The public
scheduled endpoint fixes `Context := Unit` and requires neither bounded support
nor a caller-visible local kernel. The LML-shaped full action/reward-history
direct-MGF adapter now also compiles by marginalizing the initial constant law
and coarsening each complete pair-history/next-action condition to the reward
prefix. The action-dependent selected-kernel adapter now also compiles: raw
action-indexed kernels plus scheduled-action a.e. identities reduce to those
constant laws without changing the per-arm RHS. This closes dependency-light
direct-MGF `Rat` law transport. The new Real scalar regret/pull-count leaf below
closes the target-side bookkeeping mismatch, and its stationary-kernel
specialization now also compiles. The Real ETC count-to-probability endpoint
now compiles too: measurable `actionWithCommit` pull counts are integrable and
their expectation is exactly `m + (n - K*m) * P(commit=a)`. The canonical Rat
arm-law route now also compiles the exact LML exponential constant and the
matching per-arm expected-count bound. The canonical native Real
`Measure.infinitePi` route now compiles the same single-arm tail, expected
count, kernel gap, and full finite-sum regret bound directly for a Markov Real
kernel. Native Real finite-prefix factorization and external process transport
now compile too, including a direct scheduled-arm initial/successor
`condDistrib` endpoint. The next narrow route is mapping the actual
`IsAlgEnvSeq` stationary-environment fields to those compiled premises plus
upstream measurable-argmax action/tie equivalence; direct LML integration is
now the remaining source boundary rather than an optional concentration path.

## Exact ETC Route Update: Real Mean Regret

The completed `REAL-MEAN-REGRET-PULLCOUNT` leaf provides the exact-route Real
scalar bookkeeping surface in `BanditRLProof.RealMeanRegretPullCount`.
`integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount` rewrites the
Bochner expectation of `n * iSup mean - sum mean(action)` as the finite sum of
each `realMeanGap` times the expected pull count. It uses existing finite-sum,
fiber-cardinality, integrability, and Bochner wrappers and requires only
per-arm pull-count integrability.

That stationary Real reward-kernel specialization now compiles in
`BanditRLProof.RealKernelRegretPullCount`, including nonnegative kernel gaps and
the kernel-facing Bochner pull-count equality. The downstream
`REAL-ETC-EXPECTED-PULLCOUNT` leaf now closes pull-count integrability, exact
commit-fiber indicator integration, and the abstract probability-bound
consumer. `ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT` now also
closes the exact `exp (-m*gap^2/(4*sigma2))` arithmetic, canonical Rat-arm-law
commit-fiber bound, and matching per-arm expected-count endpoint.
`ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET` now maps those laws to a Markov Real
kernel, identifies its identity-integral gaps, and closes the full finite-sum
regret assembly. `ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT` now additionally
defines the Real exploration means and deterministic finite argmax directly,
proves their measurability without a countability assumption on Real score
vectors, and connects the resulting action to the exact expected-count
consumer. `ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET` now closes the native Real
canonical product-law concentration route through the exact full finite sum,
using `iIndepFun_infinitePi`, coordinate map laws, the common centered MGF
contract, and the existing Real kernel regret decomposition.
`ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET` now factors the entire
native action/regret through `Fin (m*K)` rewards, transports equal prefix laws,
and derives that equality directly from scheduled-arm initial and successor
conditional laws. `ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET` now
also maps the upstream-shaped action-selected initial and complete pair-history
successor feedback laws into those scheduled laws, preserving the exact Real
finite-sum conclusion.

`ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET` now identifies the strict
fold with Mathlib `List.argmax`, proves equality with the LML-shaped least-
encode `Nat.find` selector, combines round-robin exploration, commit, and
persistence into action equality, and consumes the selected feedback laws for
the exact native Real finite sum.

`ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET` now mirrors the upstream
finite-history count/sum/mean surface, proves the `K*m-1` history score equals
the local exploration score under `ETC.arm_of_lt`-shaped action equality, and
feeds a history-shaped commit law directly into the exact finite-sum theorem.

`ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET` now packages the precise
measurability, three-phase action, and stationary feedback-law consequences in
`ETC.RealStationaryETCSequence`. Its theorem projects that bundle into the
history-score endpoint and returns the exact LML-shaped finite sum.

The next narrow boundary is no longer mathematical field compatibility. It is
a task-level decision about importing actual LML symbols across ABRL's Lean/
mathlib `v4.29.1` and pinned LML's Lean `v4.32.0-rc1` toolchains. Any attempt
must isolate the dependency/toolchain and symbol-identity work; do not reopen
history arithmetic, tie semantics, reward laws, concentration, constants,
gaps, or finite sums, and do not call the upstream theorem imported meanwhile.

The active UCB theorem route now also advances through
`UCB-NATIVE-REAL-HISTORY-INDEX`. The new module compiles the exact Real
empirical mean, sample-path-dependent pull-count width, finite-history score,
least-encoded score action, measurability, maximality, and history/trace
alignment used by pinned `Bandits.UCB.regret_le`.

`UCB-FIXED-COUNT-PEELING-LAW` now compiles the source-faithful next stage. A
`FixedArmPrefixSource` records that selected rewards from an arm are exactly
the first `pullCount` entries of a latent arm stream. The adaptive pair event
is peeled over `k <= n` with the finite outer-measure union bound, and one
complete-stream `IdentDistrib` law transports all fixed-count events to a
canonical stream.

`UCB-ARM-STREAM-REWARD-SOURCE` now compiles the next-unused-coordinate part of
LML's array/stream model. For any action trace on a latent arm stream,
`rewardFromArmStream` reads the selected arm at its prior pull count, and a
horizon induction proves the exact selected-sum/prefix invariant. General
measurable and canonical adapters feed this construction directly into the
compiled peeling theorem.

`UCB-ARM-STREAM-PROCESS-LAW` now constructs the recursive source-faithful UCB
action, exact actual finite history, next-unused rewards, and canonical
stationary product arm-stream measure. `UCB-ARM-STREAM-INDEX-TAIL` specializes
product independence and fixed-sum sub-Gaussian concentration through positive
count peeling to the actual random-width lower/upper index events, ending at
the LML-shaped outer-measure bound `1 / (n+1)^(c-1)`.

`UCB-ARM-STREAM-EXPECTED-PULLCOUNT` closes recursive finite-history/action/
reward measurability and the actual-width count consumer. It proves positive
initial counts, deterministic score/gap threshold algebra, the selected-large
bad-event union, its `2*constSum` measure sum, and the ENNReal lower-integral
bound with threshold `ceil(8*c*sigma2*log(n+1)/gap^2)+1`. It also proves
pull-count integrability and converts that endpoint to the exact LML-shaped
Real Bochner expected-count bound.

`UCB-ARM-STREAM-LML-REGRET` now compiles the complete canonical recursive UCB
theorem with the exact pinned gap-weighted finite-sum RHS. The only remaining
generic-process step, `UCB-EXTERNAL-ACTION-LAW-LML-REGRET`, also compiles: an
external action process with complete trace law `IdentDistrib` to the canonical
process inherits exactly the same RHS through measurable regret composition
and integral transport. `UCB-EXTERNAL-ARM-STREAM-SOURCE-LAW-LML-REGRET` now
constructs that action law from a latent arm stream with canonical complete law
and a.e. recursive action generation, but the pinned-source audit shows this is
an optional stronger adapter rather than the `IsAlgEnvSeq` route.
`UCB-EXTERNAL-ACTION-REWARD-TRAJECTORY-LAW-LML-REGRET` now compiles the faithful
route endpoint: complete observable pair-trajectory `IdentDistrib` projects to
the canonical action law and exact RHS.
`UCB-COMMON-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now constructs that complete
law from a common initial pair marginal and all common successor pair
`condDistrib` kernels. Its generic support proves full trace-law equality from
finite-prefix laws using Mathlib projective-limit uniqueness.
`UCB-CANONICAL-ACTION-REWARD-CONDDISTRIB-LML-REGRET` now removes the exposed
common-law bundle by choosing the canonical time-zero pushforward and canonical
regular conditional kernels internally. Remaining work is to derive the
external initial/successor equalities from upstream environment/action
contracts or import the literal trajectory witness. Do not reconstruct unused
arm arrays or substitute the deterministic proxy route.
## Latest UCB Compatibility Leaf

`UCB-ISALGENVSEQ-SPLIT-LAWS-LML-REGRET` is compiled. The route now accepts the
initial action law, initial feedback conditional law, successor action policy,
and successor feedback conditional law separately, combines them by
`Kernel.compProd`, obtains full observable trajectory `IdentDistrib`, and
returns the exact pinned UCB regret RHS. The next narrow UCB leaf is a concrete
producer for those four fields or a deliberate LML toolchain import decision;
do not reopen concentration or reconstruct latent unused-arm arrays.

The follow-on field compatibility theorem is also compiled in
`UCBRealLMLCompat`: `RealStationaryUCBSequence` bundles the source-shaped
fields, the canonical arm-stream process proves the bundle is inhabited, and
`regret_le_of_realStationaryUCBSequence` gives the exact pinned RHS. The next
UCB work item must therefore be a real external producer/import, not another
adapter around the same assumptions.

## Latest Thompson Process Leaf

`LOCAL-LEAF-TS-RECURSIVE-FINITE-HISTORY-DENSITY` is compiled. The new
`HistoryAlgorithm`/`HistoryEnvironment` process contract accepts separate
initial and successor action/feedback laws, assembles their pair kernels, and
proves by induction that every finite pair-history law is the reference law
weighted by `historyDensity`. This is the theorem-level local analogue of
the pinned LML algorithm-density process theorem.

The conditional-on-environment realization now also compiles:
`ConditionalHistoryAlgorithmDensitySource` requires the actual/reference
`condDistrib id` sample laws to satisfy the process contracts a.e.;
`condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource`
derives the conditional history law, and the direct consumer closes
finite-prefix Thompson probability matching.

The split-law producer layer now compiles as well.
`ConditionalHistoryAlgorithmEnvironmentSplitSource` records the initial action,
initial feedback, successor policy, and successor feedback laws under each
conditional sample measure. `conditionalHistoryAlgorithmDensitySource_of_split`
gathers the Nat-indexed laws with `ae_all_iff`, assembles both process contracts,
and the direct split-source consumer closes finite-prefix probability matching.

Next build one concrete recursive TS/reference trajectory that proves those four
split fields, then establish global sampler coupling. Do not re-assume the
combined process or density law, add pointwise RN-finiteness, or jump to
Bayesian regret.

## Latest Thompson Concentration Leaf

`LOCAL-LEAF-TS-STATIONARY-EMPIRICAL-MEAN-TAIL-TRANSPORT` is compiled. The
stationary latent-stream route now reaches the decomposition-facing canonical
trajectory measure: augmented-prior mixing, positive-count peeling, clipped
radius algebra, exact finite exponential summation, and product-associativity
transport yield both fixed-arm empirical-mean confidence failures with bound
`n * delta`.

The next single leaf is `TS-CLIPPED-UCB-CONCENTRATION-EXPECTATIONS`. It must
turn those fixed-arm events into finite arm/time controls and the two clipped
score expectations in `integral_trajectoryBayesMeanRegret_eq_add_clippedUCB`.
Do not reopen latent-stream support, stationary kernel laws, zero-count
peeling, prior mixing, posterior matching, or the decomposition.

## Latest Thompson Horizon Leaf

`LOCAL-LEAF-TS-STATIONARY-SELECTED-ARM-HORIZON-LOWER-TAIL` is compiled. The
stationary canonical trajectory now has a measurable environment-dependent arm
horizon lower-tail bound of `(n - 1) * delta`. Times are collapsed by realized
pull count on the latent stream before the finite union, preserving the pinned
LML constant.

The best-action-minus-clipped-UCB finite-horizon expectation bound now compiles;
the next single leaf is the selected-action clipped-UCB-minus-mean expectation.
It must combine a deterministic clipped-score summation inequality with a
finite-arm horizon upper-confidence event, without reopening the lower-tail
transport proved here.

## Latest Thompson Expectation Theorem

`LOCAL-LEAF-TS-CLIPPED-UCB-BEST-ACTION-EXPECTATION` is compiled with the exact
bound `(u-l) * (n-1) * n * delta`. It consumes the measurable best-action
horizon lower tail, splits the canonical integral into bad-event/complement
pieces, and uses the existing `[l,u]` score and mean contracts.

The next theorem is the selected-action clipped-UCB-minus-mean expectation.
Required supporting obligations are now explicit: a pathwise finite-horizon
clipped-UCB sum inequality and a finite-arm horizon upper-confidence event with
cost `K * (n-1) * delta`. After that theorem, combine both expectations with
the compiled Thompson decomposition.

## Latest Thompson Stationary Final Theorem

The selected-action expectation and stationary `TS-FINAL` route now compile.
The deterministic leaf reindexes the time sum by arm/pull count and bounds the
confidence widths; the probability leaf collapses bad times by realized count
before unioning over arms, preserving the exact `K*(n-1)*delta` cost. The
second expectation therefore matches pinned LML, and the general-`delta`
decomposition join is compiled.

The endpoint
`stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le`
uses `delta = 1/n^2` and proves
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)`. The next Thompson work must be a
genuinely broader model adapter or literal cross-toolchain LML import; do not
create another wrapper around this same stationary theorem or claim it covers
nonstationary, contextual, or RL settings.

### EXP3 route update: observed roundwise moments

`BanditRLProof.Exp3PredictableMoments` closes the next concrete EXP3 route
step. Its public theorem
`sampledPredictableObservedSuccessor_first_second_moment` states the one-round
first and second estimator moments directly in terms of the scalar reward
stored in the sampled trajectory, while the right sides expose the full
predictable loss vector. Supporting compiled APIs cover global next-pair
`condDistrib`, initial/successor deterministic feedback support, the retained
`(Env,prefix)` finite-action source, and the `gamma / |arms|` regularity floor.
The finite-horizon integral summation now compiles. Its sampled-Hedge,
exploration-bias, integrability, and expected-regret consumers also compile
downstream, including the tuned square-root theorem.

### EXP3 sampled Hedge route update

`EXP3-SAMPLED-HEDGE` is compiled in `BanditRLProof.Exp3SampledHedge`. The
inclusive sampled score now agrees with deterministic Hedge cumulative loss
at the correctly shifted `n + 1` index; the pure Hedge distribution agrees
with normalized sampled-score weights; and the concrete trajectory
probability is explicitly their uniform exploration mixture. Under pathwise
nonnegative scalar feedback, `sampledHistoryScore_hedge_regret_le` supplies the
finite-horizon second-order comparator inequality. The route uses the existing
sampled-score recursion, `Preorder.frestrictLe`, `cumulativeLoss_succ`, finite
sum congruence, and the compiled generalized Hedge theorem. Next work should
assemble one finite-horizon a.e. `[0,1]` reward-support event, prove the
pure-Hedge/exploration-mixed bias inequalities, and integrate; parameter
optimization and the final EXP3 theorem remain later.

### EXP3 predictable Hedge a.e. update

`EXP3-PREDICTABLE-HEDGE-AE` is compiled. Existing time-zero and successor
selected-feedback laws now yield one common finite-horizon a.e. event on which
all observed rewards are nonnegative. The generated sampled trajectory
therefore satisfies the concrete second-order Hedge inequality almost surely,
with either `cumulativeLoss` or inclusive `sampledHistoryScore` as comparator
surface. This closes the reward-sign law transport. The next theorem route is
the deterministic exploration bridge: compare pure Hedge `q_t` terms against
the actual mixture `p_t = (1-gamma)q_t + gamma/|A|`, establish integrability,
and combine those facts with the finite-horizon moment theorem. Eta/gamma
optimization remains after the integrated bound.

### EXP3 exploration-bias update

`EXP3-EXPLORATION-BIAS` is compiled in
`BanditRLProof.Exp3ExplorationBias`. The concrete exploration mixture now
yields the coordinate comparison `q_t(a) <= p_t(a)/(1-gamma)`, the resulting
pure-q versus explored-p estimator-square bound, and the predictable-loss
bias `p_t dot loss_t <= q_t dot loss_t + gamma`. One finite-horizon theorem
sums both pathwise inequalities. It needs only finite nonempty arms,
decidable equality, the predictable `[0,1]` contract, and
`0 <= gamma < 1`; it has no measure or integrability premise. The next narrow
route was adaptive pure-q first-moment transport plus integrability on the
generated trajectory law; that bridge, the integrated expected-regret consumer,
the large-horizon eta/gamma square-root optimization, the realized selected-loss
expectation adapter, and the uniform-horizon clipped-rate consumer now compile.

### EXP3 predictable expected-regret update

`EXP3-PREDICTABLE-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3PredictableIntegration`. The generated predictable EXP3
trajectory now satisfies
`E[sum_t p_t dot loss_t - sum_t loss_t(comparator)] <= log|A|/eta +
eta/(1-gamma)*|A|*T + gamma*T`. The proof uses the new cross-weight identity
`E_p[q dot hat-loss] = q dot loss`, conditional-law transport, measurable
pure-Hedge sources, finite-horizon Bochner integration, the a.e. sampled-Hedge
bound, exploration bias, and the exact estimator second moment.

The theorem requires a probability prior, Standard Borel environment/action,
measurable action singletons, finite nonempty arms, predictable measurable
`[0,1]` losses, a supported comparator, `eta > 0`, and `0 < gamma < 1`; it does
not assume independence, stationarity, oblivious losses, or concentration.
The route is root-imported and externally instantiated in `Tests.Basic`.
Retrieval is recorded by `LOCAL-LEAF-EXP3-PREDICTABLE-EXPECTED-REGRET` and its
Mathlib/local/paper dependencies. Its deterministic parameter and square-root
consumers now compile; do not reopen the law or integrability layers. The
realized selected-loss adapter and uniform-horizon clipped-rate endpoint also
compile downstream.

### EXP3 tuned expected-regret update

`EXP3-TUNED-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3ExpectedRegret`. First,
`expectedRegretBudget_le_four_mul_gamma_mul_horizon` proves the abstract
`4*gamma*T` simplification for `eta=gamma/K`, `gamma<=1/2`, and
`K*log K<=gamma^2*T`. Then `tunedExplorationRate=sqrt(K*log K/T)` and
`tunedLearningRate=gamma/K` are shown positive, within the exploration cap,
and algebraically equivalent to the `sqrt(K*T*log K)` scale. The public
generated-process theorem gives expected predictable regret at most
`4*sqrt(K*T*log K)` when `2<=K`, `0<T`, and `4*K*log K<=T`.

The proof adds only Mathlib Real log/sqrt and ordered-field algebra to the
compiled expectation route; probability, measurability, integrability, and
law assumptions are unchanged. Root import and a complete external canary
compile. The realized selected-loss and uniform-horizon clipped-rate
presentation adapters also compile downstream.

### EXP3 realized expected-regret update

`EXP3-REALIZED-EXPECTED-REGRET` is compiled in
`BanditRLProof.Exp3RealizedRegret`. It defines the actual generated scalar loss,
uses the existing deterministic-feedback law to identify it almost surely with
the selected predictable coordinate, and transports the initial/successor
sampled-action conditional laws into the one-round identity
`E[loss_t(A_t)] = E[p_t dot loss_t]`. Finite-horizon Bochner summation then
rewrites the compiled unoptimized and tuned expected-regret theorems.

The public endpoints cover both the original unoptimized budget and the
large-horizon `4*sqrt(K*T*log K)` bound for actual generated scalar losses.
They retain the existing probability/Standard-Borel/predictable-`[0,1]`
contracts and add no independence, stationarity, concentration, or supplied
integrability assumption. Root import, declaration canaries, and a full
external tuned realized-regret application compile. Its all-horizon clipped-rate
consumer now compiles downstream.

### EXP3 uniform-horizon realized-regret update

`EXP3-UNIFORM-HORIZON-REALIZED-REGRET` is compiled in
`BanditRLProof.Exp3UniformRegret`. The new support theorem bounds actual
generated realized regret by the horizon for any legal rates. The module then
sets `gamma=min(1/2,sqrt(K*log K/T))`, `eta=gamma/K`, packages
`clippedPredictableTrajectoryKernel`, and proves
`sampledPredictable_clippedRealizedExpectedRegret_le_min`:
`E[R_T] <= min(T,4*sqrt(K*T*log K))` for every `T : Nat`, including `T=0`.

The proof uses only the compiled realized-to-mixed expectation transport,
finite-horizon `[0,1]` loss budget, Mathlib finite-sum integration, Real
log/sqrt, and ordered-ring algebra. It splits on `4*K*log K<=T`; the large
branch rewrites the clipped parameters to the tuned parameters, while the
small branch proves the square-root expression is at least `T`. Contracts are
the existing probability/Standard-Borel/predictable-`[0,1]` assumptions,
`2<=K`, and a supported comparator. No positive-horizon, independence,
stationarity, concentration, or manual integrability assumption is added.

The leaf is root-imported, externally instantiated in `Tests.Basic`, indexed by
`LOCAL-LEAF-EXP3-UNIFORM-HORIZON-REALIZED-REGRET`, and marked `leanCompiled`.
This closes the all-horizon expected realized-regret presentation for the
generated predictable adversary. High-probability bounds, stochastic rewards,
non-predictable adversaries, and other EXP3 variants remain separate routes.

### Countably-generated conditional-state freeze update

`COND-EXPECT-REWARD-CONDEXPKERNEL-MEASURABLE-FREEZE` is compiled in
`BanditRLProof.ConditionalExpectationReward`. The APIs
`condExpKernel_map_eq_deterministic_of_measurable` and
`condExpKernel_map_eq_dirac_of_measurable` show that every
conditioning-measurable map into a countably generated target is frozen by the
conditional-expectation kernel under the trimmed conditioning measure.

This removes the earlier `Countable` obstruction for Real-valued EXP3 history
prefixes. The route is entirely Mathlib-backed through the diagonal
composition-product law and finite-kernel a.e. uniqueness. It remains a
support leaf: its generated EXP3 successor-action consumer and one-step
realized-deviation conditional MGF now compile in the downstream concentration
leaf. Initial-time alignment and strongly adapted finite-sum assembly are still
required before invoking Azuma. No high-probability regret claim is made here.

### EXP3 successor realized-deviation conditional-MGF update

`EXP3-REALIZED-DEVIATION-SUCC-COND-MGF` is compiled in
`BanditRLProof.Exp3RealizedConcentration`. The generated predictable EXP3 law
now has a direct successor witness
`sampledPredictableRealizedDeviation_succ_hasCondSubgaussianMGF`: conditioned
on `(Env, finite pair prefix)`, realized loss minus the exploration-mixed
predictable loss is sub-Gaussian with the `[0,1]` Hoeffding proxy.

The new finite-support bridge upgrades successor-action `condDistrib` evidence
to the full `condExpKernel` action map without assuming a countable ambient
action type. The measurable-state freeze fixes Env/history, the finite action
law supplies the exact mixed mean, and the generated feedback equality carries
the result to scalar realized loss. The next narrow leaf is initial-time
alignment plus a zero-shifted strongly adapted process; only after that should
the existing Azuma sum-tail wrapper be invoked. This update is not yet a
finite-horizon or high-probability EXP3 regret theorem. The finite-horizon
concentration part has since compiled in the downstream update below.

### EXP3 finite-horizon realized-deviation tail update

`EXP3-REALIZED-DEVIATION-SUM-TAIL` is compiled in
`BanditRLProof.Exp3RealizedDeviationTail`. The theorem
`sampledPredictableRealizedDeviation_sum_tail_ennreal` packages the initial and
successor generated action laws into a single shifted, strongly adapted
process and applies the existing Mathlib-backed conditional sub-Gaussian sum
tail theorem. Its exact variance proxy is
`horizon * Concentration.intervalVarianceProxy 0 1`.

This closes the probabilistic finite-sum deviation route without a countable
ambient action type, independence, stationarity, or user-supplied exponential
integrability. Its delta confidence-radius consumer now compiles below.

### EXP3 realized-deviation delta-confidence update

`EXP3-REALIZED-DEVIATION-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3RealizedConfidence`. It exposes the standard one-sided
radius `sqrt(2 * V_T * log(1/delta))`, with
`V_T = horizon * intervalVarianceProxy 0 1`, and proves the corresponding
generated-trajectory event has measure at most `delta`.

The attempted next-step audit also sharpened the actual route to full
high-probability regret. `sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae`
controls pure-`q` and comparator importance-weighted estimators, not the true
predictable losses appearing in regret. Therefore the next theorem route must
construct conditional concentration for the comparator estimator and the
pure-`q` cross-weight estimator, and control the random second-moment sum (or
switch to an EXP3.P estimator). A direct deterministic event rewrite would be
mathematically invalid and must not be used.

### EXP3 comparator-estimator delta-confidence update

`EXP3-COMPARATOR-ESTIMATOR-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3ComparatorConfidence`. The fixed supported comparator's
observed importance-weighted loss is centered by the true predictable
comparator loss, with per-round proxy
`intervalVarianceProxy 0 (1 / (gamma / |arms|))`; the finite-horizon delta
radius is the corresponding `sqrt(2 * V_T * log(1/delta))`.

This closes the first probabilistic obligation identified by the Hedge
statement audit. The pure-`q` cross-weight obligation now compiles downstream.

### EXP3 pure cross-weight delta-confidence update

`EXP3-PURE-CROSS-WEIGHT-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3PureConfidence`. It first centers the pure-Hedge weighted
observed importance estimator by the predictable pure-Hedge loss, then negates
the conditional MGF to expose the regret-required predictable-minus-observed
tail. Generated zero/successor instances and finite-history adaptedness compile,
with finite-horizon delta radius using the same range proxy
`intervalVarianceProxy 0 (1 / (gamma / |arms|))`.

This closes the second probabilistic obligation from the Hedge statement audit.
The random estimator-square obligation now compiles downstream.

### EXP3 predictable high-probability regret update

`EXP3-PREDICTABLE-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3HighProbabilityRegret`. Instead of postulating a separate
square concentration theorem, it proves generated rewards are in `[0,1]` a.e.
and uses the exact selected-square formula plus the exploration floor to obtain
`sum square <= horizon/(gamma/|arms|)` a.e. The final event assembly combines
sampled Hedge, exploration bias, pure-q confidence, and comparator confidence;
`measure_mono_ae` and `measure_union_le` first give the explicit two-event
bound. The primary wrapper allocates `delta / 2` to each confidence event and
uses `ENNReal.ofReal_add` to give total failure probability
`ENNReal.ofReal delta`.

The generated realized selected-loss consumer now compiles downstream.
Separately, the current range proxy is quadratic in `|arms|/gamma`, so
ideal-rate EXP3 still needs a variance-sensitive/Freedman analysis or an EXP3.P
estimator modification.

### EXP3 realized high-probability regret update

`EXP3-REALIZED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RealizedHighProbabilityRegret`. The route adds the compiled
realized-minus-exploration deviation to the predictable pseudo-regret theorem.
The pathwise finite-sum identity is proved locally, the realized bad event is
contained in the union of the two compiled bad events, and `measure_union_le`
gives the raw three-term failure budget.

The public total-delta wrapper evaluates both the predictable budget and the
realized confidence radius at `delta / 3`, matching the three underlying
pure-q, comparator-estimator, and realized-deviation events. It controls the
actual scalar losses in the generated trajectory with total failure probability
`ENNReal.ofReal delta`. The next EXP3 high-probability target should therefore
be rate optimization or a variance-sensitive/EXP3.P route, not another event
assembly wrapper.

### Fixed-tilt conditional-MGF concentration update

`CONCENTRATION-FIXED-TILT-CONDITIONAL-MGF-SUM-TAIL` is compiled in
`BanditRLProof.ConcentrationFixedMGF`. It introduces kernel, measure, and
`condExpKernel` fixed-tilt MGF witnesses, proves additive composition through
successive kernels, closes strongly-adapted finite sums by induction, and
converts the resulting MGF budget to
`exp (-tilt * eps + sum psi)` with Mathlib's exponential Markov inequality.

The generic layer deliberately assumes all-tilt exponential integrability but
only one-tilt MGF domination. It assumes neither bounded increments nor a
variance process. Repository-wide Mathlib retrieval found no existing
Freedman/Bernstein concentration primitive. The one-step fixed-comparator EXP3
source and generated finite-horizon consumer now compile in the adjacent leaf;
broader ideal-rate claims still require its remaining downstream consumers.

### EXP3 fixed-comparator variance-sensitive update

`EXP3-COMPARATOR-BERNSTEIN-FIXED-TILT` is compiled in
`BanditRLProof.Exp3ComparatorBernstein`. The finite action calculation gives
the exact centered estimator second moment and bounds it by the reciprocal
exploration floor. Combined with the quadratic exponential remainder on
`|tilt * X| <= 1`, this yields the one-step budget `tilt^2 / epsilon` for
`0 <= tilt <= epsilon`.

The result is transported through the generated initial and successor action
laws, converted from predictable to observed feedback a.e., and summed along
the existing strongly adapted filtration. The resulting finite-horizon tail
has exponent `-tilt * threshold + horizon * tilt^2 / epsilon`, with
`epsilon = gamma / |arms|`. Its delta-shaped consumer now compiles below; the
analogous pure-cross estimator bound also compiles below. The remaining route
obligation is the improved high-probability EXP3 regret assembly.

### EXP3 fixed-comparator variance-sensitive delta update

`EXP3-COMPARATOR-BERNSTEIN-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3ComparatorBernstein`. It optimizes the fixed-tilt exponent
with a square-root tilt in the quadratic regime and the legal boundary tilt in
the large-budget regime. For `budget = max(log(1/delta),0)`, the resulting
radius is `2*sqrt(T*budget/epsilon)+budget/epsilon` and the generated bad event
has ENNReal probability at most `ofReal(delta)`.

The theorem holds for every finite horizon and every positive delta. The next
specific theorem route, the pure-cross variance-sensitive delta tail in the
sign consumed by Hedge regret, is now compiled below.

### EXP3 pure-cross variance-sensitive delta update

`EXP3-PURE-CROSS-BERNSTEIN-DELTA-CONFIDENCE` is compiled in
`BanditRLProof.Exp3PureBernstein`. Its finite-law calculation identifies the
cross-weighted raw score as `q(a) * loss(a) / p(a)` at the sampled action and
bounds the centered second moment by `1 / epsilon`, using both finite
distribution contracts and the sampling floor.

The module proves the fixed positive-tilt MGF directly for
`pure predictable loss - cross-weighted estimator`, transports it through the
generated conditional action laws, rewrites the latent estimator to observed
feedback a.e., and sums the existing strongly adapted process. Reusing the
compiled scalar optimizer gives radius
`2*sqrt(T*max(log(1/delta),0)/epsilon)+max(log(1/delta),0)/epsilon` for every
`delta>0` and arbitrary finite horizon. The next improved-regret obligation is
now compiled below. The audit showed that the current deterministic
`horizon/epsilon` Hedge-square bound can be reused honestly; improving that
term is a distinct ideal-rate obligation.

### EXP3 predictable Bernstein high-probability regret update

`EXP3-PREDICTABLE-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinHighProbabilityRegret`. It replaces both
range-Hoeffding confidence radii in the generated predictable regret assembly
with the compiled variance-sensitive pure-cross and comparator radii. The raw
theorem exposes two equal-delta failures; the primary theorem evaluates both
radii at `delta/2` and bounds total failure by `ENNReal.ofReal delta`.

The assembly continues to use the pathwise
`sum observedMixedSquaredImportanceWeightedLossAt <= horizon/epsilon` bound,
so no unproved square-term concentration is hidden. It works for arbitrary
finite horizon, including zero, and only requires `delta>0`. Its realized
selected-loss consumer now compiles below; the current theorem is not a general
Freedman or ideal EXP3.P result.

### EXP3 random estimator-square Bernstein regret update

`EXP3-RANDOM-SQUARE-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RandomSquareHighProbabilityRegret`. The generated moment
upper bound gives `E[sum mixedSquare] <= |arms|*T`; after proving the sum
nonnegative, measurable, and integrable, Mathlib Markov yields threshold
`|arms|*T/deltaSquare` with failure `deltaSquare`.

The complete predictable-regret endpoint includes this square event with the
pure-cross and comparator Bernstein events. Its total-delta wrapper allocates
`delta/3` to each, replacing the deterministic `|arms|*T/gamma` square term by
`3*|arms|*T/delta`. This removes one genuine reciprocal-exploration obstruction.
Its generated realized-regret assembly now compiles below. Beyond that,
logarithmic-confidence square control and the two exploration-floor confidence
radii still require stronger variance-process or EXP3.P machinery.

### EXP3 random-square Bernstein realized-regret update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret`. The
pathwise identity adds cumulative realized-minus-predictable deviation to the
compiled random-square predictable regret. The raw endpoint keeps separate
allocations for the square, both Bernstein confidence events, and realized
deviation; the public wrapper assigns `delta/4` to each.

This closes the generated selected-loss consumer without reintroducing the
deterministic `T/epsilon` Hedge-square bound. Its learning-rate tuning now
compiles below. The remaining rate work must account honestly for both
exploration-floor Bernstein radii and the bounded-loss realized radius rather
than labeling the result ideal EXP3.P or Freedman.

### EXP3 random-square realized learning-rate tuning update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-TUNING` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning`. The explicit choice
`eta=sqrt(log K*(delta/4)/(T*K))` exactly balances entropy against the
unamplified Markov-square term. Under `gamma<=1/2`, stability increases the
pair to at most `3*sqrt(4*K*T*log K/delta)`.

The public generated tail retains `gamma*T`, both Bernstein radii, and the
realized-deviation radius verbatim, so it needs no cubic or quadratic dominance
contracts and works for every positive delta. This closes eta optimization,
while the adjacent explicit route now chooses gamma without hiding the Markov
`1/sqrt(delta)` contribution.

### EXP3 random-square realized explicit gamma update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-EXPLICIT-TUNING` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning`. It uses the
maximum of the confidence cube-root scale and realized square-root scale,
clipped at `1/2`, and proves the generated tail at
`3*sqrt(4*K*T*log K/delta)+8*gamma*T`. Two factor-eight horizon inequalities
show clipping is inactive and discharge the exact cubic/quadratic contracts.

This advances the random-square route from caller-selected gamma to a concrete
large-horizon schedule. The adjacent all-horizon consumer now covers the
active-clip branch with a coarse pathwise fallback; stronger square/variance
process concentration remains necessary for a sharp replacement.

### EXP3 random-square realized all-horizon update

`EXP3-RANDOM-SQUARE-BERNSTEIN-REALIZED-ALL-HORIZON` is compiled in
`BanditRLProof.Exp3RandomSquareBernsteinRealizedAllHorizon`. It branches on the
same two large-horizon inequalities used by the explicit schedule. The true
branch invokes the refined random-square threshold; the false branch reuses
the generated a.e. regret bound and has zero failure probability at `T+1`.

This removes caller-managed regime selection and covers every positive
horizon. It does not improve the active-clipping rate: the fallback is coarse,
and the refined branch still contains Markov `1/sqrt(delta)` and bounded-loss
Hoeffding/Azuma terms. The next genuine rate advance must strengthen the random
square or predictable variance-process concentration rather than repackage the
same branch theorem as Freedman or EXP3.P.

### EXP3 realized regret with Bernstein predictable confidence update

`EXP3-REALIZED-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret`. The pathwise
realized-regret decomposition is unchanged, but its predictable component now
uses the compiled pure-cross and fixed-comparator Bernstein confidence radii.
The primary theorem allocates `delta/3` to those two events and the existing
realized-minus-predictable deviation event, yielding total failure probability
`ENNReal.ofReal delta` for generated selected scalar loss.

The realized-deviation event still uses its bounded `[0,1]` Hoeffding/Azuma
radius and therefore keeps the positive-horizon contract. The Hedge-square
contribution also remains the deterministic `horizon/epsilon` bound. The next
route is no longer event assembly: it is a tuning/rate audit that must decide
whether the retained square term permits a meaningful parameterized corollary,
without relabeling this theorem as general Freedman or ideal EXP3.P.

### EXP3 Bernstein tuning update

`EXP3-BERNSTEIN-TUNED-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinTuning`. With
`eta=sqrt(log K * gamma/(T*K))`, the full generated realized Bernstein budget
at `delta/3` is at most `11*gamma*T` under explicit cubic arm-log/confidence
contracts and the realized quadratic contract. The public endpoint transfers
that deterministic comparison through the existing total-delta theorem by
`measure_mono`.

This audit rules out reusing the expected-regret choice `eta=gamma/K`: with
the retained pathwise estimator-square bound, that choice leaves a linear
term. The compiled theorem instead exposes the honest `T^(2/3)`-type regime.
Its explicit clipped cube-root/max consumer now compiles below. An ideal
`sqrt(K*T)` theorem still requires a stronger square/variance route such as
EXP3.P or Freedman-style control.

### EXP3 explicit Bernstein schedule update

`EXP3-EXPLICIT-BERNSTEIN-HIGH-PROBABILITY-REGRET` is compiled in
`BanditRLProof.Exp3BernsteinExplicitTuning`. The schedule is
`min(1/2,max((K log K/T)^(1/3),max((K log(3/delta)/T)^(1/3),
sqrt(2*v*log(3/delta)/T))))`, where `v=intervalVarianceProxy 0 1`. Three
large-horizon premises prove clipping inactive and synthesize every dominance
contract consumed by the `11*gamma*T` tail.

The active-clip short-horizon branch now compiles in
`BanditRLProof.Exp3BernsteinAllHorizon`. The generated realized loss is at most
one almost surely and comparator loss is nonnegative, yielding regret at most
`T` almost surely and a zero-probability bad event at `T+1`. The all-horizon
endpoint branches between this fallback and the explicit `11*gamma*T` theorem
without asking the caller for large-horizon proofs.

The remaining rate gap is substantive: the `T+1` branch is coarse, and the
deterministic estimator-square plus bounded realized-deviation route does not
give ideal `sqrt(K*T)` high-probability regret. The next concentration leaf
should target random estimator-square/variance-process control or an EXP3.P
algorithmic correction, not another clipping wrapper.

### Current EXP3 square-process advance

`EXP3-MIXED-SQUARE-EXPONENTIAL-CONFIDENCE` is now compiled. The generated
observed mixed-square sum has a delta-shaped exponential tail at
`K*T + sqrt(2*T*intervalVarianceProxy(0,K/gamma)*log(1/delta))`. The route
uses the exact finite-action conditional mean, frozen-history
`condExpKernel` transport, a strongly-adapted centered process, and the
existing observed/predictable a.e. score equality.

The adjacent predictable-regret consumer now replaces
`sampledPredictableObservedMixedSquared_sum_tail_markov` with this exponential
tail, and the realized selected-loss consumer also compiles. Both preserve the
existing eta/gamma parameters; the exact learning-rate retuning now compiles
below.
That consumer must preserve the honest `(K/gamma)^2` interval proxy; a
variance-sensitive Freedman square-process theorem remains a separate target.

The exponential square tail is now consumed by
`Exp3MixedSquareExponentialHighProbabilityRegret`. The generated predictable
regret theorem uses the square threshold `K*T + radius`, the existing two
Bernstein confidence events, and a `delta/3` union bound. Thus the earlier
Markov `K*T/delta` contribution is no longer present in this theorem route.

`Exp3MixedSquareExponentialRealizedHighProbabilityRegret` now adds the
generated realized-minus-predictable deviation to this predictable theorem.
Its total-delta wrapper allocates `delta/4` to the exponential square,
pure-cross Bernstein, comparator Bernstein, and bounded realized-deviation
events. `Exp3MixedSquareExponentialRealizedTuning` now performs the fresh
learning-rate balance without reusing the old Markov formula: it sets
`S=K*T+squareRadius(delta/4)` and `eta=sqrt(log K/S)`, yielding the threshold
`3*sqrt(log K*S)+gamma*T` plus the two Bernstein and realized radii.

`Exp3MixedSquareExponentialRealizedExplicitTuning` now supplies that concrete
consumer. It uses a clipped maximum of an arm square root, a mixed-square
sixth root, a confidence cube root, and a realized square root, while retaining
the exact eta balance above. Under four explicit horizon contracts the
generated realized tail has threshold `14*gamma*T`. The sixth root follows
from the exact `(K/(2*gamma))^2` interval proxy and records that route cost
honestly. After multiplication by `T` it has square-root horizon scaling; the
current overall `T^(2/3)` limitation comes from the Bernstein confidence
cube-root component, so this is still not an ideal EXP3.P claim.

`Exp3MixedSquareExponentialRealizedAllHorizon` now consumes the explicit leaf.
It names the exact four-contract regime and branches between the refined
explicit threshold, already bounded by `14*gamma*T`, and the strict `T+1`
zero-probability fallback. The generated theorem therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof. It
is root imported and externally instantiated in `Tests.Basic`.

This closes the active-clipping presentation only at a deliberately coarse
fallback.

`Exp3MixedSquareBernstein` now supplies the first substantive square-process
improvement. The exact finite-law centered second moment is at most
`K/epsilon`, while the centered range remains `1/epsilon`; a two-parameter
fixed-tilt optimizer therefore gives the generated observed-square radius
`2*sqrt(T*(K/epsilon)*log_+) + log_+/epsilon` for every natural horizon.
`Exp3MixedSquareBernsteinHighProbabilityRegret` consumes that tail in the
three-event generated predictable-regret theorem, with root imports and full
external canaries for both endpoints. The adjacent
`Exp3MixedSquareBernsteinRealizedHighProbabilityRegret` now closes generated
realized selected-loss assembly by adding the compiled realized-deviation
radius and allocating `delta/4` across the four underlying events. The new
`Exp3MixedSquareBernsteinRealizedTuning` module also closes exact eta balancing
against `S=K*T+mixedSquareBernsteinRadius(delta/4)`, yielding the generated
threshold `3*sqrt(log K*S)+gamma*T` plus the three remaining confidence radii.

The explicit gamma schedule and all-horizon consumer for this tuned budget now
compile below. A stronger random predictable-quadratic-variation theorem
remains a separate route. The compiled fixed-tilt result and its consumers
should not be relabeled as anytime/general Freedman or ideal EXP3.P; the
linear `log_+/epsilon` correction and bounded-loss Hoeffding/Azuma realized
radius remain visible.

The first supporting leaf on that separate route now compiles as
`Exp3MixedSquarePredictableVariance`. It exposes the exact finite-law centered
second moment as a measurable generated process, proves the finite-action
integral representation and `K/(gamma/K)` pointwise bound, shifts it into an
`IsPredictable` process for the existing filtration, and proves the finite
horizon cumulative bound. Root import and external predictability/cumulative
canaries compile. `Exp3MixedSquarePredictableVariance` now also identifies the
actual generated centered square through the ambient `condExpKernel`: the
generic score pushforward, zero/successor wrappers, and unified shifted-process
conditional-square theorem all compile with an external full theorem canary.
`Exp3MixedSquarePredictableVarianceTail` now completes the next fixed-horizon
step: exact finite-law compensation, generated zero/successor conditional-MGF
transport, and fixed-MGF iteration yield
`P(sum X>=x and sum V<=v)<=exp(-t*x+t^2*v)`. Its optimized delta wrapper uses
`2*sqrt(v*log_+(1/delta))+log_+(1/delta)/(gamma/K)`. The module is root
imported and externally canaried.

`Exp3MixedSquarePredictableVarianceHighProbabilityRegret` now performs the
next consumer step without collapsing `sum V` to the deterministic envelope.
It first transports the centered joint tail to the observed Hedge square sum,
then combines it with the sampled Hedge inequality, exploration bias, and the
pure-cross/comparator Bernstein events. Its primary theorem gives
`P(predictable regret>=budget(v,delta)) <= delta + P(sum V>v)`, and a stronger
joint-event wrapper gives failure at most `delta` on `sum V<=v`. The module is
root imported, externally instantiated in `Tests.Basic`, and consumed by the
realized route below.

`Exp3MixedSquarePredictableVarianceRealizedHighProbabilityRegret` now adds the
compiled realized-minus-predictable deviation without collapsing the random
variance. Its joint theorem bounds realized selected-loss regret together with
`sum V<=v` by `delta`; its primary theorem gives
`P(realized regret>=budget(v,delta)) <= delta + P(sum V>v)`. The budget allocates
`delta/4` across random-square, pure-cross, comparator, and realized-deviation
events. The module is root imported and its residual total-delta theorem is
externally instantiated in `Tests.Basic`; it is consumed by the Markov route
below.

`Exp3MixedSquarePredictableVarianceRealizedMarkovHighProbabilityRegret` now
provides the first closed overflow consumer. Mathlib Markov proves
`P(sum V>v)<=lintegral(ofReal(sum V))/ofReal(v)`. Under the explicit generated
trajectory contract `lintegral(ofReal(sum V))<=ofReal(M)`, the primary theorem
sets `v=M/(delta/5)` and proves a realized selected-loss regret tail at total
failure `delta`, with all five events allocated `delta/5`. The module is root
imported, externally instantiated in `Tests.Basic`, and consumed by the
loss-energy specialization below.

`Exp3MixedSquarePredictableVarianceLossEnergyRealizedMarkovHighProbabilityRegret`
now discharges that abstract lintegral contract under a pathwise predictable
loss-square energy budget. The finite-law bound is
`Var(mixed-square estimator)<=sum_a loss(a)^2/epsilon`; generated summation
gives `sum V<=(1/(gamma/K))*L2`. Integrating this pathwise inequality supplies
`M=(1/(gamma/K))*L2` to the prior Markov theorem and yields the realized
total-delta endpoint. The module is root imported, externally instantiated in
`Tests.Basic`, and consumed by the small-loss theorem below.

`Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret`
now derives `L2<=L1` for
`L1=sum_t sum_a predictableLoss_t(a)` and carries `L1` through the entire
regret assembly. In particular, the observed-square/Hedge mean upper bound is
`L1` rather than `K*T`, cumulative variance is at most
`(1/(gamma/K))*L1`, and the
five-event total-delta theorem uses
`v=((1/(gamma/K))*L1)/(delta/5)`. This module is root imported and externally
instantiated in `Tests.Basic`, and consumed by the sparse-loss scenario below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret`
now constructs that `L1` budget from a concrete scenario contract. It defines
the per-round nonzero predictable-loss support inside `arms`, proves its loss
mass is at most its cardinality, and sums a uniform pathwise support cap `s` to
obtain `L1<=s*T`. The final theorem instantiates the existing realized
small-loss total-delta theorem with `lossMassBudget=s*T`. It is root imported,
focused/root built, externally instantiated in `Tests.Basic`, and consumed by
the eta-tuned route below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovTuning` now defines
the exact sparse Markov scale
`S=s*T+predictableVarianceRadius(((K/gamma)*s*T)/(delta/5),delta/5)` and sets
`eta=sqrt(log K/S)`. With `K>=2` and `0<gamma<=1/2`, the complete
eta-dependent budget is at most `3*sqrt(log K*S)`. Its final generated theorem
uses this internal eta and retains the same total failure `delta`. The module
is root imported, focused/root built, and externally instantiated in
`Tests.Basic`, and is consumed by the explicit-gamma route below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning`
now closes the large-horizon gamma schedule. For `B=log(5/delta)`, it uses the
clipped maximum of `sqrt(s*log K/T)`, the new fifth-root Markov scale
`(5*K*s*(log K)^2*B/(delta*T^3))^(1/5)`, the confidence cube root, and the
realized square root. Four explicit horizon contracts make clipping inactive,
recover the quadratic/fifth-power/cubic/quadratic dominance conditions, and
reduce the tuned threshold to `14*gamma*T`. Both eta and gamma are internal in
the final generated tail. The module is root imported, focused/root built,
externally instantiated in `Tests.Basic`, and consumed by the all-horizon
wrapper below.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAllHorizon` now
defines the exact four-contract regime and branches between the explicit
`14*gamma*T` threshold and the strict `T+1` zero-probability fallback. Its
generated theorem covers every positive horizon for `0<delta<=1` without a
caller-supplied regime proof, using the same internal eta and clipped gamma in
both branches. It is root imported, focused/root built, and externally
instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovAESparsityAllHorizon`
now removes the universal pathwise support requirement. The exact internally
tuned generated measure may discard a null exceptional set, after which every
time before the horizon has support cardinality at most `s`. The small-loss
lintegral and observed-square bridges were generalized to consume the
resulting a.e. `L1<=s*T` budget, so the final all-horizon theorem keeps total
failure `delta` with no extra sparsity allocation. It is root imported,
focused-built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity`
now handles positive-probability violations. It defines the exact generated
event where some support cardinality exceeds `S`, proves every sample has
`L1<=S*T` or belongs to that event, and propagates the event through new
observed-square, predictable, and realized residual consumers. Because
exceptional paths need not satisfy the sparse variance bound, Markov overflow
uses the unconditional `L1<=K*T` envelope. The practical endpoint assumes
`mu(sparsityFailure)<=ofReal(epsilon)` and proves the generated realized-regret
tail at `ofReal(delta)+ofReal(epsilon)`. It is root imported, focused/root
built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity`
now removes the global Markov envelope at the caller-selected eta/gamma
surface. Outside the exact failure event, the existing pointwise loss-mass and
variance inequalities give `sum V <= (1/(gamma/K))*S*T`. New off-bad
observed/predictable/realized small-loss APIs allocate four `delta/4`
confidence events, and the final decomposition charges `sparsityFailure`
exactly once. The practical endpoint proves `delta+epsilon` without event
measurability, restricted measures, global `K*T`, or Markov `1/delta`. It is
root imported, focused/root built, and externally instantiated in
`Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning`
now removes caller eta on the sharper route. It uses
`scale=S*T+predictableVarianceRadius((1/(gamma/K))*S*T,delta/4)` and
`eta=sqrt(log K/scale)`, proves the exact square balance and the three-copy
Hedge bound under `gamma<=1/2`, and exposes residual `delta+mu(failure)` and
practical `delta+epsilon` theorems under the identical internally eta-tuned
measure. It is root imported, focused/root built, and externally instantiated
in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning`
now removes caller gamma in the large-horizon regime. The clipped maximum
uses the sparse arm square root, the sharper pathwise mixed fifth root
`(K*S*log(K)^2*log(4/delta)/T^3)^(1/5)`, the Bernstein cube root, and the
realized square root. Four horizon contracts yield the generated
`14*gamma*T` residual and `delta+epsilon` endpoints under identical internal
eta/gamma measures. This route has no global `K*T` variance envelope, no
`K^2` mixed numerator, and no polynomial Markov `1/delta`. It is root
imported, focused/root built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityTuning`
now removes caller eta. It uses
`v=((1/(gamma/K))*(K*T))/(delta/5)`,
`scale=S*T+predictableVarianceRadius(v,delta/5)`, and
`eta=sqrt(log K/scale)`. The generated residual theorem keeps
`delta+mu(sparsityFailure)`, while the practical theorem consumes the exact
internally tuned generated-measure epsilon bound and proves `delta+epsilon`.
The module is root imported, focused/root built, and externally instantiated
in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityExplicitTuning`
now removes caller gamma in the large-horizon regime. The global variance
threshold closes to `5*K^2*T/(gamma*delta)`, producing the fifth-root schedule
`(5*K^2*log(K)^2*log(5/delta)/(delta*T^3))^(1/5)`. The clipped maximum with
the sparse arm, Bernstein, and realized-deviation scales supplies all four
dominance contracts; the generated endpoint has threshold `14*gamma*T` and
failure `delta+epsilon` under the exact internally eta/gamma-tuned
sparsity-failure premise. The module is root imported, focused/root built, and
externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityAllHorizon`
now removes the caller regime proof. Its threshold branches between the
explicit `14*gamma*T` probabilistic-sparsity result and strict `T+1`, while
keeping identical internal eta/gamma and generated measures. The residual
endpoint gives `delta+mu(sparsityFailure)` and the practical endpoint gives
`delta+epsilon` for every positive horizon. It is root imported, focused/root
built, and externally instantiated in `Tests.Basic`.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityAllHorizon`
now closes that route for every positive horizon. It branches between the
refined pathwise threshold, already bounded by `14*gamma*T`, and strict
`T+1`, while preserving the exact same internal eta, clipped gamma, generated
trajectory measure, and sparsity-failure event. The residual endpoint gives
`delta+mu(sparsityFailure)` and the practical endpoint gives
`delta+epsilon` without caller horizon inequalities or the old global
Markov scale. It is root imported, focused/root and `Tests.Basic` built, and
externally instantiated.

This closes the active-clipping presentation for the pathwise
probabilistic-sparsity branch at the same deliberately coarse fallback used by
the neighboring generated EXP3 routes.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now closes the finite fixed-comparator gap. It defines hindsight best
supported-arm predictable loss by `Finset.inf'`, rewrites the regret event as
the finite union of comparator events, and applies the preceding all-horizon
off-bad theorem at confidence share `delta/K`. Raw, eta-tuned,
gamma-characterized, explicit, and all-horizon fixed-comparator off-bad
surfaces now compile. Distributing removal of the common failure set through
the finite comparator union gives a best-arm off-bad tail at `delta`; adding
that set once gives residual `delta+mu(sparsityFailure)`. Under the exact
same-measure calibration
`mu(sparsityFailure)<=ofReal(epsilon)`, the practical endpoint is
`delta+epsilon`. It is root imported, focused/root and `Tests.Basic` built,
and externally instantiated at the single-charge theorem. The old
`K*mu(bad)`/`epsilon/K` wrappers remain compatible.

This theorem is a finite hindsight best-supported-arm result, not a
stochastic-mean or first-order best-arm bound. Single charging of the common
sparsity-failure event is closed; the `delta/K` schedule still carries the
expected logarithmic arm-count cost. The next narrow theorem-level gap is
replacement of bounded realized deviation by a genuine
variance-sensitive/Freedman route; sharper clipping, anytime control, and
ideal EXP3.P remain open.

`Exp3MixedSquareBernsteinRealizedExplicitTuning` now consumes the preceding
variance-sensitive eta-tuned theorem. It proves the exact `K^2/gamma`
variance-coefficient identity, controls both the square-root and linear pieces
of the fixed-tilt mixed-square radius under the existing four horizon
contracts, and obtains a generated realized-regret tail at `14*gamma*T`.
The Lean endpoint is
`sampledPredictable_explicitBernsteinSquareRealizedRegret_tail`; it is root
imported and has a full external canary in `Tests.Basic`.

The gamma definition deliberately aliases the already compiled conservative
four-scale clipped schedule. This closes the explicit large-horizon consumer
without claiming a sharper fifth-root or jointly optimized schedule. The
all-horizon wrapper below combines this explicit branch with the existing
strict `T+1` zero-probability fallback. The current linear
`log_+/epsilon` correction is compiled into the constant; eliminating or
improving it, Hoeffding/Azuma realized deviation, random
predictable quadratic variation, general Freedman, and ideal EXP3.P remain
separate theorem routes.

`Exp3MixedSquareBernsteinRealizedAllHorizon` now consumes that explicit leaf.
It names the exact four-contract regime and branches between the refined
variance-sensitive threshold, already bounded by `14*gamma*T`, and the strict
`T+1` zero-probability fallback. The generated theorem therefore covers every
positive horizon for `0<delta<=1` without a caller-supplied regime proof. It
is root imported and externally instantiated in `Tests.Basic`.

This closes the active-clipping presentation at the same deliberately coarse
fallback used by the neighboring generated EXP3 routes. The refined branch
still contains the controlled linear `log_+/epsilon` term and bounded-loss
Hoeffding/Azuma realized deviation. Sharper clipping, a better coupled gamma
schedule, random predictable quadratic variation, general Freedman, and
ideal EXP3.P remain separate targets.

`Exp3MixedSquareBernsteinRealizedBestArmAllHorizon` now upgrades that
fixed-comparator endpoint to the finite best supported arm in hindsight. A
shared `Exp3BestArm` module owns the `Finset.inf'` cumulative-loss definition
and event equivalence. The theorem calibrates the common all-horizon schedule
at `delta/K`, unions the comparator events, and proves failure at most
`ofReal(delta)` for every positive horizon. It is root imported, focused/root
and `Tests.Basic` built, and externally instantiated without a caller
comparator or large-horizon contract.

This closes the finite best-arm presentation for the current fixed-tilt
Bernstein-square route. The next concentration-level theorem gap is no longer
a best-arm wrapper: it is a genuine random-quadratic-variation or
variance-sensitive realized-deviation input that can replace the current
deterministic variance/Hoeffding components without overstating a general
Freedman theorem.

`Exp3RealizedPredictableVariance` and
`Exp3RealizedPredictableVarianceTail` now provide that narrow
variance-sensitive realized-deviation input. They identify the exact
finite-action selected-loss centered second moment, transport its compensated
MGF through generated zero/successor conditional action laws, move from
selected to realized deterministic feedback by AE equality, construct the
predictable shifted variance process, and prove the joint tail with radius
`2*sqrt(V*log_+(1/delta))+log_+(1/delta)`.

`Exp3MixedSquarePredictableVarianceRealizedDoublePredictableVarianceHighProbabilityRegret`
joins this tail to the existing mixed-square predictable-regret route.
`Exp3MixedSquarePredictableVarianceSmallLossRealizedDoublePredictableVarianceHighProbabilityRegret`
then preserves an explicit bad set while replacing the generic `K*T`
predictable mean budget by the sparse loss-mass budget.
`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsity`
then closes the caller-parameterized sparse theorem with budgets
`S*T`, `(K/gamma)*S*T`, and `S*T` for loss mass, mixed variance, and
realized variance respectively. It exposes off-bad `delta`, residual
`delta+mu(sparsityFailure)`, and practical `delta+epsilon` surfaces, charging
the common bad event once. Root and `Tests.Basic` builds pass.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityTuning`
now reuses the old sparse pathwise scale and chooses
`eta=sqrt(log K/scale)`. The tuned threshold is
`3*sqrt(log K*scale)+gamma*T` plus the two Bernstein confidence radii and the
exact realized predictable-variance radius at `S*T`. The external practical
endpoint proves `delta+epsilon` under the same generated-measure sparsity
failure premise.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityExplicitTuning`
now closes that explicit gamma leaf. Its clipped schedule is the maximum of
the previous sparse arm/mixed/confidence scales and the new
`sqrt(S*log(4/delta)/T)` selected-loss variance scale, clipped at `1/2`.
Four transparent horizon contracts make clipping inactive and give
quadratic/fifth-power/cubic/quadratic dominance. The exact realized radius is
at most `3*gamma*T`, and the full fixed-comparator threshold is
`16*gamma*T`. Off-bad, residual, and practical `delta+epsilon` endpoints all
compile under the same internal eta/gamma/generated measure, with the common
sparsity-failure event charged once.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityAllHorizon`
now consumes that explicit leaf. It packages the same four-contract regime
and branches between the exact explicit threshold, already bounded by
`16*gamma*T`, and strict `T+1` otherwise. Off-bad, residual, and practical
`delta+epsilon` endpoints use the identical internal eta/gamma/generated
measure and cover every positive horizon without a caller regime proof.

`Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon`
now upgrades that exact surface to the finite best supported arm in hindsight.
It runs the common eta/gamma/generated measure at `delta/K`, rewrites the
best-arm event through `Finset.inf'` as a finite comparator union, and
normalizes the union bound to `ofReal(delta)`. Removing the common
sparsity-failure event before the union and adding it afterward yields the
single-charge residual `delta+mu(bad)` and practical `delta+epsilon` endpoint
from an unscaled same-measure epsilon premise.

This closes finite hindsight best-arm transport for the exact selected-loss
predictable-variance route. The `delta/K` schedule retains the expected log-K
cost, and active-clipping coverage still uses a deliberately coarse strict
`T+1` fallback. This is not stochastic-mean or first-order best-arm regret;
general Freedman, anytime/self-normalized control, sharp clipping, and ideal
EXP3.P remain separate theorem routes.

### Predictable-compensator fixed-tilt concentration update

`ConcentrationFixedMGF` now exposes
`measure_sum_ge_inter_sum_le_of_compensated_hasCondMGFUpperBoundAt`. For a
strongly adapted compensated process `tilt*Y_i-varianceCoeff*V_i`, unit-tilt
zero-budget initial and successor conditional-MGF witnesses imply
`P(sum Y>=threshold, sum V<=varianceBudget) <=
exp(-tilt*threshold+varianceCoeff*varianceBudget)` in ENNReal form.

The proof reuses the compiled fixed-tilt finite-sum MGF theorem, performs the
`Measure.real` to ENNReal conversion once, and handles the random compensator
through event inclusion. The realized selected-loss predictable-variance EXP3
tail now calls this theorem with `varianceCoeff=tilt^2`, so the leaf is tested
on an existing theorem route rather than remaining an unused abstraction.

Contracts remain explicit: Standard Borel ambient space, finite
zero-or-probability measure, strong adaptedness, source-record exponential
integrability, initial/successor MGF bounds, and nonnegative coefficients. This
is fixed-horizon and fixed-tilt; it is not maximal/anytime, self-normalized,
tilt-optimized, or a general Freedman theorem.

### Quadratic fixed-MGF delta route update

`ConcentrationQuadraticFixedMGF` now compiles the complete optimization route
from a family of quadratic fixed-tilt tails to a delta-shaped joint
deviation/variance tail. Its radius is
`2*sqrt(c*V*log_+(1/delta))+log_+(1/delta)/cap`, and the theorem handles every
positive delta, including the trivial `delta>1` branch.

The algebraic tilt optimizer was moved out of the EXP3-specific Bernstein
module into this concentration layer. Both
`sampledPredictableRealizedDeviation_sum_tail_predictableVariance_delta` and
`sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta`
now consume the generic theorem, using caps `1` and `gamma/|arms|`. Their
public statements and downstream regret routes are unchanged.

Contracts are positive variance scale, variance budget, tilt cap, and delta,
plus the fixed-tail family on one unchanged joint event. Model probability,
adaptedness, conditional-MGF, and law-transport requirements remain with the
fixed-tail producer. This closes quadratic fixed-horizon tilt optimization,
not one-step MGF construction, maximal/anytime mixtures, optional stopping,
self-normalization, or a general Freedman theorem.

### Finite-prefix quadratic maximal update

`ConcentrationQuadraticMaximal` now lifts the quadratic delta theorem over a
nonempty finite index set. It uses confidence `delta/|times|` for every event,
applies the existing optimizer, and normalizes the finite outer-measure union
back to `ofReal(delta)`. No event-measurability premise is introduced.

`Exp3RealizedPredictableVarianceMaximal` consumes this theorem on
`times=range horizon`: index `t` denotes the positive prefix of length `t+1`,
so the covered lengths are `1` through `horizon` inclusive. All prefixes
share one selected-loss predictable-variance budget, and the
result controls their union under the generated EXP3 trajectory measure.

The generic layer requires a measurable ambient space, a decidable nonempty
finite index set, positive scale/budget/cap/delta, and one fixed-tail family
per index. The EXP3 specialization supplies its probability, Standard Borel,
loss regularity, and fixed-tilt law contracts. This is a finite union bound
with the explicit log-horizon cost; it is not a Ville/Doob inequality,
horizon-free anytime theorem, mixture boundary, optional-stopping result,
self-normalized theorem, or general Freedman theorem.

## Practical selected-policy centered-sum tail leaf

`ConditionalExpectationReward.centeredRewardSuccProcess_sum_tail_ennreal_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
now compiles in `BanditRLProof.ConditionalRewardLawSource`. On an ambient
probability space it turns the per-time policy-selected reward-coordinate
`condExpKernel.map` law, raw reward and selected-mean ranges, measurable
context/state/mean surfaces, `CenteredRewardKernelLaw`, and selected-history
variance ceilings into an ENNReal Azuma-Hoeffding bound for the zero-initialized
`Finset.range n` centered-reward sum. The random sum contains rewards `1`
through `n-1`.

The route reuses generated-history `StronglyAdapted`, the practical
selected-policy one-step conditional-MGF producer, and
`Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`. It is a
fixed-horizon aggregate tail, not an arm-wise empirical mean, confidence
inversion, anytime bound, or regret theorem. If a concrete model lacks the
selected reward law or variance transport, keep that obligation explicit
rather than assuming independence or an abstract conditional-MGF witness.

## Practical selected-policy two-sided delta confidence

The next theorem-facing layer now compiles. Generic declarations in
`BanditRLProof.ConcentrationSubGaussian` turn strongly adapted conditional
sub-Gaussian increments into a two-sided ENNReal finite-sum tail and calibrate
the radius
`Concentration.subGaussianSumConfidenceRadius V delta = sqrt (2*V*log(2/delta))`.
The practical endpoint
`ConditionalExpectationReward.centeredRewardSuccProcess_sum_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
instantiates this route from the selected reward-coordinate law and the same
raw/mean/history-variance contracts as the one-sided theorem.

The result controls the absolute aggregate centered-reward sum for rewards
`1..n-1` by `ENNReal.ofReal delta` under positive total proxy variance and
`0 < delta <= 1`. It is fixed-horizon aggregate confidence, not an arm-wise
empirical mean, random pull-count confidence sequence, anytime theorem, or
regret theorem. The next concrete route should supply an arm/sample-count
process or a model-specific selected-law transport; missing law, variance, or
positive-total-variance evidence must remain explicit.

## Practical selected-policy fixed-sample average confidence

The fixed-sample average leaf now compiles at both generic and practical
surfaces. `Concentration.measure_average_abs_tail_le_of_measure_sum_abs_tail`
transports any two-sided sum-confidence event through a positive deterministic
sample count, while
`Concentration.condSubGaussian_average_abs_tail_ennreal_delta_of_stronglyAdapted`
packages that transport with the compiled conditional sub-Gaussian sum route.
The practical endpoint is
`ConditionalExpectationReward.centeredRewardSuccProcess_average_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

Its prefix is exactly `Finset.range (m+1)`: slot zero is zero and slots
`1..m` are the `m` centered successor rewards, so the sum and radius are both
divided by `m`. Contracts are the existing selected-law/raw-range/mean-range/
history-variance surface plus `0<m`, positive total proxy variance, and
`0<delta<=1`. The next theorem route must introduce a genuine arm/sample-count
process before claiming arm-wise or random-count confidence; this result is
not anytime, self-normalized, Freedman, or regret concentration.

## UCB arm-stream fixed-prefix empirical-mean theorem

The arm/sample process requested by the preceding route is now instantiated
for the canonical stationary product arm-stream model. The generic independent
layer compiles two-sided finite-sum, delta-calibrated sum, and exact
`Finset.range k` average theorems using Mathlib
`HasSubgaussianMGF.sum_of_iIndepFun`. The concrete endpoint
`UCB.measure_armPrefixAverageConfidenceRadius_le_abs_empiricalMean_sub`
controls one arm's first `k>0` latent rewards around its supplied mean by
`ENNReal.ofReal delta`.

`UCB.armPrefixEmpiricalMean` averages coordinates `0..k-1`, and its radius is
`sqrt(2*(k*sigma2)*log(2/delta))/k`. Product-law coordinate independence and
the centered one-coordinate MGF law discharge the generic assumptions; total
variance positivity is derived internally from `k>0` and `sigma2!=0`.
Adaptive realized pull-count confidence remains on the already compiled
fixed-count peeling/index-tail route. This theorem adds no anytime,
self-normalized, Freedman, or new non-product selected-law transport claim.

## Selected-policy fixed-arm masked sum theorem

The non-product selected-policy route now has a real arm-wise aggregate step.
`ProbabilityTheory.HasCondSubgaussianMGF.indicator` uses conditional-kernel
support on a conditioning-measurable event to retain the same proxy after
masking. `generatedActionFromRewardHistory_succ_measurable_historyFiltrationSucc`
derives action predictability from the reward-prefix comap identity, and the
practical endpoint controls the absolute fixed-arm masked centered sum over
`Finset.range n` by `ENNReal.ofReal delta`.

The deterministic proxy sum in this older theorem still includes every
`varianceCeiling i`, including times when the arm is not selected. The newer
predictable-variance route below supplies the stronger masked proxy as a
separate compiled theorem.

## Selected-policy successor-arm empirical-mean theorem

The practical selected-policy route now reaches a genuine fixed-arm empirical
mean on the event that its realized successor pull count is positive.
`successorArmPullCount` and `successorArmRewardSum` cover exactly coordinates
`1..n-1`; `armMaskedCenteredRewardSuccProcess_sum_eq_successorArmRewardSum_sub_pullCount_mul`
uses a stationary arm mean to identify the masked centered sum; and the generic
`measure_randomCount_average_abs_tail_le_of_measure_sum_abs_tail` divides the
sum confidence event by the realized count. The final theorem is
`successorArmEmpiricalMean_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.

This older endpoint closes random positive-denominator transport with radius
`sqrt(2*V_horizon*log(2/delta))/N_arm`, where `V_horizon` is the full
deterministic horizon proxy.

The next count-adaptive layer now compiles. At one step,
`HasCondSubgaussianMGF.indicator_compensated_hasCondMGFUpperBoundAt` pays the
quadratic MGF budget only on the predictable arm-selection event. The generic
fixed-horizon theorem retains the cumulative masked proxy in a joint event and
optimizes the fixed tilt. In the practical selected-policy specialization,
`armMaskedVarianceSuccProcess_sum_eq_mul_successorArmPullCount` identifies a
constant ceiling's proxy sum with `sigma2 * successorArmPullCount`. Consequently
`successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
charges exactly `k*sigma2` on every fixed positive fiber `pullCount=k`.

Finite count peeling now closes the single random-count confidence event.
`measure_positive_randomCount_event_le_sum_exactCount` covers any positive
Nat-valued count event by its exact fibers under a deterministic ceiling, and
`measure_positive_randomCount_event_le_of_exactCount_uniform` assigns equal
`delta/maxCount` shares without count or event measurability. For the practical
route, `successorArmPullCount_le_horizon` supplies `maxCount=n`, and
`successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
uses the realized count in `successorArmEmpiricalMeanPeelingRadius` and has total
failure `ENNReal.ofReal delta`.

The simultaneous finite arm/time confidence event now compiles.
`successorArmEmpiricalMeanFiniteArmTimeBadEvent` unions over the explicit
nonempty family `arms.product (Finset.range T)`, using horizon `i+1` for every
`i<T`. `successorArmEmpiricalMeanFiniteArmTimeConfidenceShare` gives every
arm/time member an equal outer share, and its member theorem performs the prior
realized-count peeling internally. The final endpoint is
`successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`,
with total failure `ENNReal.ofReal delta`.

The random-width UCB score adapter now compiles in
`BanditRLProof.Algorithms.UCBConditionalRewardLaw`. It keeps the realized-count
radius instead of forcing the theorem through `UCB.finiteHorizonConfidenceBadEvent`,
whose radius is sample-independent. `SelectedPolicySuccessorInitializedScoreMaxSource`
packages an explicit post-initialization time set, candidate membership,
positive best/chosen counts, and score maximality. The pointwise consumer gives
`gap <= 2 * chosenRadius` outside the practical simultaneous event, and
`measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`
therefore gives total large-gap failure `ENNReal.ofReal delta`.

The concrete producer and expected-count transport described by this earlier
checkpoint are now closed in the following leaf. The route remains fixed
finite horizon and still does not provide regret, maximal/anytime,
self-normalized, or general Freedman concentration.

## Generated selected-policy UCB pull-count route

The concrete producer and pull-count consumer now compile in
`BanditRLProof.Algorithms.UCBConditionalRewardLawPolicy`. A measurable
finite-history policy reconstructs the actual pair prefix from generated
rewards, initializes all `Fin K` arms once on successor coordinates `1..K`,
and then chooses `UCB.scoreArgmax` for the same realized-count index used by
the random-width large-gap theorem. The reconstruction invariant proves that
the policy-side counts, sums, and indices are the generated trace quantities,
so `selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource` is a concrete
producer rather than an assumed algorithm contract.

For a chosen arm with positive gap, the full-horizon inequalities
`32*sigma2*L_T < gap^2*B` and `4*L_T < gap*B` uniformly imply
`2*radius(k,n) < gap` for `B<=k` and `n<=T`. The compiled consumers therefore
give both `P(N_chosen(T+1)>B) <= ENNReal.ofReal delta` and
`lintegral N_chosen(T+1) <= B + T*ENNReal.ofReal delta`. The practical tail
endpoint consumes the existing selected reward law, raw/mean range,
measurability, stationary arm mean, centered kernel, and uniform variance
contracts. The module is root-imported and externally canaried in
`Tests.Basic`.

The closed-form threshold and finite-arm gap-weighted pseudo-regret assembly
described by this checkpoint now compile in the following leaves. Model-side
production of the selected reward law and any anytime/self-normalized/general
Freedman or final broad UCB claim remain separate.

## Explicit-threshold practical UCB expected count

`selectedPolicySuccessorRealPullThreshold` is now the maximum of
`32*sigma2*L_T/gap^2` and `4*L_T/gap`, and
`selectedPolicySuccessorPullThreshold` is its `Nat.ceil` plus one.
`selectedPolicySuccessorPullThreshold_contracts` proves positivity and both
strict full-budget inequalities from only `gap>0`; the explicit radius, tail,
and ENNReal expectation consumers therefore expose no caller-supplied `B`,
`hradius`, or numeric inequalities.

The end-to-end theorem is
`lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy`.
It first builds the concrete source large-gap bound from the trim-a.e. selected
reward law, then concludes `lintegral N_chosen(T+1) <= threshold + T*ofReal
delta`. Its regularity surface is exactly the practical selected-law,
measurability, raw/mean range, centered-kernel, stationary-mean, positive
uniform-variance, `K,T>0`, `delta>0`, and positive chosen-gap contracts.

This leaf is Mathlib-backed through `Nat.le_ceil`, max/order and positive
division algebra, plus the already compiled measure and `lintegral` route. It
is consumed by the finite-arm practical pseudo-regret leaf below.

## Explicit-threshold practical UCB pseudo-regret

`BanditRLProof.Algorithms.UCBConditionalRewardLawRegret` now defines
`selectedPolicySuccessorGeneratedUCBRegretAction`, shifting generated successor
actions `1..T` to the standard pseudo-regret coordinates `0..T-1`, and proves
that its arm pull counts equal the existing successor counts at `T+1`.
`modelMeanGap_bestArm_eq_realGap` aligns the Real UCB mean gap with
`FiniteBanditModel.gap`.

The reusable theorem
`lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount`
expands scalar pseudo-regret into the finite arm sum, exchanges `lintegral`
with that sum, and asks for a count bound only when an arm gap is positive.
Model gap nonnegativity makes every zero-gap term vanish. The end-to-end
selected-law theorem then applies the explicit expected-count leaf armwise and
bounds practical ENNReal pseudo-regret by the `Finset.univ` sum of
`ofReal(gap) * explicitThreshold(gap)` and
`ofReal(gap) * (T * ofReal(delta))`.

Imports/APIs are `UCBConditionalRewardLawPolicy`,
`FiniteBanditModelInvariants`, `ScalarPseudoRegret`, the scalar
`ofReal_pseudoRegret` pull-count identity, `FiniteBanditModel.gap_nonneg`,
`MeasureTheory.lintegral_finset_sum`, and
`MeasureTheory.lintegral_const_mul`. The practical regularity surface retains
the probability/Standard-Borel, selected reward law, measurability, raw/mean
range, centered-kernel, stationary-model-mean, positive uniform variance,
`K,T>0`, and `delta>0` contracts; it exposes no per-arm positive-gap premise.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-EXPLICIT-THRESHOLD-PSEUDOREGRET`
is `leanCompiled`, root imported, focused-built, and externally canaried in
`Tests.Basic`. Retrieval evidence is compiled local/Mathlib code; theorem-card
and weapon-only text is not proof evidence. Its ceiling/max finite sum is now
simplified by the following leaf.

## Textbook positive-gap practical UCB pseudo-regret

`selectedPolicySuccessorTextbookGapBudget K sigma2 T delta gap` is
`32*sigma2*L_T/gap + 4*L_T + 2*gap`. The ceiling lemma bounds the integer
threshold by its real maximum plus two; the two nonnegative maximum branches
are bounded by their sum, and multiplication by a positive gap removes one
gap power. The ENNReal transport uses `ENNReal.ofReal_natCast`,
`ENNReal.ofReal_mul`, and `ENNReal.ofReal_le_ofReal`.

`sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum` filters the arm
sum to strictly positive model gaps, preserves the
`ofReal(gap)*(T*ofReal(delta))` term exactly, and removes zero-gap arms using
`FiniteBanditModel.gap_nonneg`. The full practical endpoint is
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_of_reward_map_eq_selected_policy`.
It directly exposes the positive-gap sum of the textbook arm budget plus the
confidence-failure contribution.

The imports and regularity contracts are unchanged from the explicit-threshold
practical theorem: probability/Standard Borel, selected reward
`condExpKernel.map` law, measurable context/reward/state/mean, raw/mean ranges,
centered kernel, stationary model means, positive uniform variance, `K,T>0`,
and `delta>0`. No per-arm positivity, threshold, radius, or numeric inversion
premise is caller-visible.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-GENERATED-TEXTBOOK-GAP-SUM-PSEUDOREGRET` is
`leanCompiled`, root imported through the existing module, focused-built, and
externally canaried in `Tests.Basic`. Compiled local/Mathlib declarations are
the retrieval evidence; theorem-card and weapon-only text is not proof. This
leaf is consumed by the canonical reward-only `trajMeasure` endpoint below.

## Canonical reward-only trajMeasure UCB pseudo-regret

`selectedPolicySuccessorRewardStepKernelFamily` specializes
`RewardKernel.historyStepKernelFamily` to the generated UCB policy/state.
`isMarkovKernel_selectedPolicySuccessorRewardStepKernelFamily` supplies the
family instances, and `selectedPolicySuccessorRewardTrajMeasure` plus its
probability instance expose the canonical Ionescu-Tulcea trajectory law.

`selectedPolicySuccessorGeneratedUCBSelectedRewardLawSource_trajMeasure`
specializes the canonical comap-trim selected-reward theorem and transports it
through
`generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy`.
Its public projection
`selectedPolicySuccessorGeneratedUCB_reward_map_eq_selected_policy_trajMeasure`
has the exact trim-a.e. `historyFiltrationSucc` `condExpKernel.map` surface used
by the practical theorem. The final
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure`
therefore supplies that law internally and returns the positive-gap textbook
ENNReal finite sum under the canonical reward-only trajectory measure.

The route imports `UCBConditionalRewardLawRegret` and uses
`Kernel.trajMeasure`, `ProbabilityTheory.IsMarkovKernel`, the canonical
trim-aware law, the finite-pair comap adapter,
`historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace`, and
`measurable_pi_apply`. Contracts remain explicit: probability initial law,
measurable context/state extraction, Markov reward kernel, measurable mean,
centered kernel law, stationary model means, positive selected-history
variance ceiling, `K,T>0`, `delta>0`, mean range, and pointwise raw range.

Card
`LOCAL-LEAF-UCB-SELECTED-POLICY-CANONICAL-REWARD-TRAJMEASURE-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`, root imported, focused-built, and canaried in `Tests.Basic`.
Evidence is the compiled declarations and Mathlib kernel/measure APIs; theorem
cards and weapon-only text are not proofs. The canonical selected-law premise
is closed. This compatibility endpoint is now consumed by the stronger
centered-kernel route below; its pointwise `hraw` and mean-range fields are no
longer blockers for the canonical theorem.

## Centered-kernel canonical UCB pseudo-regret

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final statement
`lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel`
uses the same canonical reward-only trajectory measure and textbook
positive-gap finite sum, but removes `hraw`, mean-range bounds, and the caller
selected-law premise completely.

The random variable at successor time `i+1` is reward minus the
history-selected kernel mean; the filtration is `historyFiltrationSucc`.
`CenteredRewardKernelLaw` already supplies selected-law integrability, zero
mean, and `HasSubgaussianMGF`. The canonical trim-a.e.
`condExpKernel.map` identity transfers this directly to
`HasCondSubgaussianMGF`. A predictable arm-selection indicator charges
`sigma2` exactly on pulls, exact-count fibers give two-sided confidence,
finite peeling handles the random count, and a finite arms-times union supplies
the generated-UCB large-gap event. Existing deterministic UCB algebra then
produces expected pull counts, finite-arm pseudo-regret, and the textbook
`32*sigma2*L/gap + 4*L + 2*gap` budget.

The module imports `UCBConditionalRewardLawTrajMeasure` and reuses the
integrated conditional-MGF transfer, generated-history `StronglyAdapted`
helpers, predictable-variance tail, exact-count peeling, finite union bounds,
score-max source, pull-count integration, and textbook sum algebra. Contracts
are now only probability `mu0`, measurable context and mean, a Markov reward
kernel with `CenteredRewardKernelLaw`, stationary means equal to `model.mean`,
positive selected-history variance ceiling, `K,T>0`, and `delta>0`.

Focused/root/`Tests.Basic` builds and twelve external canaries pass. Compiled
local declarations and Mathlib probability/kernel/integration APIs are the
evidence; theorem-card and weapon-only material is not proof. The complete
canonical ENNReal textbook pseudo-regret route is closed. Optional Real/
Bochner presentation and context-independent direct-subGaussian/bounded
constructors are closed by the downstream routes below. Context-dependent
constructors, anytime/self-normalized/general Freedman, cross-LML, and other
bandit/RL algorithms remain outside this route.

## Real/Bochner canonical UCB pseudo-regret

Card
`LOCAL-LEAF-UCB-CANONICAL-REWARD-TRAJMEASURE-CENTERED-KERNEL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel`
integrates the Real cast of canonical generated-UCB pseudo-regret with
`MeasureTheory.integral` and exposes the explicit positive-gap Real sum
`textbookGapBudget + gap * (T * delta)`. The public RHS contains no
`ENNReal.toReal`.

The supporting leaf `integrable_real_pullCount_of_measurable_action` derives
finite-horizon pull-count integrability from timewise action measurability,
`measurable_natCast_pullCount`, `pullCount_le_time`, and
`Integrable.of_bound` under a finite measure. The generated-UCB wrapper feeds
these witnesses to `integrable_real_pseudoRegret_of_integrable_pullCount`.
The final proof establishes pseudo-regret nonnegativity from the finite-arm
pull-count decomposition, rewrites `ofReal (integral ...)` as the compiled
lintegral, consumes the centered-kernel ENNReal theorem, proves the finite RHS
is not infinity, and normalizes it with `ENNReal.toReal_sum/add/mul/ofReal`.

Imports are `UCBConditionalRewardLawCenteredKernel` and
`ExpectationRegretPullCount`. The final regularity contracts remain exactly
the centered-kernel canonical contracts: probability initial law, measurable
context/mean, `CenteredRewardKernelLaw`, stationary model means, selected-
history variance bounded by positive `sigma2`, `K,T>0`, and `delta>0`.
Finite-horizon integrability is internal; no caller integrability, raw/mean
range, support restriction, or selected-law premise is added. Focused/root/
`Tests.Basic` builds and four new canaries pass. Compiled local declarations,
`MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, and the pinned Mathlib Bochner/
ENNReal APIs are the retrieval evidence. Context-independent direct-subGaussian
and bounded centered-kernel constructors, plus a bounded finite-arm theorem,
now compile downstream. Do not reopen the completed ENNReal-to-Real conversion
or weaken the theorem to a `.toReal` RHS.

## Bounded finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The final theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_boundedFiniteArmLaws`
instantiates the canonical Real route from stationary per-arm probability laws
sharing one nondegenerate interval `[lo,hi]`.

`FiniteArmRewardKernelLaw` is algorithm independent. It exposes
`contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF` from exact
means and direct per-arm MGF witnesses, and
`contextIndependentBoundedCenteredRewardKernelLaw` from a.e. measurable reward
casts, common a.s. interval bounds, and exact means. The latter reuses the
Mathlib-backed bounded centered-MGF wrapper. The supporting theorem
`intervalVarianceProxy_pos_of_lt` proves strict positivity of the Hoeffding
proxy from `lo < hi`.

The UCB theorem takes `Context := Unit`, uses `armLaw defaultAction` for the
initial reward and `contextIndependentOfActionLaws` for successors, sets the
kernel mean to `model.mean`, and discharges the constant variance ceiling and
all canonical trajectory contracts internally. Callers provide only per-arm
probability laws, `lo < hi`, a.e. measurability and a.s. interval membership,
exact model means, a default arm, `T>0`, and `delta>0`. The result is the same
explicit positive-gap Real textbook sum; no centered law, selected law,
trajectory law, variance premise, or integrability premise remains.

Focused/root/`Tests.Basic` builds and four external canaries pass. Retrieval
found the older ETC-specific bounded constructor first; the new generic module
avoids importing the large ETC theorem route into UCB. Exact local declarations,
`MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`, and the prior canonical
Real card are proof evidence. Unequal-range finite-arm laws compile in the
armwise route below; context-dependent, anytime/Freedman, and other algorithm
routes remain separate.

## Armwise bounded finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-ARMWISE-BOUNDED-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_armwiseBoundedFiniteArmLaws`
accepts separate support endpoints `lo arm` and `hi arm` for every finite arm.

`finiteArmIntervalVarianceProxy` computes the `Finset.univ.sup` of all armwise
Hoeffding proxies. `intervalVarianceProxy_le_finiteArmIntervalVarianceProxy`
discharges the selected-history variance ceiling, and
`finiteArmIntervalVarianceProxy_pos` uses `model.hK` plus pointwise
nondegeneracy to prove the UCB proxy is positive. The armwise reward-kernel
constructor applies the bounded centered MGF theorem independently to every
arm before the canonical Real endpoint is invoked.

The public contracts are per-arm probability laws, pointwise `lo arm < hi arm`,
a.e. measurable reward casts, per-arm a.s. interval support, exact model means,
a default arm, `T>0`, and `delta>0`. No common interval, caller variance
ceiling, centered law, selected law, trajectory law, or integrability witness
is required. Context-dependent/nonstationary laws and anytime/Freedman routes
remain separate.

## Direct sub-Gaussian finite-arm canonical UCB theorem

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_finiteArmSubgaussianLaws`
removes bounded-support assumptions entirely. Callers supply exact arm means
and a centered `HasSubgaussianMGF` witness with an `NNReal` proxy for each arm.

`finiteArmVarianceProxy` computes the finite maximum proxy;
`varianceProxy_le_finiteArmVarianceProxy` provides every selected-arm ceiling;
and `finiteArmVarianceProxy_pos_of_exists` needs only one positive member.
Zero-proxy deterministic arms are therefore allowed. The direct centered-law
constructor supplies integrability and zero mean, while the theorem constructs
the Unit-context stationary kernel and canonical trajectory internally.

The final result is the explicit Real positive-gap textbook sum at the maximum
proxy. There is no bounded support, common interval, caller variance ceiling,
abstract centered law, selected law, trajectory law, or integrability premise.
The exact-max endpoint still requires one positive member because the canonical
UCB theorem assumes a strictly positive common proxy. The positive-padded
endpoint below closes the all-zero family.

## Positive-padded direct sub-Gaussian finite-arm UCB theorem

Card
`LOCAL-LEAF-UCB-SUBGAUSSIAN-FINITE-ARM-LAWS-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. `Concentration.finiteArmPositiveVarianceProxy` is `max 1`
of the exact finite-arm maximum. It dominates every genuine arm proxy and is
strictly positive without a positive-member witness.

The public theorem
`integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_finiteArmSubgaussianLaws_without_proxy_positivity`
therefore accepts all-zero armwise proxy families. Original centered MGF
witnesses remain at their genuine proxies; padding is used only for UCB tuning.
The Unit-context kernel, trajectory law, centering, and integrability remain
internal. Padding may loosen the explicit Real textbook bound; sharper
zero-width behavior and nonstationary/anytime routes remain separate.

## Context-dependent bounded reward-kernel canonical UCB theorem

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-BOUNDED-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The generic `BoundedRewardKernelLaw` layer now constructs a
`CenteredRewardKernelLaw` for an arbitrary `MarkovRewardKernel`: either directly
from pointwise centered `HasSubgaussianMGF` witnesses and exact means, or from a
common nondegenerate a.s. interval by the Mathlib-backed bounded MGF theorem.

The final theorem accepts a measurable history-dependent context extractor and
allows the selected reward distribution to vary with context and action. It
requires the arm mean to remain `model.mean arm`, matching the stationary
`pseudoRegret` definition, and uses one common `lo < hi` support interval. The
interval proxy, centered law, selected-law probability instances, trajectory
law, variance ceiling, centered/raw integrability, and zero-centered-mean facts
are constructed internally.

The conclusion is the explicit positive-gap Real textbook sum. Focused and
external canary builds pass. Context/action-dependent intervals, direct
context-dependent sub-Gaussian laws with an automatically constructed positive
common ceiling, nonstationary regret, and anytime/Freedman routes remain
separate leaves. The direct sub-Gaussian route with an explicit global ceiling
is closed below.

## Context-dependent direct sub-Gaussian canonical UCB theorem

Card
`LOCAL-LEAF-UCB-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. The theorem accepts an arbitrary context-dependent Markov
reward kernel, a pointwise `NNReal` proxy, and direct centered
`HasSubgaussianMGF` evidence for every context/action selected law. Rewards and
proxies may vary with context/action, while exact means remain
`model.mean arm` to match stationary pseudo-regret.

Callers supply one strictly positive `sigma2` and prove every pointwise proxy
is at most it. This is the necessary general contract for an arbitrary
measurable context space: unlike `Fin K`, it has no finite `Finset.sup` from
which Lean can compute a maximum. The centered kernel law, selected-law and
trajectory transports, centering, and all integrability obligations are
constructed internally, with no bounded-support assumption.

The result is the explicit positive-gap Real textbook sum at `sigma2`. The two
finite-context specializations below close exact automatic maxima and
all-zero/noiseless families by positive padding. Infinite compact-context
ceilings, context-dependent means/nonstationary regret, and anytime/Freedman
routes remain separate.

## Finite-context automatic-ceiling direct sub-Gaussian UCB theorem

Card
`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-AUTOMATIC-CEILING-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. `Concentration.finiteContextArmVarianceProxy` computes the
nested `Finset.univ.sup` over `Context` and `Fin K`; Mathlib `Finset.le_sup`
proves pointwise domination, and one positive context/action proxy makes the
maximum strictly positive.

The finite-context UCB theorem removes caller-supplied `sigma2` and its global
domination proof. It retains finite measurable context, stationary arm means,
direct pointwise centered `HasSubgaussianMGF`, one positive proxy, and the
existing horizon/delta contracts, while constructing all law transport and
integrability internally. This exact-maximum endpoint still needs one positive
member; the padded endpoint below closes the all-zero case. Automatic ceilings
for infinite context spaces remain separate.

## Finite-context positive-padded direct sub-Gaussian UCB theorem

Card
`LOCAL-LEAF-UCB-FINITE-CONTEXT-DEPENDENT-SUBGAUSSIAN-REWARD-KERNEL-POSITIVE-PADDED-CANONICAL-REAL-TEXTBOOK-PSEUDOREGRET`
is `leanCompiled`. `Concentration.finiteContextArmPositiveVarianceProxy` is
`max 1` of the exact finite context/action maximum. It dominates every genuine
proxy and is strictly positive without assuming any proxy is positive.

The public canonical Real theorem therefore accepts arbitrary `NNReal`
context/action proxies, including an all-zero family. Pointwise MGF evidence
remains stated at each genuine proxy; the padded value is used only for the UCB
confidence width. No caller `sigma2`, domination proof, or positivity witness
remains. Infinite context, nonstationary means, and anytime/Freedman routes are
still separate.

## Generated half-Tsallis trajectory route

The narrow leaf `TSALLIS-HALF-GENERATED-TRAJECTORY-STABILITY` now compiles in
`BanditRLProof.TsallisFTRLRecursiveTrajectory`. It upgrades the prior abstract
finite-horizon expected-stability theorem to a generated predictable pure
half-Tsallis process: recursive sampled-history scores, measurable finite-arm
policy kernels, an Ionescu--Tulcea trajectory, the conditional next-action law,
and the a.e. importance-weighted score update are constructed locally. The
external `Tests.Basic` canary instantiates the final generated endpoint.

The follow-up leaf
`TSALLIS-HALF-GENERATED-STABILITY-AUTOMATIC-INTEGRABILITY` now compiles in
`BanditRLProof.TsallisFTRLGeneratedRegularity`. Finite sampling mass cancels the
importance-weighted denominator, giving a conditional absolute-moment bound
`1 + arms.card`; the half-power budget is uniformly bounded by
`2 * |eta| * arms.card`. Consequently the generated finite-horizon endpoint
retains only per-round stability-score measurability and removes both caller
integrability families. `Tests.Basic` canaries the no-integrability theorem.

The next leaf `TSALLIS-HALF-GENERATED-STABILITY-MEASURABILITY` also compiles in
`BanditRLProof.TsallisFTRLGeneratedMeasurability`. Finite measurable sums,
singleton-action importance-weighted coordinates, predictable-loss
composition, and current/updated selector coordinates derive the generated
stability score's measurability. Its selector-only horizon theorem therefore
has neither caller `hscore` nor caller integrability families.

`TSALLIS-HALF-CANONICAL-SELECTOR-MEASURABILITY` now compiles. The route proves
strict convexity and supported-coordinate uniqueness, then uses compactness,
ultrafilter cluster-point transport, and joint objective continuity to prove
the restricted canonical minimizer continuous in its finite score vector.
Coordinatewise Borel composition constructs the finite-history and generated
updated selector contracts. The canonical generated horizon endpoint therefore
has no selector, `hscore`, or integrability argument.

`TSALLIS-ESTIMATED-ENVIRONMENT-REGRET` now compiles in
`BanditRLProof.TsallisFTRLEstimatedEnvironmentRegret`. It joins the deterministic
canonical decomposition to the generated predictable trajectory for
`horizon + 1` actual rounds, handling time zero separately from successors
`1, ..., horizon`. Observed-to-predictable law transport and finite sampling
mass cancellation prove the required mixed/comparator first moments without a
uniform probability floor. The final endpoint uses a probability prior and a
general finite-simplex comparator, and is root imported and externally
canaried.

`SELF-BOUNDING-CONVERSION` now compiles in
`BanditRLProof.TsallisSelfBounding`: fixed-gap point-mass environment regret is
identified with gap mass, the integrated `(Delta,C,T)` condition and finite
completion-of-squares consumer compile, and a point-mass theorem records why
the current all-arm half-power budget cannot supply the needed suboptimal-arm
bound.

The supporting `TSALLIS-REFINED-SHIFTED-IW-MOMENT` leaf now compiles in
`BanditRLProof.TsallisRefinedImportanceWeightedMoment`. Subtracting the sampled
raw loss as a common baseline exposes a quadratic inverse-half-Hessian moment
whose simplex average is at most `sum_a sqrt(p_a)*(1-p_a)` and a positive cubic
remainder whose average is at most one. Its exact current-FTRL wrapper therefore
returns `eta/2 * sum_a sqrt(p_a)*(1-p_a) + eta^2/2` from one explicit premise,
`hshiftedTaylor`. The finite-sum cancellation is proved locally; a direct
pointwise `sqrt(p_chosen)*(1-p_chosen)` replacement is false.

`TSALLIS-REFINED-AVERAGED-STABILITY-DIAGNOSTIC` is now resolved negatively in
`BanditRLProof.TsallisRefinedAveragedStabilityObstruction`. The compiled public
theorem constructs `Fin 2` data with `eta = 1/100`, a strict current simplex
minimizer, strict simplex minimizers for both ordinary-IW sampled updates, and
losses in `[0,1]`, yet the sampled average of `<p-p_next,hatLoss>` is strictly
larger than the locally paper-scaled
`eta * sum_a sqrt(p_a)*(1-p_a) + 2*eta^2`. Thus the entire desired direct
average, not only the earlier stronger `hshiftedTaylor` coefficient, is false
under the existing contracts. The obstruction concerns the current
symmetrized term, not the paper's conjugate-potential stability.

The distinct producer `TSALLIS-CONJUGATE-POTENTIAL-STABILITY` now compiles in
`BanditRLProof.TsallisConjugatePotentialStability`. Its canonical endpoint uses
the existing half-Tsallis minimizer/update selectors and proves the ordinary-IW
sampled-action bound
`eta * sum_a sqrt(p_a)*(1-p_a) + 2*eta^2`. The local `eta <= 1/2` contract is
the paper's `eta_paper <= 1` after `eta_paper = 2*eta_local`. The proof derives
the exact rational coordinate conjugate increment, applies a quadratic/cubic
upper bound, cancels score and the common stationarity multiplier, cancels the
selected raw-loss baseline by simplex normalization, and reuses the compiled
shifted moments. Current/update exact minimizers and `[0,1]` losses are the only
algorithmic contracts; there is no measure, kernel, integrability, or trajectory
premise.

Independent review found the fixed-eta coefficients and signs correct, and also
identified a cross-eta normalization hazard. The potential definition now adds
`1/eta`, matching the paper normalization; this cancels in the present
one-step theorem but is essential for a future time-varying telescope. The
low-level feasible-next theorem is explicitly named and documented as a
candidate bridge; only the minimizer-level and canonical wrappers represent
both constrained potential values. The public-import axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

This closes the deterministic paper-faithful one-step producer, not the full
Tsallis-INF theorem. Its downstream fixed-eta generated conditional-action
transport and finite-horizon telescope now compile as
`TSALLIS-CONJUGATE-POTENTIAL-FINITE-HORIZON-DECOMPOSITION`.
`TSALLIS-TIME-VARYING-PENALTY` now compiles independently in
`BanditRLProof.TsallisTimeVaryingPenalty`. Its generic and canonical endpoints
telescope positive nonincreasing schedules, use same-rate next-score minimizers
for cross-eta comparison, retain the negative terminal comparator mass, and
specialize a supported point mass to the explicit best-arm term `-1 / eta_n`.
A complete generated route still needs scheduled-selector measurability and
trajectory/law transport, a coarse early-round fallback when local
`eta > 1/2`, and an exact reusable Lemma 18 conjugate-value interface. A
reduced-variance estimator remains a separate estimator/law route.
Paper/theorem cards are route evidence and weapon cards are inspiration-only,
not local Lean proofs; no final Tsallis-INF regret theorem is claimed.

The next scheduled-law obligation now compiles as
`TSALLIS-SCHEDULED-RECURSIVE-TRAJECTORY` in
`BanditRLProof.TsallisScheduledRecursiveTrajectory`. Its exact index convention
is `eta 0` for the initial action and `eta (n+1)` for the successor action after
prefix `n`. Canonical selector coordinate measurability is packaged roundwise;
the recursive score, finite-action policy, full measurable-environment
trajectory, and both conditional successor-action laws are locally proved.

This closes the generated scheduled policy/law layer without adding positivity
or monotonicity assumptions to it. The downstream pathwise alignment and
deterministic penalty assembly now compile in
`BanditRLProof.TsallisScheduledScoreAlignment`. The expected successor-round
same-rate stability sum now also compiles in
`BanditRLProof.TsallisScheduledExpectedStability`. The next narrow leaf is the
separate time-zero expected stability consumer. The early local-rate fallback,
full refined expectation assembly, schedule tuning, and final Tsallis-INF
regret remain open.

`TSALLIS-CONJUGATE-POTENTIAL-FINITE-HORIZON-DECOMPOSITION` now compiles in
`BanditRLProof.TsallisConjugatePotentialFiniteHorizon`. It provides the exact
fixed-eta deterministic telescope, a generic finite-horizon integral theorem
under identified conditional action laws, and a generated canonical successor
endpoint. The latter constructs selector measurability, finite-action policy
and condDistrib identities, score recursion, and all required integrability
internally. Its expected upper is the finite sum of
`eta * sum_a sqrt(p_a)*(1-p_a) + 2*eta^2`, with no uniform probability floor.

The contracts are finite nonempty decidable arms, finite prior, Standard Borel
environment/action, measurable action singletons, predictable `[0,1]` losses,
and fixed local `eta` in `(0,1/2]`. The next narrow route is therefore not
another fixed-eta transport theorem. The deterministic scheduled
`TSALLIS-TIME-VARYING-PENALTY` producer, scheduled selector/trajectory law, and
pathwise score/penalty alignment now compile. The successor portion of the
expected scheduled same-rate stability sum now compiles as well. Next prove the
initial-action finite-law expectation/integrability consumer, followed
separately by an explicit early-round fallback for local `eta > 1/2`. Refined
assembly and final regret remain open.

The supporting `TSALLIS-REFINED-ALLARM-TO-SUBOPTIMAL` bridge now compiles in
`BanditRLProof.TsallisRefinedSuboptimalStability`. It eliminates the best arm
from the paper-shaped `sqrt(p)*(1-p)` sum and directly composes a finite
time-indexed refined upper with the compiled self-bound. Since the compiled
obstruction rules out `hshiftedTaylor` for the current expression, the
paper-faithful producer route is
`TSALLIS-CONJUGATE-POTENTIAL-STABILITY`, expected-simplex/Jensen transport,
and the per-round `eta_t^2/2` base term. The separate
`TSALLIS-TIME-VARYING-PENALTY` route needs scheduled minimizers,
measurability, kernel identities, and same-`eta_t` auxiliary updates; these now
compile through the pathwise generated assembly. The time-zero expected
stability term and its exact all-times assembly with the compiled successor
sum now also compile. The early large-rate fallback and the small-rate
expected stability-plus-penalty integration remain separate narrow consumers.

`TSALLIS-SCHEDULED-SUCCESSOR-EXPECTED-STABILITY` now compiles in
`BanditRLProof.TsallisScheduledExpectedStability`. For every successor index in
`Finset.range horizon`, it applies the ordinary-IW conjugate stability theorem
at the local rate `eta (n+1)`, transports the scheduled finite conditional
action law, derives selector measurability and score/budget integrability, and
rewrites the stored reward to the predictable `[0,1]` loss coordinate almost
surely. The final Lean statement directly integrates the pathwise stability
term consumed by `TsallisScheduledScoreAlignment`, not an auxiliary surrogate.

Contracts are finite nonempty decidable arms, finite prior, Standard Borel
environment/action with measurable action singletons, predictable `[0,1]`
losses, and `0 < eta (n+1) <= 1/2` on included successors. Schedule
monotonicity and a probability floor are not required.

`TSALLIS-SCHEDULED-INITIAL-EXPECTED-STABILITY` now compiles in
`BanditRLProof.TsallisScheduledInitialExpectedStability`. It identifies the
actual pathwise time-zero stability term almost surely with the canonical
zero-score initial history/action potential score and applies the same generic
refined one-round theorem through the initial action `condDistrib`. Its exact
contracts are a finite prior, Standard Borel environment/action, measurable
action singletons, finite nonempty decidable arms, predictable `[0,1]` initial
losses, and `0 < eta 0 <= 1/2`; no successor-rate or monotonicity premise is
used. Its downstream all-times consumer now compiles.

`TSALLIS-SCHEDULED-ALL-TIMES-EXPECTED-STABILITY` now compiles in
`BanditRLProof.TsallisScheduledAllTimesExpectedStability`. It proves
integrability of the exact `Finset.range (horizon + 1)` pathwise stability sum
and bounds its expectation by the initial refined budget plus the complete
successor refined-budget sum. The route reuses the public successor a.e.
history/action identification, both expected-stability endpoints,
`IntegrabilitySums.integrable_finset_sum`, `Integrable.add`, and
`integral_add`. Its exact contracts are a finite prior, Standard Borel
environment/action, measurable action singletons, finite nonempty decidable
arms, predictable `[0,1]` losses, and `0 < eta t <= 1/2` through the horizon;
no monotonicity or probability floor is required. Next isolate the local
`eta_t > 1/2` coarse fallback or integrate this small-rate bound with the
scheduled penalty theorem. Neither step yet proves the full refined regret or
Tsallis-INF theorem.

`TSALLIS-SCHEDULED-ALL-RATE-EXPECTED-STABILITY` now compiles in
`BanditRLProof.TsallisScheduledAllRateExpectedStability`. It closes the first
of those two alternatives: deterministic ordinary-IW cancellation gives a
coarse one-round stability budget `1` for every positive local rate, generic
finite-action integrability and `condDistrib` APIs transport that budget, and
generated initial/successor wrappers combine it with the existing refined
budget at rates at most `1/2`. The final theorem retains the exact
`Finset.range (horizon + 1)` pathwise sum and assumes only positivity through
the horizon. Its expected stability-plus-time-varying-penalty consumer now
compiles.

`TSALLIS-SCHEDULED-EXPECTED-REGRET` now compiles in
`BanditRLProof.TsallisScheduledExpectedRegret`. It proves the scheduled
probability/measurability and no-floor conditional-IW moment layer, transports
the stored-reward estimated regret exactly to predictable environment regret,
and combines the pathwise point-mass penalty with the all-rate stability sum.
The endpoint assumes a probability prior, `best ∈ arms`, positive rates
through the inclusive horizon, and a nonincreasing schedule; it imposes no
uniform eta upper bound or probability floor. The next theorem route is the
all-arm-to-suboptimal expected conversion feeding schedule tuning; its
small-rate conversion now compiles downstream.

`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY` now compiles in
`BanditRLProof.TsallisScheduledSuboptimalExpectedBound`. Expected scheduled
action probabilities form a finite simplex, Mathlib concave Jensen moves
`E[sqrt (p_t(a))]` below `sqrt (E[p_t(a)])`, and the compiled all-arm
elimination reduces every small-rate refined budget to `arms.erase best`.
The generated point-mass environment-regret bound now reaches the deterministic
time-by-suboptimal-arm expression and, under an explicit positive-gap
self-bounding inequality, the completion-of-squares endpoint. The next narrow
route, deriving that self-bound automatically from an exact predictable
fixed-gap loss law, now compiles downstream.

`TSALLIS-SCHEDULED-FIXED-GAP-SELF-BOUNDING` now compiles in
`BanditRLProof.TsallisScheduledFixedGapSelfBounding`. It identifies scheduled
point-mass environment regret pathwise with suboptimal gap mass, exchanges the
finite time/arm sums with expectation, and proves exact equality with
`sum_t sum_{a != best} gap(a) E[p_t(a)]`. Nonnegative corruption therefore
supplies the self-bounding premise automatically, and the final theorem reaches
the squared-rate-over-gap regret bound. The next narrow route is either to
transport a stochastic reward-kernel/mean law into this exact predictable gap
contract or to tune a concrete schedule; the refined penalty prerequisite for
the second route now compiles downstream.

`TSALLIS-SCHEDULED-REFINED-EXPECTED-PENALTY` now compiles in
`BanditRLProof.TsallisScheduledRefinedExpectedPenalty`. It preserves every
`1 / eta (t+1) - 1 / eta t` term from the deterministic penalty telescope,
cancels the point-mass baseline, bounds the remaining potential mass by
`2 * sum_{a != best} (sqrt(p_a) - p_a/2)`, and transports this expression to
expected scheduled probabilities with the existing Jensen API. The generated
predictable environment-regret endpoint has no terminal
`M(p_0) / eta_horizon` term. The next narrow route is to combine these refined
penalty coefficients with the refined stability coefficients; that assembly
now compiles downstream.

`TSALLIS-SCHEDULED-REFINED-STABILITY-PENALTY-ASSEMBLY` now compiles in
`BanditRLProof.TsallisScheduledRefinedStabilityPenalty`. Its unified coefficient
is `2*eta_0+2/eta_0` at time zero and
`2*eta_t+2*(1/eta_t-1/eta_(t-1))` afterward. The deterministic expected-regret
endpoint has base `sum_t 2*eta_t^2` and one coefficient times each suboptimal
square-root mass. Under the existing exact fixed-gap contract, completion of
squares is automatic and produces `sum_(t,a) coefficient_t^2/gap_a` plus
twice the base and corruption. Its concrete square-root schedule consumer now
compiles downstream. Reward-kernel-to-gap transport and the full Tsallis-INF
theorem remain separate.

`TSALLIS-SQRT-SCHEDULE-FIXED-GAP` now compiles in
`BanditRLProof.TsallisSqrtScheduleFixedGap`. The concrete rate
`eta_t=1/(2*sqrt(t+1))` automatically discharges positivity, monotonicity, and
the `1/2` small-rate contract. The module proves `4*eta_t^2=1/(t+1)` and
`c_t^2<=25/(t+1)`, then factors the time/arm product to obtain
`H_(T+1)*(1+25*sum_(a!=best)1/gap_a)+corruption`. The theorem is root-imported
and externally canaried on `Fin 2`. Its Mathlib-backed harmonic-to-log
corollary now compiles downstream. Broader stochastic/corrupted-law transport
into self-bounding remains separate.

`TSALLIS-SQRT-SCHEDULE-LOG-FIXED-GAP` now compiles in the same module. The
local Real harmonic sum is identified with the cast of Mathlib
`harmonic (T+1)`, and `harmonic_le_one_add_log` yields the explicit endpoint
`(1+log(T+1))*(1+25*sum_(a!=best)1/gap_a)+corruption`. No extra horizon or
schedule hypothesis is exposed. The next substantial route is no longer
schedule algebra: it is a precise stochastic/corrupted reward-law transport
into the self-bounding contract required by the broader Tsallis-INF theorem.

`TSALLIS-FINITE-BANDIT-MEAN-LOSS` now closes the intervening model-semantic
route in `BanditRLProof.TsallisFiniteBanditMeanLoss`: bounded finite-arm reward
means generate the stationary predictable losses `1-mean`, their differences
against `bestArm` are the model gaps, and the existing logarithmic theorem
therefore exposes an explicit `FiniteBanditModel` endpoint without caller
loss/gap-law/schedule proofs. This is intentionally a deterministic Dirac
mean-loss environment. The next substantial route is specifically to replace
that feedback with stochastic reward-kernel observations while preserving the
conditional mean and self-bounding identity; merely restating arm means is no
longer the missing step.

`TSALLIS-SCHEDULED-EXPECTED-GAP-SELF-BOUNDING` now closes the next theorem
route. The project has a compiled per-time/per-arm first-moment contract
`HasScheduledExpectedGapLaw`, its finite integral/self-bounding transport, and
generic refined and square-root-schedule consumers. Consequently the explicit
logarithmic endpoint no longer needs a samplewise exact-gap law; it needs only
`E[p_t(a)(loss_t(a)-loss_t(best))]=gap(a)E[p_t(a)]` plus positive suboptimal
gaps and nonnegative corruption. Root and `Tests.Basic` builds and an external
`Fin 2` canary pass.

The next narrow theorem route is now sharply isolated: construct a concrete
stochastic latent loss/reward model and prove this expected-gap law from its
conditional mean or independence contract. The finite-sum integration,
completion of squares, square-root schedule, and harmonic/log algebra should
not be reopened. This leaf is not yet the full stochastic or corrupted
Tsallis-INF theorem because the first-moment law is still an explicit premise.

`TSALLIS-SCHEDULED-CONDITIONAL-MEAN-EXPECTED-GAP` now closes that first
conditional-expectation transport step. The scheduled action probability is
proved measurable on the pre-action trace-prefix sigma-algebra, and a constant
conditional loss-gap law is converted by Mathlib pull-out and total-integral
identities into `HasScheduledExpectedGapLaw`. The existing expected
self-bound, square-root schedule, and logarithmic endpoint therefore accept
the new conditional-mean contract without further finite-sum work.

`TSALLIS-SCHEDULED-INDEPENDENT-MEAN-GAP-REGRET` now supplies the explicit
independence branch. Coordinatewise independence from the pre-action trace and
the corresponding global mean gap imply the conditional-mean and expected-gap
laws, and the generated square-root schedule reaches the existing logarithmic
regret expression. A public `Fin 2` canary exercises that final theorem.

The next narrow producer must now be concrete: choose a stochastic
reward/loss kernel and prove its generated trajectory satisfies the
independence and global-mean premises. Generic conditional-expectation,
self-bounding, schedule, and logarithmic algebra should not be reopened, and
the abstract independence contract must not be reported as the full
stochastic/corrupted Tsallis-INF result.
+
### IID loss-state law transport

`TSALLIS-SCHEDULED-IID-MEAN-GAP-REGRET` now compiles end to end for the concrete
infinite-product model.  Finite `partialTraj` congruence, a measurable finite
loss-prefix extension, and the explicit IID prefix kernel prove
`HasScheduledIIDPrefixKernelFactorization` for the canonical trajectory.
Coordinate independence and exact marginal means then reach the
square-root-schedule logarithmic endpoint without a caller `hfactor`.

`TSALLIS-SCHEDULED-INDEPENDENT-NONIDENTICAL-MEAN-GAP` now generalizes the
time-varying evaluator's process-law layer from one common coordinate law to
`law : Nat -> Measure LossState`. Under a probability instance for every
coordinate and the same finite-prefix factorization, `Measure.infinitePi law`
gives the exact per-round marginal gap under `law t` and independence from the
visible past. The common-law theorem remains a compatibility wrapper. This
closes nonidentical independent latent states, but it does not yet construct a
finite-arm nonstationary reward model or cover history-dependent/conditional
reward kernels.

That model-facing transport now compiles as
`TSALLIS-FINITE-ARM-IID-REWARD-LAW-REGRET` in
`BanditRLProof.TsallisFiniteArmIIDRewardLaw`. Bounded rational arm laws are
combined with `Measure.pi`; pointwise clipping supplies the global loss bounds,
the a.e. unit-interval contract preserves every supplied mean, and
`MeasureTheory.integral_comp_eval` identifies the abstract IID mean gap with
`FiniteBanditModel.gap`. The generated scheduled half-Tsallis endpoint is now
stated directly in reciprocal model gaps.

The first genuine corrupted-process route now compiles as
`TSALLIS-FINITE-ARM-IID-STATIONARY-CORRUPTED-REWARD-LAW-REGRET`.
A fixed per-arm reward shift is clipped to `[0,1]`; unit-interval contraction,
mean-gap transport, and the perturbed expected-gap self-bound produce the
explicit additive budget
`(T+1) * sum_(a != best) (abs (shift a) + abs (shift best))`.
No arbitrary nonnegative corruption parameter remains in the final theorem.

That deterministic time-indexed route now compiles as
`TSALLIS-FINITE-ARM-IID-TIME-VARYING-CORRUPTED-REWARD-LAW-REGRET`.
The new evaluator reads one fresh IID state at round `t` but applies a
deterministic `rewardShift t`; finite-prefix factorization and coordinate
independence produce a time-varying expected-gap law. The final baseline-gap
bound adds exactly
`sum_(t<=T) sum_(a!=best) (abs (shift t a) + abs (shift t best))`, with no
free corruption scalar. Zero schedules have zero budget and constant schedules
recover the stationary budget.

The next theorem route was history-adaptive predictable corruption, with the
shift measurable in the pre-action generated history. That route now compiles
as described below. The deterministic time-indexed theorem alone did not
establish it, and neither theorem is the full corrupted-stochastic Tsallis-INF
paper theorem.

## 2026-07-23 History-Adaptive Corrupted IID Reward-Law Update

The pre-action-history route now compiles. A
`FiniteArmIIDHistoryAdaptiveRewardShiftSource` packages initial and successor
arm shifts, successor joint measurability in finite pair history and arm, and
a deterministic nonnegative envelope. The actual clipped predictable loss is
state-coordinate local, so its canonical trajectory factors through finite
IID state prefixes. On that actual trajectory measure, the uncorrupted
reference loss still has the model-gap expected law. The new reference-gap
self-bound converts the pointwise clipped gap deviation into the explicit
envelope budget, and the final theorem reaches the logarithmic sqrt-schedule
endpoint without a free corruption scalar.

The next honest boundary is stronger corruption semantics: shifts that read
the current action, corruption that changes the latent reward law, or budgets
stated only in conditional expectation need a filtration-aware conditional-law
producer. The compiled theorem does not cover those models and is not the
entire Tsallis-INF paper theorem.

## 2026-07-23 Self-Bounding Interpolation Update

The paper-facing lambda step now compiles in
`TsallisScheduledSelfBoundingInterpolation`. It consumes the generated
scheduled half-Tsallis expected-probability upper estimate and a terminal
`gapMass-C <= regret` contract, exposing the exact pre-optimization expression
`(1+lambda)*upper-lambda*gapMass+lambda*C` for `lambda in [0,1]`.

The finite-action one-time consumer now compiles in
`TsallisConstrainedQuadraticOptimization`: both positive-coefficient quadratic
branches, the simplex square-root mass constraint, and generated expected-
probability wrappers are available. The next narrow leaf is the across-time
threshold decomposition for the scheduled coefficient
`b_t = 2*(1+lambda)*eta_t`. Only after its finite sums compile should the
harmonic/log estimate and joint `lambda` optimization toward the
Masoudian--Seldin square-root-in-`C` theorem be attempted. The current route
does not establish that endpoint.

## 2026-07-23 Square-Root Self-Bounding Optimization Update

The across-time optimization is now compiled in
`TsallisScheduledSelfBoundingOptimization` and
`TsallisSqrtScheduleSelfBoundingOptimization`. Exact active/inactive filters
are converted to a prefix/suffix split, the refined generated
stability/penalty route supplies the correct small base, and Mathlib-backed
inverse-square-root and harmonic integral comparisons produce the closed
`sqrt(cutoff)`/`log((T+1)/cutoff)` regret expression.

The discrete part of the scalar tuning now compiles in
`TsallisSqrtScheduleSelfBoundingTuning`: the continuous threshold is floored,
all rounding and horizon contracts are proved, and `lambda=1` yields an
explicit general corruption theorem with the expected
`T(K-1)/S^2` logarithmic ratio, up to the local coefficient-envelope constants.

The joint local `lambda` optimizer now compiles without Lambert W. The audit of
the existing floor theorem's coefficient `5` yields the corrected local beta
equation with offset `-2`; Mathlib IVT plus an elementary log/square-root
estimate gives quantitative beta-weight bounds, transports beta through
alpha/lambda, identifies the exact floor threshold, and composes with the
generated theorem. The resulting explicit endpoint has local constants and
scales as `sqrt(C*S)` times a logarithmic-radius factor.

The history-adaptive finite-arm IID corruption model now supplies the terminal
self-bound and composes with this refined endpoint. Its deterministic envelope
budget replaces the free `C`, while the IID-prefix/reference-gap law transport
is discharged internally. The concrete `uniformSuboptimalRewardBoostSource`
now closes the first envelope-family consumer: it leaves the best arm fixed,
boosts each other arm by nonnegative `epsilon`, proves exact budget
`(T+1)*(K-1)*epsilon`, derives the compact window from the displayed horizon,
`epsilon*S<=1`, and logarithmic lower-budget conditions, and exposes the
refined model-level theorem with explicit `C`. Its new named regime and
`finiteArmIIDUniformSuboptimalBoostAllRegimeBound` now close the complementary
branch as well: when the refined clauses fail, the final theorem automatically
uses the existing logarithmic `+C` endpoint. Thus every nonnegative `epsilon`
and finite horizon is covered for this source, including zero/small
corruption. The arm-dependent stationary extension now also compiles: a
nonnegative `boost : Fin K -> Real`, with the best-arm shift forced to zero,
has exact budget `(T+1) * sum_(a != best) boost(a)`, and its total theorem
selects the refined or logarithmic branch internally. The deterministic
time-varying extension now also compiles for
`boost : Nat -> Fin K -> Real`, with exact budget
`sum_(t<T+1) sum_(a!=best) boost(t,a)` and the same internal regime split. A
concrete previous-action-gated source now also compiles: at successor time
`n+1` it reads action `n` from the finite pair history and activates the
scheduled boost only when that action equals a fixed trigger arm. The general
measurable-history extension now compiles as well: an arbitrary initial arm
set gates time zero, and every measurable set on `FinitePairHistory × Fin K`
can gate a successor boost. This covers action coordinates and past observed
clipped-feedback/loss coordinates, not current, raw, or latent reward-vector
coordinates. The next route must not redo tuning, law transport, scalar-window conversion,
these exact-budget calculations, or the regime split. It should strengthen
beyond the deterministic full-schedule envelope, or isolate a current-action,
latent-law, or expectation-only corruption transport. The paper's ideal `-1`
equation and sharper constant remain distinct from the compiled local theorem.

## Current Tsallis Expected-Corruption Route

The next requested strengthening is now compiled in
`TsallisFiniteArmIIDHistoryAdaptiveExpectedCorruptedRewardLaw`. The theorem no
longer charges the full deterministic schedule. It uses the generated-policy
budget
`Cexp = sum_t sum_(a!=best) E[p_t(a) *
(|shift_t(a)| + |shift_t(best)|)]`, proves `0 <= Cexp` and
`Cexp <= C_envelope`, and selects the refined or logarithmic branch internally.
The arbitrary measurable history-arm gate has a direct theorem wrapper, so
gate closure and lower conditional selection probability reduce the charged
corruption; zero conditional probability gives zero contribution.

The proof route is stable: sample-dependent reference-gap self-bounding,
realized-shift measurability and integrability, IID-prefix reference-law
transport, expected-budget terminal self-bound, then the existing refined/log
consumers. The public all-regimes theorem now guards the refined branch by both
nonempty suboptimal arms and the compact window, falling back to the logarithmic
branch otherwise. Required caller contracts are still all-time predictable
measurability, probability arm laws, bounded support, exact means, finite
horizon, and suboptimal gaps in `(0,1]`; the gap clauses are vacuous for `K=1`,
whose bound simplifies to `1 + log(T+1)`.

Horizon-local source packaging now compiles in
`TsallisFiniteArmIIDHorizonHistoryAdaptiveExpectedCorruptedRewardLaw`. The
caller supplies initial data plus successor shifts, joint measurability, and
envelope bounds indexed only by `Fin horizon`. A zero extension preserves all
rounds used by the regret theorem and supplies zero shifts/envelopes afterward.
The named budget remains the exact generated-policy expected corruption, not a
deterministic surrogate, and the final all-regimes theorem supports
`horizon=0` and `K=1` without post-horizon or nonempty-suboptimal assumptions.

The next route must not recreate these bridges. Useful remaining forks are
nonpredictable/current-action corruption, raw/latent reward-law transport,
paper-sharp constants, or a different concrete corruption model.

## Independent Nonidentical Finite-Arm Model

`TSALLIS-FINITE-ARM-NONIDENTICAL-REWARD-LAW-REGRET` now compiles in
`TsallisFiniteArmIndependentRewardLaw`. Every `armLaw t arm` may vary with
time if its support remains in `[0,1]` almost surely and its integral remains
the fixed model mean. The route is `Measure.pi` per round,
`Measure.infinitePi` across rounds, exact model-gap identification, canonical
finite-prefix factorization, conversion to
`HasScheduledIndependentMeanGapLaw`, and the existing logarithmic scheduled
half-Tsallis endpoint.

`Tests.Basic` also constructs two genuinely different round laws with the
same mean: a point mass at `1/2` and an equal mixture at `0` and `1`. It proves
the laws differ and instantiates the final theorem with their alternating
schedule.

Do not reopen this route as an IID wrapper. Remaining law-level forks include
time-varying means with an explicit deviation budget, dependent-arm or
conditional kernels, and history-dependent latent reward laws. The free
nonnegative corruption allowance is inherited from the existing endpoint and
is not an independently derived corruption model.

### Nonidentical drifting-mean reward laws

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REWARD-LAW-REGRET` now
compiles in `TsallisFiniteArmIndependentDriftingMeanRewardLaw`. Independent
product arm laws and independent nonidentical rounds are retained, while each
round/arm mean may drift within an explicit deterministic envelope. The
actual gap is identified from product-coordinate integrals, compared with
the fixed baseline gap by a two-arm triangle bound, and transported through
the time-varying expected-gap self-bound. Generated scheduled static-comparator
regret against the fixed `model.bestArm` is then bounded by the baseline
logarithmic reciprocal-gap term plus the resulting finite double sum,
removing the free additive scalar for this model class. This is not dynamic
regret against the best actual arm at each round.

The compact-window refined and all-regimes consumers for this explicit budget
now compile downstream. The next leaf on this route must change a genuinely
different contract: history-dependent/conditional reward laws, dependent
arms, current-action law changes, or a proved source for data-derived
envelopes. Do not rebuild product-law integrals, prefix factorization, the
time-varying expected-gap bridge, or the refined/log branch composition.

### Refined nonidentical drifting-mean regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REFINED-REGRET` compiles in
`TsallisFiniteArmIndependentDriftingMeanRefinedRegret`. The parent module now
exposes the exact generated terminal self-bound. The new module sets
`C = finiteArmIndependentMeanDeviationBudget`, sets `S` to the reciprocal
baseline-gap sum over non-best arms, derives the refined optimizer's scalar
premises from the compact `RefinedLocalCorruptionWindow`, and returns the
coefficient-aware local `sqrt(C*S)` regret expression.

This theorem retains the fixed `model.bestArm` comparator and the independent
nonidentical reward-law construction. It adds nonempty non-best arms, baseline
gaps in `(0,1]`, and the compact window needed by the optimizer, but no new
conditional or history-law regularity. Its all-regimes and actual-mean
dynamic-comparator wrappers now compile downstream.

### All-regimes nonidentical drifting-mean regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-ALL-REGIMES` compiles in
`TsallisFiniteArmIndependentDriftingMeanAllRegimes`. The named total bound
guards the refined expression by both nonempty erased arms and the exact
compact window, then uses the logarithmic explicit-budget theorem on either
complement. The public generated theorem therefore needs neither `hwindow`
nor `hsuboptimal`; the positive-gap and gap-at-most-one contracts are vacuous
for `K=1`, whose bound simplifies to `1 + log(T+1)`.

This closes arm-count and corruption-window branching for the explicit
deterministic mean envelope. This module itself compares with fixed
`model.bestArm`; the actual-mean dynamic-regret extension now compiles
downstream.

### Dynamic regret for nonidentical drifting means

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-DYNAMIC-REGRET-ALL-REGIMES`
compiles in `TsallisFiniteArmIndependentDriftingMeanDynamicRegret`.
`finiteArmIndependentBestArmAt` uses finite argmax existence to select an arm
with maximum actual reward mean at every round. The moving-comparator regret
has an exact fixed-plus-advantage integral decomposition, and model baseline
optimality bounds each actual-mean advantage by the selected and baseline
mean-deviation envelopes.

The public generated theorem adds that explicit dynamic-comparator penalty to
the fixed all-regimes bound. It is an expected predictable-environment result,
not realized sample-path regret. It requires no caller comparator, max certificate,
window proof, or nonempty-suboptimal proof, and the `Fin 1` endpoint remains
exactly `1 + log(T+1)`. Its cumulative actual-mean path-variation
specialization now compiles downstream. Remaining work is a
horizon-compressed or minimax-sharp standard `V_T`/switch-count rate,
conditional/history-dependent or dependent reward laws, paper-level
constants, and the complete Tsallis-INF theorem.

### Law-derived cumulative population-mean path variation

`TSALLIS-FINITE-ARM-NONIDENTICAL-PATH-VARIATION-DYNAMIC-REGRET-ALL-REGIMES`
compiles in `TsallisFiniteArmIndependentPathVariationDynamicRegret`.
For every arm, `finiteArmIndependentCumulativeMeanPathVariation` sums the
absolute consecutive changes of the actual reward mean before time `t`.
An induction using `abs_add_le` and `Finset.sum_range_succ` proves that this
sum controls displacement from the round-zero mean.

When the round-zero actual means equal the baseline model means, the public
generated theorem automatically supplies the parent dynamic theorem's
all-time deviation family. The caller provides no comparator, argmax
certificate, `meanDeviation`, window, or nonempty-suboptimal proof. External
canaries check an exact one-step variation of `1/2`, a genuinely switching
two-arm law, and the exact `Fin 1` endpoint. The bound retains the cumulative
envelope at each included time; it is not yet a compressed or minimax-sharp
standard `V_T` or switch-count theorem.

### Armwise population-mean switch-count dynamic regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
compiles in `TsallisFiniteArmIndependentMeanSwitchCountDynamicRegret`.
The law-level support and probability contracts first imply that every actual
arm mean belongs to `[0,1]`. Consequently each nonzero consecutive mean
change has magnitude at most one. The exact zero-or-one sum over
`Finset.range t` is also proved equal to the real coercion of the filtered
cardinality of changed rounds.

The existing path telescope therefore yields an all-time model-deviation
envelope from this per-arm prefix count, and the generated dynamic-regret
theorem requires no caller comparator, `meanDeviation`, path variation,
switch budget, window, or nonempty-suboptimal proof. External canaries cover
mean range, zero count, an exact one-step count of one, path-to-count
domination, the `Fin 1` endpoint, and the final theorem on an alternating
two-arm law.

This is a law-derived per-arm prefix population-mean count. It is not a
single global environment change-point count, a minimax switch-rate theorem,
an observable/sample-derived count, a compressed standard `V_T` result, or a
realized sample-path bound. Those remain distinct downstream routes.

### Global population-mean change-point dynamic regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
compiles in
`TsallisFiniteArmIndependentGlobalMeanSwitchCountDynamicRegret`. Its global
prefix count records one exactly when at least one arm's population mean
changes between `s` and `s+1`, for `s < t`. The indicator sum is identified
with the real coercion of the corresponding filtered cardinality, and every
armwise switch count is proved no larger than this single global count.

The existing path and initial-model-match adapters therefore generate the
all-time deviation family without caller variation or count data. The final
expected predictable-environment dynamic-regret theorem requires no caller
comparator, armwise count, global switch budget, window, or
nonempty-suboptimal proof. External canaries cover zero and exact one-step
global counts, a law where only arm one changes, the cardinality identity,
armwise and path domination, the `Fin 1` endpoint, and an alternating two-arm
final instantiation.

This closes an exact law-derived global prefix change-point envelope. The
bound still repeats that prefix count at each time in the parent expression;
it is not a minimax or horizon-compressed switch-rate/variation-budget
theorem. That compression, together with realized sample-path and
conditional/dependent-law routes, remains downstream work.

### Horizon-compressed global switch-count logarithmic dynamic regret

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-HORIZON-COMPRESSED-LOG-DYNAMIC-REGRET`
now compiles in
`TsallisFiniteArmIndependentGlobalMeanSwitchCountCompressedDynamicRegret`.
The global prefix count is nonnegative and monotone. Replacing every
time-indexed prefix count by its value at `horizon + 1` bounds both the
fixed-comparator mean-deviation budget and the moving-comparator penalty by

`2 * |Fin K \ {best}| * (horizon + 1) * globalCount(horizon)`.

The exact moving-comparator decomposition and compiled logarithmic
fixed-comparator theorem therefore give a final factor-four terminal-count
term. The public theorem needs probability and unit-support laws, initial
actual/model mean matching, and positive non-best baseline gaps; it does not
need the parent's upper gap bound, caller deviation/count data, a window, or
a nonempty-suboptimal proof. `Fin 1` remains exactly `1 + log(T+1)`.

This closes only the algebraic horizon compression of the existing prefix
envelope. The terminal count excludes the post-horizon `T -> T+1`
transition. The result is linear in both `T+1` and `globalCount(T)`. A
minimax-sharp or sublinear `sqrt(S*T)` switch-rate theorem, sharp standard
`V_T` bound, observable count, realized sample-path result, and
conditional/dependent-law routes remain open.

### Single-switch comparator-route obstruction

`TSALLIS-FINITE-ARM-NONIDENTICAL-SINGLE-SWITCH-DYNAMIC-COMPARATOR-ADVANTAGE-OBSTRUCTION`
now compiles in
`TsallisFiniteArmIndependentSingleSwitchComparatorObstruction`. A concrete
two-arm Dirac law has one permanent population-mean switch: arm zero stays
at mean `1/2`, while arm one moves from `1/4` to `3/4` after round zero.
For every positive horizon `T`, the exact global count is one, the actual
moving-comparator advantage charged by the current decomposition is `T/4`,
and its repeated-prefix envelope penalty is `2*T`.

The square-horizon theorem proves that for every natural coefficient `c`,
`T=(4*c+1)^2` still has one switch while the comparator advantage is larger
than `c*sqrt(T)`. This precisely blocks obtaining a uniform
`sqrt(S*T)` theorem by bounding that term independently. It is not a regret
lower bound or an impossibility result: the next theorem route must either
capture cancellation between fixed-comparator regret and comparator
advantage, or introduce restart, sliding-window, or change-detection
structure.

### Oracle-restart epoch assembly

`TSALLIS-ORACLE-RESTART-EPOCH-DYNAMIC-REGRET-ASSEMBLY` now compiles in
`TsallisOracleRestartDynamicRegret`. For any finite epoch registry containing
every round in the inclusive range `0..horizon`, the moving-comparator regret
against an epochwise comparator is exactly the sum of its epoch-fiber
regrets. Cardinality conservation and finite Cauchy--Schwarz then turn
per-epoch certificates

`C * sqrt(epochLength)`

into `C * sqrt(numberEpochs) * sqrt(horizon+1)`. If the registry has at most
`switches+1` epochs, the compiled public endpoint is
`C * sqrt(switches+1) * sqrt(horizon+1)`.

This is deterministic assembly, not a generated restart algorithm. The
generated selector and trajectory action law now compile in the downstream
module described next. A further downstream module now instantiates the same
fiberwise route with the generated restart probability and the schedule's own
start map. No reward-law or concentration claim is made by this generic
assembly alone.

### Generated oracle-restart trajectory action law

`TSALLIS-ORACLE-RESTART-GENERATED-TRAJECTORY-ACTION-LAW` now compiles in
`TsallisOracleRestartGeneratedTrajectory`. `OracleRestartSchedule` records
whether each successor continues the current epoch or starts a fresh one.
The policy measurably reindexes exactly the inclusive suffix from the epoch
start through the last observed round, resets to the initial half-Tsallis law
at boundaries, and otherwise runs the existing scheduled policy on that
local suffix. The resulting `HistoryAlgorithm`, canonical trajectory kernel,
actual-time probability surface, and successor `condDistrib` theorem compile.
Never-restart reduces to the global scheduled interfaces, while
restart-every-round reduces every successor law to the initial distribution.

The restart-specific predictable-regret surface and direct schedule-fiber
assembly now compile in the downstream module described next. Independent
review found no process-law correctness issue; its metadata, regularity, and
canary observations were resolved.

### Oracle-restart predictable dynamic-regret assembly

`TSALLIS-ORACLE-RESTART-PREDICTABLE-DYNAMIC-REGRET-ASSEMBLY` now compiles in
`TsallisOracleRestartPredictableRegret`. It defines fixed- and
moving-comparator predictable environment regret using
`sampledOracleRestartHalfTsallisProbabilityAtTime`, proves both
never-restart reductions, and proves the fixed-plus-moving decomposition when
`best ∈ arms`.

The finite epoch registry is
`(Finset.range (horizon+1)).image schedule.start`; coverage is automatic.
The moving-comparator regret is exactly the sum of the schedule-aligned epoch
fibers, with no independent `epochOf` or compatibility premise. Pointwise
epoch certificates assemble into
`C*sqrt(numberEpochs)*sqrt(horizon+1)` and, given
`numberEpochs <= switches+1`, into
`C*sqrt(switches+1)*sqrt(horizon+1)`.

Focused and external-canary builds pass. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; independent review found no
P0/P1 issue, and its contract/canary observations were resolved. This leaf
does not prove fresh independent epoch laws, a law-derived bound on the
schedule epoch count, concentration, or final generated dynamic regret. The
fixed-comparator law/expected-regret transport now compiles downstream;
schedule-cardinality derivation remains a separate narrow leaf.

### Oracle-restart epoch-local fixed-comparator regret transport

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-FIXED-COMPARATOR-REGRET-TRANSPORT` now
compiles in `TsallisOracleRestartExpectedRegret`. The generated successor
action law is available after retaining both the environment and complete
global prefix. Restart probabilities are measurable, finite-simplex, and
strictly positive on `arms`, so the generic importance-weighted first-moment
API applies at time zero and every successor time.

Estimated and predictable environment regret have equal integrals on every
actual `schedule.start` fiber under the single global generated trajectory
measure. Point-mass comparators identify that environment surface with the
existing arm-valued epoch regret. The stored-reward importance-weighted
estimator now agrees almost everywhere with the predictable estimator at every
global time and on every epoch fiber. Its point-mass epoch integral therefore
has the same identification. Consequently, expected predictable or
stored-reward estimated-regret certificates `C*sqrt(fiber.card)` assemble
directly into both
`C*sqrt(numberEpochs)*sqrt(horizon+1)` and the explicit switch-count endpoint.
No independent local trajectory or fresh epoch law is assumed.

Focused and `Tests.Basic` builds pass. External canaries instantiate the
per-time first moments, both predictable and observed point-mass epoch integral
equalities, and both expected switch-count certificate consumers. The axiom
audit of the observed bridges and observed switch endpoint reports only `propext`,
`Classical.choice`, and `Quot.sound`. Independent review confirmed the
conditional-law direction, zero/successor split, integrability, point-mass
fiber rewrite, and claim boundary.

## Restart-local score alignment leaf

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-SCORE-ALIGNMENT` is now compiled in
`BanditRLProof.TsallisOracleRestartScoreAlignment`. Its Lean-facing endpoint
shifts the actual generated trajectory to epoch-local time, identifies both
restart probabilities and stored-reward IW losses with scheduled surfaces,
proves every visited schedule fiber is a contiguous translated inclusive
range with matching cardinality, and reuses the scheduled time-varying FTRL
theorem to bound actual observed point-mass epoch estimated regret pathwise by
local stability plus penalty.

The proof uses the restart probability definitions, schedule monotonicity and
idempotence, `Finset.max'`, `Finset.sum_image`, and
`Finset.card_image_of_injective`. Contracts are finite nonempty arms,
decidable actions, a valid deterministic schedule, a positive nonincreasing
local eta sequence, a visited epoch, and best-arm membership. It introduces no
measure, independence, concentration, or fresh epoch law. Focused/root/tests
builds and external canaries pass; public-import axiom audit is baseline only.

The downstream global-law expected transport now compiles.

## Restart-local expected stability transport leaf

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-EXPECTED-STABILITY-TRANSPORT` is compiled
in `BanditRLProof.TsallisOracleRestartExpectedStability`. It conditions on the
environment plus the complete visible global prefix, transports the actual
stored-reward stability term to the predictable local score almost surely,
and applies the existing coarse and refined conditional-distribution
stability APIs. Global time zero is handled separately from successors.

Finite-prior one-round statements retain the correct total-mass factor. Under
a probability prior, the compiled finite-prefix theorem sums the actual
restart-local stability terms to at most `localHorizon + 1`; combining this
with the pathwise FTRL theorem yields an integrable observed epoch
estimated-regret certificate bounded by cardinality plus the deterministic
half-Tsallis penalty. No shifted-law pushforward equality or fresh independent
epoch is assumed.

The exact next blocker is to sum the refined local bounds and tune the local
learning-rate and penalty terms to obtain `C*sqrt(fiber.card)` under the same
global law. The current coarse bound is linear and must not be presented as
the square-root certificate. Law-derived schedule cardinality remains a
separate leaf.

## Restart-local square-root certificate

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-REFINED-STABILITY-TUNING` now compiles in
`BanditRLProof.TsallisOracleRestartRefinedStabilityTuning`. It consumes the
global-law refined transport, the finite-simplex erased-arm square-root bound,
the square-root schedule prefix estimate, and the refined potential-mass
penalty. Every visited actual epoch now satisfies

`E[observed estimated regret on epoch] <=
  (8*sqrt(K))*sqrt(epochRounds.card)`.

The final API requires only a probability prior, the existing measurable
restart model contracts, comparator membership, and epoch membership. It
derives the contiguous local horizon and all eta positivity, small-rate, and
monotonicity obligations internally.

## Generated restart dynamic-regret endpoint

`TSALLIS-ORACLE-RESTART-GENERATED-DYNAMIC-REGRET` now feeds that certificate
into the compiled moving-comparator assembly. The generated square-root
schedule has expected predictable dynamic regret at most
`(8*sqrt(K))*sqrt(scheduleEpochs.card)*sqrt(T+1)`, and at most
`(8*sqrt(K))*sqrt(switches+1)*sqrt(T+1)` when supplied the explicit
`scheduleEpochs.card <= switches+1` contract.

The population-mean oracle successor is now compiled. It defines the concrete
restart policy, derives the epoch-cardinality identity from finite-arm
population-mean change points, proves the epoch-start comparator remains
mean-optimal, and under a.e. `[0,1]` reward support proves it is also optimal
for the clipped loss used by the trajectory. It obtains the independent-law
`8*sqrt(K)*sqrt(S_T+1)*sqrt(T+1)` endpoint without a caller count premise.
This support bridge resolves independent review's raw-mean/clipped-loss
semantic finding.

The next distinct route should replace complete population-mean-law access by
an observable change detector, with explicit delay and false-alarm contracts,
or move to another theorem route. Do not describe the current oracle theorem
as implementable from sampled rewards.

## Canonical `COND-EXPECT-REWARD` Endpoint

The umbrella conditional-reward foundation is now compiled on the canonical
reward-only `trajMeasure`. The endpoint packages, for every successor,
conditional expectation zero and `HasCondSubgaussianMGF`, then exposes the
finite-sum ENNReal Azuma-Hoeffding upper tail for the same zero-initialized
centered process. Conditional MGF exponential integrability is now lowered to
ordinary integrability by a general local Mathlib-facing wrapper, so callers
do not provide `h_integrable`.

The next conditional-reward leaves should consume this endpoint for a specific
arm-wise empirical-mean or confidence route, or separately transport an
arbitrary ambient law. Do not reopen the canonical `partialTraj` construction
or describe this endpoint as a uniform-time confidence or final regret
theorem.

The concrete producer now compiles in
`BanditRLProof.OFULHistoryEnvironmentRewardLaw`.
`OFUL.CanonicalLinearSubgaussianEnvironmentLaw` records theta-norm control and
centered sub-Gaussian MGF laws for the initial arm and every history/action
feedback section. It yields the strict-past residual conditional-MGF field and
the existing successor-gap delta tail. The Real conditional-law bridge uses
rational `Iic` generators, so no `Countable Real` premise was introduced.

The next narrow OFUL route should combine canonical successor indexing with
the compiled selected-width summation and a radius-domination contract.
Initial-round accounting and a bounded bad-event loss envelope remain
separate; this is not complete OFUL regret.

## OFUL Deterministic Foundation

The standard logarithmic determinant-growth and clipped
elliptical-potential conclusions are now packaged by
`OFUL.standardLogDeterminantAndEllipticalPotential`. Consumers no longer need
to assemble rank-one determinant updates, the log-det telescope, trace AM-GM,
and scalar logarithmic simplification separately.

The vector self-normalized theorem, finite-horizon least-squares confidence
ellipsoid, scalar `V_0=lambda I` regularization-bias adapter, and fixed-horizon
finite-action optimism theorem now compile. The next OFUL target is not
another determinant or concentration wrapper: it is a measurable
deterministic tie-breaker and recursive selected-action/feature alignment.
Only after that process layer compiles should the route allocate confidence
over time and assemble selected-width regret.

## OFUL Self-Normalized Route: Current Edge

The fixed-direction deterministic-horizon precursor now compiles as
`OFUL.fixedDirectionCompensatedScore_hasMGFUpperBoundAt`. The local route
freezes each predictable projection inside the conditional kernel, applies
the conditional sub-Gaussian witness, derives all-tilt integrability from a
deterministic projection ceiling, and composes the finite sequence.

The scalar, finite-product, and diagonal-coordinate Gaussian
quadratic-exponential identities now compile in
`BanditRLProof.OFULGaussianMixture`. The terminal diagonal theorem exposes
the inverse square root determinant of `diagonal (1+q)` and its
inverse-diagonal score quadratic form under the exact contract `0 <= q_i`.
It uses the real Gaussian PDF normalization, finite product integral
factorization, and Mathlib diagonal determinant/inverse APIs.

The orthonormal spectral transport now compiles in
`BanditRLProof.OFULGaussianSpectralMixture`. For any real PSD matrix `A`, its
endpoint identifies the `stdGaussian` integral of
`exp(<score,z>-<z,A z>/2)` with
`sqrt(det(1+A))^-1 * exp(score^T(1+A)^-1 score/2)`. The exact contract is a
finite decidable coordinate type, `A.PosSemidef`, and a deterministic score;
no extra nonempty, integrability, or measurability premise is exposed.

The positive-definite covariance transport now compiles in
`BanditRLProof.OFULGaussianCovarianceMixture`. For `V_0.PosDef` and
`G.PosSemidef`, it identifies the `N(0,V_0^-1)` integral with
`sqrt(det V_0 / det(V_0+G)) *
  exp(score^T(V_0+G)^-1 score/2)`.
The proof unfolds Mathlib's multivariate Gaussian pushforward, applies the
standard-Gaussian spectral endpoint to `sqrt(V_0^-1) G sqrt(V_0^-1)`, and
collects the determinant and inverse through one matrix factorization.

The joint-measurability/Tonelli layer now compiles in
`BanditRLProof.OFULGaussianMixtureMeasurability`. It packages the random
quadratic exponential and its `ENNReal` wrapper, proves joint measurability
from measurable scores and coordinatewise measurable Gram entries, and
exposes both generic `SFinite` and `N(0,V_0^-1)` product-lintegral
factorizations. No sample probability, Gram PSD, or integrability premise is
needed for this measure-theoretic rearrangement.

The finite-horizon stochastic bridge now compiles in
`BanditRLProof.OFULFiniteHorizonScoreGram`. It constructs the random score and
variance-weighted Gram, proves the Gram PSD and both processes measurable,
identifies the fixed-direction compensated exponent exactly, and transports
the unit expectation bound across arbitrary probability direction laws and
`N(0,V_0^-1)` as a product `lintegral <= 1`.

The evaluated-mixture bridge now compiles in
`BanditRLProof.OFULGaussianEvaluatedMixture`. It proves Gaussian
square-exponential integrability via Fernique, evaluates the inner
`N(0,V_0^-1)` `ENNReal` integral samplewise under `V_0.PosDef` and
`G_n.PosSemidef`, and exposes the outer determinant-ratio inverse-Gram sample
`lintegral <= 1`.

The Markov/event transport and common-paper scaling now compile in
`BanditRLProof.OFULSelfNormalizedMarkov`. The terminal theorem
`OFUL.measure_finiteHorizon_selfNormalizedQuadratic_gt_two_mul_sq_mul_log_detRatio_div_le`
controls the exact determinant-ratio bad event with radius
`2 * R^2 * log(sqrt(det V_n / det V_0) / delta)`. It is obtained from
Mathlib's `meas_ge_le_lintegral_div`, exact event algebra, and the
`c_i=R^2` Gram/inverse/determinant scaling identities.

The least-squares consumer now compiles in
`BanditRLProof.OFULConfidenceEllipsoid`. The terminal declaration
`OFUL.measure_finiteHorizonRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le`
uses the linear observation identity, exact ridge-error decomposition,
positive-definite matrix norm, determinant-ratio nonnegativity, and event
monotonicity to obtain the finite-horizon confidence ellipsoid directly from
the common-`R` vector tail.

The scalar `V_0=lambda I` adapter now compiles in
`BanditRLProof.OFULScalarRegularizationBias`. It proves the reusable
deterministic bias inequality from scalar positive definiteness, Gram PSD,
finite-sum Cauchy-Schwarz, and energy cancellation, then specializes the
finite-horizon confidence theorem under
`OFUL.euclideanLength thetaStar <= S`. The resulting radius has the standard
`sqrt(lambda) * S` bias term and does not expose a caller-supplied bias cap.

Finite-action optimistic selection now compiles in
`BanditRLProof.OFULFiniteActionOptimism`. Mathlib's positive-definite
matrix-induced inner product yields the weighted dual-norm inequality; a
finite score argmax then gives the one-step comparator-gap bound. The
terminal theorem includes the existence of any fixed-horizon gap violation
into the scalar confidence bad event and preserves its `ofReal delta`
probability bound.

The measurable deterministic tie-breaker and canonical recursive
selected-action/chosen-feature alignment now compile in
`BanditRLProof.OFULMeasurableRecursiveSelection`. The contract is
coordinatewise measurability of the fixed-action optimistic score on each
finite-history space; no confidence or integrability premise is added.

Concrete finite-history state measurability now compiles in
`BanditRLProof.OFULConcreteHistoryRidgeSelection`. The module reconstructs the
scalar-ridge Gram, response vector, estimate, and confidence radius from the
inclusive history, proves each fixed-arm score measurable without an
`hscores` input, and packages the resulting deterministic history algorithm.
Its terminal process theorem identifies the feature of the actual canonical
successor action with the selected ridge-state feature almost surely for any
valid `Thompson.HistoryEnvironment (Fin K) Real`; no feedback-independence
claim is introduced.

Generic deterministic finite-window confidence now compiles in
`BanditRLProof.OFULUniformTimeConfidence`. It unions the fixed-time
scalar-ridge confidence failures over `Finset.range (horizon+1)`, supports an
arbitrary positive schedule bounded by one, and specializes to the exact
equal allocation `delta/(horizon+1)` with total failure probability at most
`delta`. Its sub-Gaussian and response assumptions are horizon-local.

One fixed-process all-time confidence endpoint now compiles in
`BanditRLProof.OFULAllTimeConfidence`. It unions the existing fixed-time
failures over every `n`, proves the reciprocal schedule
`delta/((n+1)*(n+2))` has exact total `ENNReal` budget `delta`, and obtains one
simultaneous deterministic-horizon confidence event by countable
subadditivity. The all-time source contracts are predictable features,
adapted zero-initialized noise, projection domination, and conditional
sub-Gaussian/response laws for every time. No independence, event
measurability, bounded rewards, stopping-time theorem, generated policy, or
regret premise is introduced.

This new theorem is not the existing horizon-indexed algorithm family viewed
as one anytime policy: that family uses a horizon-dependent constant
confidence parameter. The separate scheduled canonical algorithm described
next is therefore required for a one-policy generated theorem.

The scheduled generated theorem now compiles in
`BanditRLProof.OFULScheduledAllTimeConfidence`. It defines one fixed
canonical history algorithm whose selector at history index `n` uses
`allTimeTelescopingDelta delta (n+1)`, derives the strict-past predictable
feature/residual regularity, and transports the countable confidence event to
actual trajectory features. Under
`CanonicalScheduledPredictableScalarRidgeResidualLaw`, both the generated
all-time confidence failure and the event that any successor round violates
its matching optimism-gap certificate have probability at most `delta`.

The model-side law source now compiles as well. Reusable
algorithm-parametric canonical reward bridges expose the initial law under a
Dirac initial-action equality and the successor reward
`condDistrib`/`condExpKernel.map` law. The scheduled step marginal identifies
the selected feedback kernel section, and
`canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment`
transports `CanonicalLinearSubgaussianEnvironmentLaw` to the all-time scheduled
residual source on the same trajectory measure.

The direct confidence and existential successor-gap wrappers therefore accept
the concrete environment law without a manual residual-law premise. The next
narrow theorem is an all-horizon cumulative-gap tail combining these
simultaneous per-round certificates with deterministic radius-times-width
summation on the one scheduled process. Stopping-time evaluation remains a
separate measurable-selection question.

Deterministic selected-width summation now compiles in
`BanditRLProof.OFULSelectedWidthSummation`. The terminal theorem accepts an
arbitrary selected-action sequence and charges time `t` against the prefix
Gram containing only features at `s<t`. It bounds clipped widths at the
standard logarithmic square-root budget and exposes raw widths only under an
explicit `width<=1` contract.

Canonical generated-trajectory state/index and good-event gap transport now
compile in `BanditRLProof.OFULGeneratedTrajectoryConfidenceGap`. Exact trace
lemmas identify inclusive history `n` with generic horizon `n+1` for the
feature Gram, response vector, ridge estimate, and confidence radius. A
selector-independent score-max gap lemma is instantiated by the measurable
strict-fold selector directly, without identifying it with the
`Classical.choose` argmax. The terminal theorem sums the true linear gap over
actual rounds `1,...,horizon`, conditional on the complement of the
equal-share uniform-confidence failure set. It intentionally excludes time
zero, where the algorithm uses its fixed initial action.

The canonical high-probability consumer now compiles in
`BanditRLProof.OFULGeneratedTrajectoryUniformConfidence`.
`OFUL.CanonicalScalarRidgeConfidenceSource` packages the exact filtration,
predictable selected-feature, shifted adapted residual-noise, projection,
conditional sub-Gaussian, parameter-norm, and response-law contracts required
by the generic uniform theorem. Its terminal theorem proves that the strict
successor-gap violation event has canonical measure at most
`ENNReal.ofReal delta`. The algorithm and failure event use the same local
budget `delta/(horizon+1)`, and the event still covers only actual rounds
`1,...,horizon`.

The predictable specialization now compiles in
`BanditRLProof.OFULGeneratedTrajectoryPredictableConfidence`. It defines a
strict-past filtration with level `n+1 = Filtration.piLE n`, constructs the
measurable strict-fold selected-feature modification, proves simultaneous
all-time almost-sure equality with the actual selected feature, and derives
the residual adaptedness, response identity, and finite-action projection
bound internally. The reduced
`OFUL.CanonicalPredictableScalarRidgeResidualLaw` retains only theta-norm
control and horizon-local residual conditional sub-Gaussian MGF witnesses.
The terminal theorem transports the predictable confidence event back to the
actual feature process and proves the same successor-gap violation bound.

The concrete `HistoryEnvironment` producer now compiles in
`BanditRLProof.OFULHistoryEnvironmentRewardLaw` under explicit centered
sub-Gaussian initial and feedback-section laws. Arbitrary Markov kernels still
do not provide this contract automatically.

The deterministic standard radius-width consumer now compiles in
`BanditRLProof.OFULGeneratedTrajectoryRadiusWidth`. It bounds every prefix
confidence radius by a terminal standard log-determinant radius and applies
the selected-width theorem to the full actual action prefix
`0,...,horizon`, with `T = horizon + 1`. The true gap sum remains exactly the
successor window `1,...,horizon`, so no successor-only design matrix is
introduced. Its named violation event has probability at most
`ENNReal.ofReal delta` under the concrete linear-sub-Gaussian environment law.

The base theorem deliberately retains a pathwise raw-width ceiling
`confidenceWidth <= 1`. The normalized downstream consumer now compiles in
`BanditRLProof.OFULNormalizedRadiusWidth`: it proves
`xᵀ V⁻¹ x <= 1` from `xᵀx <= lambda` using positive-definite inverse
cancellation, the exact regularized-Gram energy expansion, and finite
Cauchy--Schwarz. The canonical endpoint derives the premise from the arm norm
bound and `L2 <= lambda`, then exposes the same concrete successor-gap delta
tail without a caller `hwidth`.

The next narrow route leaf is fixed initial-action gap accounting. An expected
bad-event loss envelope follows separately. The compiled tail remains
finite-window and is not a complete OFUL regret theorem.

The fixed initial-action leaf now compiles in
`BanditRLProof.OFULInitialRoundGap`. It charges the canonical time-zero gap by
`2*S*sqrt(L2)`, defines the all-round finite-window budget and violation event,
and transports the event almost surely to the normalized successor tail. The
terminal theorem covers action times `0,...,horizon` with probability bound
`ENNReal.ofReal delta` and no caller `hwidth`.

Its explicit fixed-window pseudo-regret presentation now compiles in
`BanditRLProof.OFULHighProbabilityRegretRate`. For
`B_T=d*log(1+(T+1)*L2/(d*lambda))`, define
`H_T(delta)=B_T+2*log((T+1)/delta)`. The horizon-`T` algorithm runs at
`delta/(T+1)`, and the complete fixed-optimal-arm pseudo-regret exceeds
`2*S*sqrt(L2) + 2*(R*sqrt(H_T(delta))+sqrt(lambda)*S)
*sqrt(T+1)*sqrt(2*B_T)` with probability at most `delta`. This is a
finite-window theorem, not an anytime or simultaneous all-horizon event.
Focused/root/`Tests.Basic` and full checks pass. Independent review found one
retrieval-only named-argument truncation; the bracket-aware declaration scanner
and its CLI regression test now preserve the full strict-event conclusion.

The expected bad-event consumer now compiles in
`BanditRLProof.OFULExpectedRegret`. It proves measurability and integrability
of the full `0,...,horizon` comparator-gap sum, bounds its absolute value by
`(horizon+1)*2*S*sqrt(L2)`, and integrates a measurable violation-set
indicator. The explicit endpoint is
`standardScalarAllRoundGapBound + envelope*delta`.

For a certified optimal fixed arm, the result is nonnegative expected
pseudo-regret. The terminal corollary selects
`delta_T=1/(horizon+1)`, so the envelope contribution reduces to one
`standardScalarInitialGapBound` and no caller delta remains. The finite-window
OFUL expected-pseudo-regret route is therefore compiled. The next narrow OFUL
surface was an explicit closed-form rate presentation, now compiled in
`BanditRLProof.OFULExpectedRegretRate`.

The explicit theorem runs the generated algorithm directly at
`1/(horizon+1)^2`. For
`B_T=d*log(1+(T+1)*L2/(d*lambda))`, it bounds expected pseudo-regret by
`4*S*sqrt(L2) + 2*(R*sqrt(B_T+4*log(T+1))+sqrt(lambda)*S)
*sqrt(T+1)*sqrt(2*B_T)`. No new stochastic contract is introduced.
Focused/root/`Tests.Basic` and full checks pass. Independent review found no
P0/P1 issue; its budget-notation and direct composition-canary findings were
resolved, and the public axiom audit is baseline-only.

The finite-window OFUL confidence-to-expected-regret route and its explicit
rate surface are now compiled. The next narrow surface, implemented in
`BanditRLProof.OFULExpectedRegretAsymptotics`, fixes all model parameters
while the horizon varies and proves that the exact canonical expected
pseudo-regret at algorithm parameter `1/(horizon+1)^2` is
`O(sqrt(horizon+1)*log(horizon+1))` at `Filter.atTop`.

This asymptotic theorem consumes the explicit finite-window bound through
Mathlib `IsBigO` algebra. It does not quantify uniformly over model
parameters. Its theorem-level expected-average consumer now also compiles in
`BanditRLProof.OFULExpectedRegretConsistency`: the complete expected
pseudo-regret divided by `horizon+1` tends to zero. The proof uses the
little-o scale `sqrt(T+1)*log(T+1)=o(T+1)` and introduces no new stochastic
contract.

This convergence is for the horizon-indexed family whose horizon-`T`
algorithm parameter is `1/(T+1)^2`; it is not consistency of one
horizon-independent anytime policy. Future OFUL targets must be stated
separately, such as minimax dependence, anytime confidence/regret, a
simultaneous high-probability all-horizon rate, or a
contextual/dynamic/broader linear model.

## Compiled UCB Selected-Reward Route

The route
`UCB-REAL-STATIONARY-CANONICAL-KERNEL-TRAJECTORY-SELECTED-REWARD-LAW-EXPECTED-AVERAGE-CONSISTENCY`
now compiles. `UCBArmStreamConditionalReward` assembles measurable countable
next-coordinate fibers and branchwise product identities into
`map (historyAction, rewardSucc) (armStreamMeasure nu) =
 map historyAction (armStreamMeasure nu) ⊗ₘ
 (nu.comap Prod.snd measurable_snd)`, then obtains the successor `condDistrib`
law. `UCBRealStationarySelectedRewardConsistency` transports the exact
history/action marginal to the fresh `Kernel.trajMeasure`, proves generated
initial and successor selected-reward laws, and pairs them with the compiled
explicit-policy event and expected-average pseudo-regret convergence theorem.

The generic law route requires only positive finite arms and a Markov Real
kernel. The finite-arm terminal adds pointwise probability laws and armwise
a.s. interval support. Kernel equality is only marginal-a.e.; no global
null-history equality, horizon-indexed process, common interval, caller
selected law, or stronger pathwise/probability/a.s. consistency is claimed.
Literal compatible-toolchain LML import remains separate.

## Compiled RL Occupancy-Regret Route

`BanditRLProof/RL/FiniteHorizonOccupancyRegret.lean` now closes
`RL-FINITE-HORIZON-OCCUPANCY-REGRET`. It recursively composes chronological
state occupancies, proves their probability instances, defines measurable and
nonnegative policy Bellman gaps, and transports continuation-value differences
through the induced next-state kernel using Mathlib map/compProd integrals.
The recursive finite occupancy gap telescopes exactly to optimal value minus
policy value. Combined with the generated trajectory/value identity, this is
exactly expected trajectory regret; it is nonnegative for every Markov policy
and zero for the compiled measurable greedy policy.

The route keeps finite state/action spaces, `Nonempty Action`,
`MeasurableSingletonClass State`, all parent MDP/policy contracts, and a
probability initial-state law. It adds no reward bounds, caller integrability,
optimism, confidence sets, repeated episodes, high-probability event, minimax
rate, or asymptotic claim. The next RL work should introduce a narrow
finite-episode or optimism interface before attempting UCB-VI regret.

## Compiled RL Optimistic Bellman Certificate

`BanditRLProof/RL/FiniteHorizonOptimisticCertificate.lean` now closes
`RL-FINITE-HORIZON-OPTIMISTIC-BELLMAN-CERTIFICATE`. A certificate records an
exact zero terminal upper value and a local inequality above the true optimal
Bellman backup. Bellman monotonicity and backward induction prove global
optimism. For any Markov policy, the upper-minus-policy value difference is
exactly the recursive true-occupancy sum of policy Bellman residuals. A
pointwise bonus bound on those residuals therefore bounds the episode's
expected regret by the corresponding true-occupancy bonus sum.

The canonical certificate is the true optimal value and its residual sum is
proved equal to the previously compiled `occupancyGapRemaining`, preventing a
parallel incompatible semantics. This route is deterministic and
single-episode. Its estimated-model producer now compiles downstream; the
remaining probabilistic work is to derive those model-confidence inequalities
from episode history before attempting cumulative UCB-VI regret assembly.

## Compiled RL Estimated-Model Optimistic Regret

`BanditRLProof/RL/FiniteHorizonEstimatedModelCertificate.lean` closes
`RL-FINITE-HORIZON-ESTIMATED-MODEL-OPTIMISTIC-REGRET`. It stores measurable
stage-indexed reward estimates and radii plus a Markov transition estimate,
recurses an optimistic finite-action Bellman maximum, and requires two-sided
reward and transition-expectation errors only on its generated tail upper
values. The lower error sides construct the true Bellman certificate and
global optimism. The upper sides, after exact stage/remaining selector
alignment, bound the estimated-greedy policy residual by twice its selected
reward-plus-transition radius. The compiled occupancy theorem then gives the
single-episode expected-regret bound.

This is still a deterministic confidence-event consumer. It does not define
empirical counts or estimators, prove a confidence probability, model repeated
episodes, or sum bonuses and martingale noise. The next route should produce
the reward/transition inequalities from finite episode history and a concrete
concentration contract.

## Compiled RL Coordinate Model Confidence

`BanditRLProof/RL/FiniteHorizonCoordinateModelConfidence.lean` closes
`RL-FINITE-HORIZON-COORDINATE-MODEL-CONFIDENCE-REGRET`. Its generic finite
atomic integral lemma turns singleton transition-mass errors and a pointwise
tail-value envelope into an expectation-error bound. The
`CoordinateConfidence` structure aligns these observable coordinate errors
with chronological stages and the recursively generated upper values, covers
their finite sum by the plan transition radius, packages the existing
`Confidence`, and reaches the compiled global-optimism/single-episode-regret
endpoint.

The next narrow route is now the empirical producer itself: finite episode
histories, state-action visit counts, empirical rewards and singleton
transition frequencies, plus a simultaneous concentration event. Clipping or
range contracts, zero-count behavior, event measurability, and failure-budget
allocation must be explicit before introducing cross-episode filtration or
cumulative UCB-VI regret.

## Compiled RL Finite-Batch Empirical Model Confidence

`BanditRLProof/RL/FiniteHorizonEmpiricalModel.lean` closes
`RL-FINITE-HORIZON-FINITE-BATCH-EMPIRICAL-MODEL-CONFIDENCE-REGRET`. Finite
episode-stage records now produce visit counts, reward sums and means, and
next-state counts. The next-state counts partition visits. Positive visit
counts are normalized into a Mathlib `PMF`; zero visits use an explicit
default-state `PMF.pure`. These PMFs form a measurable Markov kernel, and their
singleton Real masses are exposed as the usual count/visit frequencies.

`FiniteBatchModel.plan` derives the estimated reward and transition kernel from
the records. Its `Confidence` states raw empirical reward and singleton-mass
errors, then transports them through the compiled coordinate-confidence route
to global optimism and the selected-radius single-episode expected-regret
bound. The records remain deterministic inputs: no theorem yet says they are
generated by the MDP trajectory law or that their confidence contracts hold
with high probability. The next route should construct a measurable random
episode batch from generated trajectories, identify its coordinate laws, and
prove a simultaneous reward/transition concentration event with explicit
range, zero-count, filtration, measurability, and failure-budget contracts.

## Compiled RL IID Generated-Trajectory Batch Law

`BanditRLProof/RL/FiniteHorizonIIDTrajectoryBatch.lean` closes
`RL-FINITE-HORIZON-IID-TRAJECTORY-BATCH-LAW`. A finite `Measure.pi` product of
one fixed policy's genuine trajectory law now maps measurably into
`EpisodeBatch`. Every episode/stage record has the expected single-trajectory
pushforward law, while records, arbitrary measurable record statistics, and
the named visit/reward/transition contributions are independent across
episode coordinates. Record/statistic independence is available directly
under the mapped `iidEpisodeBatchMeasure`; contribution independence remains
available on the source trajectory product law. The existing batch visit
counts, reward sums, and transition counts are definitionally the finite sums
of those contributions. Independent review's mapped-law and API-ownership/test
findings are resolved, and the public axiom audit is baseline-only.
The full project gate passes (root 3497 jobs, Tests 3499 jobs, 15 CLI tests
with one expected skip).

This route intentionally fixes one Markov policy for all episodes and inherits
the current MDP's deterministic reward field. The next narrow route is a
fixed-stage iid concentration producer: cast visit and transition indicators
to `Real`, center them around their integrals, apply a bounded finite-sum tail,
and only then form a simultaneous finite stage/state/action/next-state event.
Adaptive episode policies, positive random denominators, empirical ratios,
filtration, confidence allocation, cumulative regret, and UCB-VI remain open.

## Compiled RL IID Fixed-Coordinate Count Confidence

`BanditRLProof/RL/FiniteHorizonIIDCountConcentration.lean` closes
`RL-FINITE-HORIZON-IID-COUNT-CONFIDENCE`. Measurable Real visit and
state-action-next-state indicators are centered at their genuine
single-trajectory integrals. The mapped episode marginal theorem identifies
the same mean at every episode coordinate, and mapped-batch statistic
independence survives centering. Exact finite-sum identities rewrite these
sums as the Real cast of the named visit or transition count minus `episodes`
times its mean.

The transition center is explicitly named `stageTransitionJointProbability`:
it is the joint mass of `(state, action, nextState)`, not a conditional
transition probability. Both means are identified with measurable trajectory
events, lie in `[0,1]`, and the joint mass is bounded by the visit mass. The
module also exposes the exact proxy identity `episodes / 4`, measurable Real
counts/deviations, and measurable fixed-coordinate bad events for the next
finite-union route.

Mathlib's bounded-variable Hoeffding lemma supplies proxy `1/4` per episode;
the compiled two-sided independent-sum theorem gives each fixed coordinate a
failure probability at most `delta` for `0 < delta <= 1` and positive episode
count. The bundled endpoint is deliberately a conjunction of two marginal
tail inequalities, not a probability bound for their union. The next theorem
route should enumerate the finite stage/state/action/next-state registry and
allocate a shared failure budget. Positive visit denominators, empirical
transition ratios, reward confidence, adaptive episode policies, cumulative
bonus control, and UCB-VI remain separate.

Independent review found no P0/P1/P2; its public-contract, canary,
measurability, and ledger P3 findings are resolved. Focused, root, Tests, CLI,
axiom, retrieval/index, and full project gates pass.

## Compiled RL IID Eligible Visit-Count Positivity

`RL-FINITE-HORIZON-IID-ELIGIBLE-VISIT-COUNT-POSITIVITY` is compiled. For an
arbitrary finite set of eligible stage/state/action coordinates, the genuine
expected count must strictly exceed the common simultaneous radius. On that
contract, zero realized count contradicts the compiled strict deviation
bound. The eligible zero-count union is measurable, is included in the
simultaneous bad event, and inherits its global-delta tail under the same
mapped fixed-policy iid batch law. Its exact complement directly exposes all
eligible Nat counts as positive.

Eligibility avoids the false full-support claim that every state-action pair
must be reached. Zero horizon and empty eligible sets remain vacuous. This
route supplies positive denominators only. The next route must identify the
generated joint-transition probability with visit probability times the true
transition-kernel singleton mass. Empirical conditional ratios follow only
after that law transport; reward confidence, adaptive policies, cumulative
bonuses, and UCB-VI remain downstream.

## Compiled RL IID Simultaneous Count Confidence

`RL-FINITE-HORIZON-IID-SIMULTANEOUS-COUNT-CONFIDENCE` now indexes both visit
and joint-transition coordinates in one finite sum type, uses the compiled
fixed-coordinate tails at the equal share
`delta / Fintype.card CountCoordinate`, and applies the existing Mathlib-backed
finite outer-measure union wrapper. The compiled endpoint exposes one
global-delta bad union plus strict coordinatewise deviation bounds outside it.

The proof explicitly splits empty and nonempty coordinate types, so an MDP
with zero horizon has an empty union and needs no artificial positive-horizon
assumption. The route remains fixed-policy iid and count-only. Denominator
positivity, conditional transition ratios, reward confidence, adaptive
episode policies, anytime control, cumulative bonuses, and UCB-VI remain
downstream. The next narrow route is deterministic margin-to-positive-visit
count transport on the simultaneous good event; empirical conditional ratios
remain a later route.

## Compiled RL Stage-Transition Joint Factorization

`RL-FINITE-HORIZON-STAGE-TRANSITION-JOINT-FACTORIZATION` identifies the named
generated joint-transition probability exactly as the stage visit probability
times `(mdp.transition (state, action) {nextState}).toReal`. The module owns
relative trace coordinate maps, proves the head law by `Kernel.fst_compProd`
and singleton `compProd`, and reaches arbitrary stages by recursive-kernel
induction. The identity remains valid at zero occupancy; no support or
denominator premise is introduced. It is consumed by the eligible empirical
transition-confidence route below.

## Compiled RL Eligible Empirical Transition Confidence

The fixed-policy iid RL route now converts the shared visit/joint count event
into empirical transition singleton confidence on any finite eligible registry.
The public endpoint retains the same global-delta event and proves the strict
random-denominator radius `2 * simultaneousCountConfidenceRadius / visitCount`
for every eligible coordinate and every next state. Eligibility is exactly the
previous strict expected-count margin, so unreachable coordinates are not given
a false denominator guarantee.

## Compiled RL Generated Empirical Reward Exactness

The generated-batch route now reflects the actual deterministic reward surface:
`episodeBatchOfTrajectories` is reward-consistent, its reward sum is visit count
times `mdp.reward`, positive-count empirical reward is exact, and mapped iid
batches have this consistency almost everywhere. The same
simultaneous-count event therefore supplies zero reward error and the existing
eligible transition singleton bounds without an extra reward tail budget.

The deterministic known-reward `FiniteBatchModel.Confidence` producer described
here is now complemented by the fixed-policy stochastic sampled-reward route at
the top of this document. Adaptive history transport and explicit calibration
remain downstream; do not claim full confidence from caller-selected eligible
coordinates or from a self-referential envelope.
