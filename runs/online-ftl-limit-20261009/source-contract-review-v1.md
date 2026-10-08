# FTL limit source CONTRACT review v1

Verdict: accepted-with-explicit-delta, for the five exact proposed types and bounded future proof scope only. No new theorem body is certified.

The reviewer /root/source_reviewer is a reused distinct automated actor with prior staged source-review history, distinct from formalizer and decoder. Requested GPT-6 Astra/medium is not runtime-attested; no human/external/absolute-blind claim.

All48 fixed RAW inputs were independently hashed before/after. The cached v10 PDF independently matches cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Original PDF14/16/18 PNGs were personally viewed at requested original detail and their supplied source text read. Printed2 distinguishes hindsight fixed minimum, fixed-comparator regret and displayed ordinary-limit nonpositivity; printed4 states Theorem1.3 for actual half-initialized strict-past means with4+4lnT; printed6 concludes sublinearity. None prints these five new hinge statements.

Actual reused definitions agree with neutral reconstruction: empiricalMean0=0, meanPredict0=1/2, comparatorRegret is a difference of finite sums, squaredBestRegret uses the actual interval loss-image infimum, and LimitNoRegret quantifies a possibly comparator-dependent finite nonpositive ordinary limit. Existing upper-epsilon NoRegret is different. Decoder reconstructs these distinctions correctly and is not itself a source/proof verdict.

F1 — accepted-with-explicit-delta

- objects: Actual meanPredict, real observation stream and horizon empirical mean
- quantifiers: forall real y, every natural T
- assumptions: None: no bounds, feasibility or positive T
- metric: 0 <= loss(actual strict-past predictor)-loss(prefix mean)
- normalization: Finite sums t<T; T0 both sums0
- information_probability: Deterministic; initial1/2 then exactly past t observations
- boundary: Derived global-real statement; not arbitrary-predictor nonnegativity or unit-game feasibility

F2 — accepted-with-explicit-delta

- objects: Same actual predictor, fixed real u and horizon mean
- quantifiers: forall y,u,T
- assumptions: None
- metric: R_T(u)=R_T(mean_T)-T*(u-mean_T)^2
- normalization: Exact signed identity including empty T0
- information_probability: Same strict-past plays on both sides; hindsight mean analysis-only
- boundary: Derived algebra; fixed regret can be negative

F3 — accepted-with-explicit-delta

- objects: Unit observations, same predictor, actual interval-loss minimum
- quantifiers: forall infinite y satisfying all-time support; T tends infinity
- assumptions: Every y_t in closed[0,1]
- metric: squaredBestRegret/T tends ordinary real0
- normalization: Real division by T, eventual T>0; totalized T0 irrelevant
- information_probability: Deterministic pathwise result, no expectation
- boundary: Derived squeeze from new actual nonnegative gap and printed4+4logT; no fixed-u convergence implied

F4 — accepted-with-explicit-delta

- objects: Same bounded stream, every real comparator and candidate real limit
- quantifiers: forall y with support, forall u,a
- assumptions: Support only, no convergence or sign premise on a
- metric: R_T(u)/T tends a iff squared distance(u,mean_T) tends -a
- normalization: Normalized decomposition only eventually T>0; no identity at T0 claimed
- information_probability: Same infinite causal predictor, no probability
- boundary: Exact criterion, no unconditional existence; one squared-distance convergence need not mean empirical-mean convergence

F5 — accepted-with-explicit-delta

- objects: Bounded stream, supplied empirical-mean limit m, same actual predictor
- quantifiers: forall y/support,m/convergence; then all real u and comparator-wise existential limit
- assumptions: Explicit ordinary empiricalMean convergence hm
- metric: All fixed-u limits equal -(u-m)^2; LimitNoRegret on[0,1]
- normalization: Ordinary finite-real limit, possibly strictly negative; T0 irrelevant
- information_probability: m never algorithm input; deterministic and no IID assumption
- boundary: Sufficient conditional source reconciliation, not all bounded streams or a common comparator-independent limit

Plausibility audit: F1 has a genuine prefix-minimum induction route. If M_T is the minimal cumulative square loss, evaluating the new prefix objective at the previous minimizer gives M_(T+1)<=M_T+(mean_T-y_T)^2 for T>0, while the first actual loss is nonnegative and M_1=0. Thus the desired lower bound is produced, not an assumed regret oracle; the printed Be-the-Leader inequality alone has the opposite comparison and must not be substituted for this argument. F2 is the existing global square decomposition plus an explicit empty-prefix case. F3 uses produced feasible minimum equality and F1 to squeeze against the vanishing printed logarithmic upper bound. F4 then follows from the eventual positive-horizon normalized F2 and F3 in both directions. F5 follows by continuity of the squared distance and supplies each comparator its own negative-square witness. No mathematical counterexample to these exact statements was found.

Important source delta: F5 adds genuine empiricalMean convergence; neither the printed arbitrary-stream bound nor existing meanPredict_noRegret supplies it. F4 asserts no limit exists. The existing affine time-unbounded signed-loss counterexample is not a bounded squared-loss actual-FTL counterexample. A bounded oscillating-mean example and all-comparator converse remain required source-reconciliation work, explicitly open; this contract does not close that gap. No min/expectation interchange, stochastic rate, oracle knowledge or arbitrary algorithm claim is present.

The draft check reports five closed Prop types and exit0, with unused-variable warnings in the proposition declarations. This is type elaboration only, not compiled theorem bodies. API checks support the proposed route, not its successful implementation. Renderer missing-pypdfium2 failure and Poppler-only repair are retained; no source/type change or installation is inferred. Proposed canary is still a plan: actual binary counts/mean convergence and all five instantiations must be proved after its separate header freeze/review.

Future permission is exactly the copied contract-mutable-scope-v1 object: two new scoped files, bodies under frozen headers, separately reviewed canary contract, own append-only stage evidence and own native journals. Existing modules/pins/global frontier/memory remain immutable. Root/Test imports and reader/registry/contribution integration need separate BODY integration review. Target edits require a new contract review. No proof/native/publication action was executed here.

R1–R7 below are future requirements, not discharged reader gates:

R1: Pinned source ordinary-limit display and source4log upper stated separately; five derived hinges, not five printed theorems.

R2: Actual same meanPredict initialized1/2 with strict past; F1/F2 arbitraryreal streams/algebra do not assert unit-game feasibility there.

R3: F1 actual nonnegative loss gap produced from prefix minimum; no lower-bound oracle. F3 actual interval-minimum best/T tends0 via source upper +F1.

R4: F2 exact signed comparator identity with minusT*square and emptyT0; F4 everyreal comparator/limit target, iff square-distance converges to negative target.

R5: F5 extra empiricalMean convergence explicit, all-real fixed limits negative square; no unconditional finite ordinary limit for arbitrary bounded streams or mean known to algorithm.

R6: Nondegenerate periodic binary publiccanary derives empiricalMean convergence and positive bestregret/strictnegative comparatorlimit; all5 endpoints, frozenheaders/axioms/rootTests/harness/site/shadow separately verified.

R7: Abstract unbounded-affine counterexample doesnotsettle bounded actualFTL; actualbounded oscillation/exactall-comparator converse remain source-reconciliation obligations. Original16/null/wholeGoalACTIVE, no chapter/main/live closure.

Required blocking mathematical/metadata repairs: none. BODY/canary/kernel/combined/root/Tests/harness/site/pixels/FINAL/native/delivery remain pending. Original16/null proof total, remaining source reconciliation, all required chapters/appendices and whole active Goal remain open.
