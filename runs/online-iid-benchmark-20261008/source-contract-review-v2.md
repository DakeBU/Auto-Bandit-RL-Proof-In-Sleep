# IID expected-fixed benchmark: CONTRACT v2 source review

Verdict: **accepted-with-explicit-delta**, for source/type stabilization only. No target proof body, reader integration, source package, native acceptance or publication is accepted.

Actor `/root/source_reviewer` is distinct from the formalizer and decoder and has prior staged source-review history. Requested GPT-6 Astra / medium; runtime model/effort are not attested. This is not absolute blindness, human or external review.

All 186 fixed raw input rows were independently hashed before and after review with no mismatch. Both original source PNGs (PDF13/printed1 and PDF14/printed2) were actually viewed. The pinned PDF SHA is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Source equations concern expected loss minus the minimum of expected FIXED loss, not expected hindsight minimum.

The v2 revision changes ONLY I005 and I008: output feasibility is conditional on all supplied strict-past coordinates being in [0,1]. Six other raw headers and complete definitions are unchanged. This removes an unnecessary off-domain restriction without changing conclusions. Measurability remains global on the finite real product. A.s. outcome support must yield a.s. legal actual histories and L2 predictions; it must not be upgraded to pointwise support.

The effective draft-neutral-identities-v2.lean checks eight closed propositions at the same arbitrary universe u and four complete definition identities; actual exit is zero. These rfl equalities prove correspondence of proposition TYPES, not the proposed results. Earlier unconstrained-universe failure and preparer missing-path failure remain historical; v1 was not stabilized.

The read reused Stochastic/History/Information/IID/FTL/Mean bodies distinguish actual history/current independence from consumers. In particular, older pointwise-bounded meanPredict_memLp/iid_meanPredict_excess/source_mean_optimal and all-real-tuples history APIs cannot discharge the new a.s./legal-history targets by silently strengthening their premises. The proposed dependency route is plausible; its finite-integrability, attainment and causal bridges remain actual BODY obligations.

## I001 — BanditRL.OnlineLearning.expected_fixed_prefix_decomposition
Verdict: accepted-with-explicit-delta
- objects_spaces: Common outcome family; fixed real comparator u.
- quantifiers_order: Common assumptions then every natural T and every real u.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. No independence and no feasibility restriction on u.
- conclusion_metric: Expected fixed cumulative square loss = T variance + T squared distance from the population mean.
- constants_normalization_indexing: Range T is source rounds 1 through T; real multiplier T, no averaging.
- probability_information: One comparator across all samples/times; no learner involved.
- boundary_source_delta: T0 permitted. Derived decomposition supports source benchmark; not a printed separate theorem.

## I002 — BanditRL.OnlineLearning.expected_fixed_prefix_minimum
Verdict: accepted-with-explicit-delta
- objects_spaces: Population mean and real image of feasible fixed expected losses.
- quantifiers_order: Common assumptions then every T; IsLeast contains attainment and every lower comparison.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. No independence.
- conclusion_metric: Mean feasible AND IsLeast of the generally infinite image at T variance.
- constants_normalization_indexing: Closed [0,1], same T and variance Y0.
- probability_information: Minimum outside expectation; mean is fixed, not sample-dependent hindsight.
- boundary_source_delta: T0 all feasible comparators tie; no uniqueness. Membership must be produced, not only a lower bound.

## I003 — BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance
Verdict: accepted-with-explicit-delta
- objects_spaces: Complete expectedFixedMinimum infimum definition.
- quantifiers_order: Common assumptions then every T.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. No independence.
- conclusion_metric: Infimum equals T variance.
- constants_normalization_indexing: Unnormalized finite prefix; same reference law.
- probability_information: No min/integral exchange; IsLeast route supplies csInf legitimacy.
- boundary_source_delta: T0 zero; totalized definition alone is not this theorem.

## I004 — BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition
Verdict: accepted-with-explicit-delta
- objects_spaces: Supplied real random predictions and outcomes.
- quantifiers_order: Common assumptions, P, all-time MemLp and pairwise contemporaneous independence, then T.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. P in L2 and IndepFun(Pt,Yt) supplied; no feasible P or joint Y independence required.
- conclusion_metric: Cumulative expected loss minus T variance equals sum of expected squared deviations.
- constants_normalization_indexing: Squares, range T, no division.
- probability_information: Consumer of independence, not an algorithm/causality producer.
- boundary_source_delta: T0; real predictions may lie outside [0,1]. This helper cannot alone close source algorithm claims.

## I005 — BanditRL.OnlineLearning.history_policy_expectedFixed_excess
Verdict: accepted-with-explicit-delta
- objects_spaces: Measurable finite strict-history policy and its actual outputs.
- quantifiers_order: Common assumptions, joint independence, policy, all-time measurability and legal-tuple conditional feasibility, then T.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. iIndepFun; hpb only when all past tuple coordinates lie in [0,1].
- conclusion_metric: Same actual expectedFixedRegret equals deviation sum AND is nonnegative.
- constants_normalization_indexing: Source1/Lean0; empty history output feasible but not necessarily 1/2.
- probability_information: Only indices i<t supplied. Actual history support, prediction L2 and current-target independence must be derived; no consumer premises for them.
- boundary_source_delta: T0 allowed; off-cube outputs unconstrained by hpb. Deterministic finite-history scope, not external-seed/general-filtration closure.

## I006 — BanditRL.OnlineLearning.meanPredict_expectedFixed_excess
Verdict: accepted-with-explicit-delta
- objects_spaces: Actual existing meanPredict on the same outcome sample path.
- quantifiers_order: Common assumptions and joint independence, then every T.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. iIndepFun; no assumed prediction L2 or independence.
- conclusion_metric: Actual meanPredict expected excess identity AND nonnegativity.
- constants_normalization_indexing: Initial 1/2; at t>0 exactly average of i<t, not population mean.
- probability_information: Actual producer must derive a.s. boundedness/L2 and current independence. Old pointwise IID APIs cannot be silently substituted.
- boundary_source_delta: T0/T1 included; no convergence rate or success-equivalence terminal.

## I007 — BanditRL.OnlineLearning.constant_mean_expectedFixed_excess_zero
Verdict: accepted-with-explicit-delta
- objects_spaces: Distribution-dependent constant population-mean predictor.
- quantifiers_order: Common assumptions then every T; predictor fixed by measure/law.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. No independence.
- conclusion_metric: Mean feasible AND its expectedFixedRegret is exactly zero.
- constants_normalization_indexing: Same population mean at every time, unnormalized.
- probability_information: Oracle comparison, not an unknown-law implementable learner.
- boundary_source_delta: T0 and degenerate distributions allowed; no uniqueness or estimation guarantee.

## I008 — BanditRL.OnlineLearning.history_policy_normalized_expectedFixed_excess
Verdict: accepted-with-explicit-delta
- objects_spaces: Same legal strict-history prediction path and its average expected excess.
- quantifiers_order: Common assumptions, joint independence, policy/hp/conditional hpb, then T>0.
- assumptions_regularity: Arbitrary-universe measurable probability space; measurable real outcomes with the law of Y0 and a.s. [0,1] support at every time. Same legal-history feasibility as I005; positive horizon explicit.
- conclusion_metric: Expected cumulative loss divided by T minus variance = expectedFixedRegret/T.
- constants_normalization_indexing: Real denominator T on both sides; no T+1.
- probability_information: Finite normalization identity, no almost-sure/high-probability/limit result.
- boundary_source_delta: T0 deliberately excluded: left would be minus variance under totalized division. Asymptotic success equivalence remains required.

## Complete definition expectedFixedMinimum
Verdict: accepted with the stated totalization boundary.
- objects_spaces: Arbitrary measurable space/measure, real outcome sequence and natural horizon.
- quantifiers_order: Definition parameters then image over fixed u in [0,1].
- assumptions_regularity: No probability, measurability, support or integrability hypotheses in bare definition.
- conclusion_metric: Real sInf of expected fixed cumulative losses.
- constants_normalization_indexing: Range T; squared loss; no averaging.
- probability_information: Expectation before optimization, fixed comparator across samples.
- boundary_source_delta: Totalized integral/infimum outside theorem premises; no automatic attainment or performance; T0 empty extension.

## Complete definition expectedFixedRegret
Verdict: accepted with the stated totalization boundary.
- objects_spaces: Same measure/outcomes plus arbitrary prediction sequence.
- quantifiers_order: Supplied Y, prediction and T; no hidden policy quantifier.
- assumptions_regularity: No causal, feasible, independent or integrable premise in bare definition.
- conclusion_metric: Expected prediction cumulative loss minus expectedFixedMinimum.
- constants_normalization_indexing: Signed real excess; range T and no averaging.
- probability_information: Arbitrary traces are not causal algorithms; nonnegativity belongs to proved qualified terminals.
- boundary_source_delta: Could be negative without causal hypotheses; no expectation of hindsight minimum or asymptotic result.

## Required later reader and proof obligations
These exact R1–R9 requirements are retained, not discharged by CONTRACT:
- R1: Keep minimum of EXPECTED FIXED cumulative loss outside integration; never replace it by expectation of the hindsight minimum or pathwise square regret.
- R2: Preserve probability normalization, measurable observations, a.s. unit support and derived L2/integrability; no silent pointwise strengthening or totalized-integral performance claim. Policy feasibility is required only on legal unit-interval strict-history tuples; actual history support and prediction L2 must be produced a.s.
- R3: Produce actual feasible distribution-mean image membership and all lower comparisons before real csInf; generally infinite image, T0 empty extension without uniqueness.
- R4: Same-law fixed benchmark needs no independence; causal performance requires joint target independence and actual current-target independence derived from strict history or meanPredict.
- R5: I004 is only a supplied-independent-prediction intermediate with two real causal consumers; standalone definitions/arbitrary traces cannot certify algorithm existence or nonnegative expected excess.
- R6: Actual meanPredict starts at1/2 then exact strict past; fixed distribution-mean optimum knows the law and is not an unknown-law learning implementation.
- R7: Deterministic finite-history policy scope is explicit; randomized/general filtration coverage remains mandatory audit work. Do not label all strategies or full source/chapter complete from this package.
- R8: Keep source1..T/Lean0..T−1, T0 extension, positiveT average denominators, actual nondegenerate IID canaries and same-prefix processes; no asymptotic-success or high-probability claim.
- R9: Reuse shared Lean graph/registry and exact old declarations; source, draft/type, actual body, kernel/canary/combined/harness/site/FINAL/native/PR gates separate. Original16C1items/proof-totalnull, five old module audits, C1/C2/program open,3–16/appendices required; OPENunmergedPR193 stack is not main/live.

Required mathematical repairs: none. Required metadata repairs: none. Blocking repairs for this bounded contract: none.

Eight derived producers/representations/adapters are not eight printed theorems. Deterministic finite-history coverage is explicitly partial; independent external-seed/general-filtration algorithms and source asymptotic-success equivalence remain REQUIRED. Subsequent actual bodies, nondegenerate canaries, kernel/header/dependency checks, root/Tests/harness, reader/site/FINAL/native/PR gates remain pending. Five older main-relative module audits remain unwaived; original sixteen Chapter1 items have null proof total, Chapters1/2 remain incomplete, Chapters3–16 and necessary appendices remain required, whole Goal ACTIVE. PR193 is an unmerged stack reference, not main/live acceptance.

Raw input inventory is preserved in the accompanying receipt; hashes refer to bytes, without newline normalization.
