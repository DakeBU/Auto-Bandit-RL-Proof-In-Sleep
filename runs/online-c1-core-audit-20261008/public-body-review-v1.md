# C1 core BODY review

Verdict: accepted-with-explicit-delta, limited to the actual retained public proof bodies and current validation canaries. No blocking mathematical or metadata repair found.

Actor /root/source_reviewer is a reused distinct automated staged reviewer with prior CONTRACT and other source-review history. GPT-6 Astra / medium is the requested setting, not independently attested runtime. This is not absolute blindness, external or human review.

All 185 fixed raw inputs were independently read and SHA-256 checked before and after review. All 93 original CONTRACT rows resolve exactly, using the nine immutable baseline snapshots where appropriate. The five current public files equal their original byte sequences with precisely the approved comment inserted before the namespace; current whole-file hashes legitimately differ. Every old theorem/header/proof byte is preserved. The pinned v10 PDF hash is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Original-detail source PNGs PDF13–16 were personally viewed and the text reread. Printed4/PDF16 is the supplied-minimizer Lemma1.2; the remaining eleven APIs are derived/generic/regularity results.

## A001 BanditRL.OnlineLearning.lemma_1_2

- objects: Arbitrary ambient X, V, real losses and supplied leaders
- quantifiers: All positive n<=T feasible and minimizing against every u in V
- assumptions: hmem and hmin both required; no minimizer existence theorem
- terminal: Sum of current-prefix-leader losses <= final-prefix-leader cumulative loss
- normalization_and_boundaries: Source t1 maps loss0, leader(t+1); T0 empty extension
- information_structure: Hindsight current-prefix objects, not causal predictions
- source_delta: Euclidean source generalized to arbitrary type/ambient extension; exactly one printed Lemma1.2

Actual body: Actual Nat induction chains the earlier prefix comparison with hmin at n and hmem of leader(n+1). Zero is empty and one identical. Neither prefix minimizers nor their feasibility are manufactured. Verdict: accepted-with-explicit-delta.

## A002 BanditRL.OnlineLearning.expected_square_decomposition

- objects: Real L2 target on arbitrary probability space and real fixed u
- quantifiers: Every real u, including outside[0,1]
- assumptions: Probability and MemLp2; no support or independence
- terminal: E(u-Y)^2=VarY+(u-EY)^2
- normalization_and_boundaries: Square2, no horizon
- information_structure: Fixed comparator outside expectation; mean is law dependent
- source_delta: Derived generic identity, not numbered source or minimizer-existence API

Actual body: variance_eq_sub on const-minus-Y, variance_const_sub and integral_sub use derived L1 from MemLp2; scalar rearrangement proves the exact all-real comparator identity. Verdict: accepted-with-explicit-delta.

## A003 BanditRL.OnlineLearning.independent_prediction_square

- objects: Real L2 P,Y on probability space
- quantifiers: Every P,Y satisfying supplied independence
- assumptions: Both MemLp2 and IndepFun P Y
- terminal: E(P-Y)^2=E(P-EY)^2+VarY
- normalization_and_boundaries: No time/rate
- information_structure: Consumes independence; does not derive causality
- source_delta: Derived identity only; no universal strategy class

Actual body: variance_sub and independence covariance zero, together with the centered variance identity and legitimate integral subtraction, produce the decomposition. This remains an independence consumer. Verdict: accepted-with-explicit-delta.

## A004 BanditRL.OnlineLearning.meanPredict_independent

- objects: Infinite measurable jointly independent target family, actual meanPredict
- quantifiers: All natural t
- assumptions: Probability, coordinate measurability, joint independence; no common law/bounds
- terminal: Actual meanPredict independent of current Yt
- normalization_and_boundaries: Initialhalf at0; mean firstt thereafter
- information_structure: Derived via sum-range independence and measurable division; zero constant
- source_delta: No random kernel representation; source initialhalf specialization p4

Actual body: At zero constant-half independence; otherwise joint-family independent finite past sum, measurable division and actual meanPredict unfolding produce current independence. Verdict: accepted-with-explicit-delta.

## A005 BanditRL.OnlineLearning.meanPredict_measurable

- objects: Measurable target sequence and actual predictor
- quantifiers: All t
- assumptions: Only measurable coordinates; no measure/probability
- terminal: Actual prediction measurable
- normalization_and_boundaries: Initialhalf/strictpast branches
- information_structure: Finite sums/division, not supplied prediction measurability
- source_delta: Derived regularity, not performance

Actual body: Unfolds actual meanPredict/empiricalMean and proves both constant and finite-sum branches measurable. No probability premise is smuggled in. Verdict: accepted-with-explicit-delta.

## A006 BanditRL.OnlineLearning.meanPredict_memLp

- objects: Probability process and actual predictor
- quantifiers: Every sample point and all times bounded, all t
- assumptions: Measurability plus pointwise[0,1]; no independence
- terminal: Prediction MemLp2
- normalization_and_boundaries: Initialhalf and bounded finite means
- information_structure: Bounded actual prediction producer
- source_delta: Pointwise stronger than AE; do not silently substitute later AE API

Actual body: Actual meanPredict_mem supplies a pointwise interval bound; measurable predictor and memLp_of_bounded yield L2. Strong pointwise target premise is retained. Verdict: accepted-with-explicit-delta.

## A007 BanditRL.OnlineLearning.iid_meanPredict_excess

- objects: Probability jointly IID process and same meanPredict
- quantifiers: All T; same infinite process before horizon
- assumptions: Measurable, joint independent, same-law, pointwise unit support
- terminal: Variance-subtracted expected cumulative loss equals summed integrated mean errors
- normalization_and_boundaries: T VarY0, rangeT; T0 bothzero
- information_structure: Actual strictpast independence produced, then independent square consumed
- source_delta: Finite identity only; no rate/convergence or min-expectation swap

Actual body: Derives target and predictor L2, integrability of squared differences and finite integral-sum interchange, invokes actual mean independence and square decomposition, then identical-law mean/variance rewrites. No desired excess identity is assumed. Verdict: accepted-with-explicit-delta.

## A008 BanditRL.OnlineLearning.iid_meanPredict_excess_nonneg

- objects: Same actual IID mean process
- quantifiers: All natural T
- assumptions: Same stronger pointwise IID premises
- terminal: Expected cumulative loss minus T VarY0 >=0
- normalization_and_boundaries: T0 zero; no normalization
- information_structure: For actual learner only, not arbitrary P
- source_delta: Expected nonnegative, not samplewise nonnegative or success

Actual body: Rewrites the proved finite excess identity, then sums nonnegative square integrals. This is expected nonnegativity, not pathwise regret or convergence. Verdict: accepted-with-explicit-delta.

## A009 BanditRL.OnlineLearning.source_mean_optimal

- objects: One bounded measurable real target and probability mean
- quantifiers: Every real comparator u in last conjunct
- assumptions: Pointwise unit support and measurability
- terminal: Mean feasible, attains variance, all-real fixed losses >=variance
- normalization_and_boundaries: No horizon or uniqueness
- information_structure: Known-law proof witness not unknown-law learner input
- source_delta: Derived attainment/optimality under stronger support; no E(min)

Actual body: Pointwise unit support yields L2/L1 and mean feasibility by integral order; all-real square decomposition gives attainment and universal lower bound. No min/expectation interchange. Verdict: accepted-with-explicit-delta.

## A010 BanditRL.OnlineLearning.history_policy_independent

- objects: Measurable finite real-history deterministic policy
- quantifiers: Every t and measurable scalar policy on range t
- assumptions: Joint target independence/measurability; no law/bounds
- terminal: Composed history policy independent of current target
- normalization_and_boundaries: t0 emptytuple
- information_structure: Actual disjoint range t/{t} independence then measurable composition
- source_delta: Scalar output only, no tuple-output or universal randomized representation

Actual body: Disjoint range t and singleton t under iIndepFun produce tuple independence; measurable scalar policy and current projection compose it. No same-law or support premise. Verdict: accepted-with-explicit-delta.

## A011 BanditRL.OnlineLearning.history_policy_loss_ge_variance

- objects: Same deterministic history policy and pointwise unit targets
- quantifiers: Every real tuple z has policyz in[0,1]
- assumptions: Joint independence, measurability, pointwise targets, globally bounded policy; no same-law
- terminal: Current expected loss >=Var(Yt)
- normalization_and_boundaries: Single t, not VarY0 without commonlaw; t0 allowed
- information_structure: Actual history independence and derived L2 feed square decomposition
- source_delta: Global off-cube bound strictly stronger than legal-cube; no fullsource class closure

Actual body: Actual history composition is measurable and globally bounded, hence L2; current target is L2. Actual history independence and square decomposition leave a nonnegative centered integral and current-round variance. Verdict: accepted-with-explicit-delta.

## A012 BanditRL.OnlineLearning.normalized_excess

- objects: Two arbitrary reals total,variance and natural T
- quantifiers: For every total/variance/T with T>0
- assumptions: Only strictly positive horizon
- terminal: total/T-variance=(total-T*variance)/T
- normalization_and_boundaries: Real coercion; no T+1; T0 generally false
- information_structure: Pure scalar arithmetic, no learner
- source_delta: No statistical nonnegativity or ordinary/asymptotic convergence

Actual body: Positive natural T gives a nonzero real denominator; field_simp/ring prove scalar identity. No limit or stochastic guarantee is claimed. Verdict: accepted-with-explicit-delta.

## Actual validation and evidence

All 34 new named canary proofs and four test fixtures were read, together with the seven retained Foundations canaries. Foundations produces changing Bool prefix minimizers and strict -2<0; omission tests isolate optimality and feasibility. The latter is an ambient-loss extension counterexample, not a source-admissible out-of-domain play. T0 and T1 boundaries are separate.

### clip

- objects: Real input, real output max0(min1x)
- quantifiers: All real x
- assumptions: No probability premise
- terminal: Measurable and globally unit-valued; identity only on unit interval
- normalization_and_boundaries: Endpoints included
- information_structure: Deterministic test-only map
- source_delta: Not a production definition or pointwise identity globally

### boundedObservation

- objects: Infinite real-coordinate product probability process
- quantifiers: All times and sample points, with separate AE equality
- assumptions: Existing fair IID law and measurable clipping
- terminal: Joint independence/common law, mean1/2 variance1/4, L2 actually produced
- normalization_and_boundaries: Off-null constant2 gives clipped1 versus original2
- information_structure: Same coordinatewise process; no future policy input
- source_delta: AE replacement test does not weaken legacy pointwise public premise

### boundedLast

- objects: Scalar finite-history policy
- quantifiers: All t and ALL real tuples z
- assumptions: Measurable lastPolicy then clip
- terminal: Global unit support, legal-history identity, genuine current independence/lower bound
- normalization_and_boundaries: At t1 random previous coordinate gives loss1/2
- information_structure: Strict past tuple excludes current target
- source_delta: Test-only clipping produces stronger global API premise; no universal representation

### heterogeneous

- objects: First target zero, later clipped fair coordinates
- quantifiers: All natural times on same iidLaw
- assumptions: Measurable coordinate transformations of independent family
- terminal: Independent/unit-valued and explicitly NOT same-law; current variance lower1/4
- normalization_and_boundaries: Variance at0=0, at1=1/4
- information_structure: Same strict-past boundedLast composition
- source_delta: Confirms current variance, not common variance or an IID premise

The independent-coordinate consumer is instantiated by genuinely random coordinates, with loss1/2; comparator2 has loss5/2. The actual source predictor has two-round excess1/4, produced through its public finite identity and actual variance. boundedLast at round1 has loss1/2. The heterogeneous process proves not IdentDistrib by unequal variances and invokes the genuine current-variance producer. The positive scalar identity is accompanied by a T0 discrepancy (-1/4 versus0); neither is convergence.

Actual focused attempt v1 failed inverse-two normalization, unreduced measurable mapper, nonexistent variance_const and opaque function-variance rewriting. Attempt v2 retained only the final mean/sum normalization mismatch. Attempt v3 repairs only proof terms with actual variance_zero/function equalities/simpa, succeeds exit0 in17.594s, 9102 jobs including replay. All original test statement headers remain unchanged. The kernel/type elaboration succeeds exit0 in41.516s: twelve whole Props, twelve public proof VALUE instantiations and actual meanPredict definition identity. I independently parsed 68 unique named axiom outputs, all within propext/Classical.choice/Quot.sound, no sorryAx. This is distinct from the 70 selected compiler nodes. The graph contains4134 merged type/value edges; summing separate type/value lists counts shared dependencies twice. All19 prespecified direct VALUE pairs are present. Twelve fences and twelve safe-verifications succeed separately; safe verification is not compilation. Linter warnings remain disclosed.

## Future integration permission and reader obligations

The exact body-future-integration-scope-v1.json is acceptable as a bounded future plan: append the single own Tests import preserving baseline bytes; public root unchanged; one own source card, correct only the two named existing notes, append ten missing notes and own boundaries, preserving unrelated cards/notes/IDs/links/status. Own schema2 may cover the five actually changed comment paths and owned readers, not unchanged production paths. Only own task native metadata/frontier/trials and new own evidence are permitted; global SGB and frozen rows/snapshots remain fixed. Any changed receipt-bound live path requires explicit original snapshot resolution and later exact scoped diff; this is not a blanket prefix/status waiver. No future operation is certified as executed.

- R1 (future pending): Attribute Lemma1.2 to printed4/PDF16 and the IID motivation to printed1/PDF13; source rounds1..T map to Lean0..T-1. Eleven derived/generic/regularity APIs are not eleven printed source theorems.
- R2 (future pending): Expose EVERY positive-prefix feasibility and minimization assumption of Lemma1.2, arbitrary ambient-type generalization, supplied existence and T0 extension; hindsight prefix leaders are not causal FTL predictions.
- R3 (future pending): Distinguish the generic probability/L2 independent-prediction consumer from the actual strict-past mean/history independence producers; never claim supplied independence establishes a causal algorithm.
- R4 (future pending): Display exact legacy every-omega target bounds and global every-history policy bounds as stronger API limitations; do not silently replace with AE/legal-cube assumptions or waive full source coverage.
- R5 (future pending): Show one actual initial-half strict-past meanPredict and the same infinite target process, joint independence/same-law where present, fixed population mean as analysis comparator and no future/law/horizon algorithm input.
- R6 (future pending): Keep expected-fixed minimum outside expectation, no expected hindsight minimum swap; the positive normalization scalar identity is not a convergence theorem. Current-round variance need not use same-law in the history lower bound.
- R7 (future pending): Preserve all existing public names, complete signatures/proof bodies and registry IDs/URLs/statement hashes; current folded types, source formulas and proof explanations require actual focused/kernel/VALUE/canary/combined/site/pixel evidence.
- R8 (future pending): Close only the five specifically audited source-module obligations after actual source/FINAL/native gates. Preserve original sixteen Chapter1 source objects/null proof total and full universal-model/completion/AE-factorization, remaining C1/C2/C3–16/appendix obligations; Goal active, no main/live claim.

Historical Foundations acceptance is preserved, not erased or recursively reaccepted. Zero new production mathematical proofs or wrappers; 34 new validation proofs are not source closure growth. Five source-module audit obligations remain pending. Combined root/Tests/full harness, stacked and main-relative contributor gates, shared registry/site/pixels, FINAL/native/delivery remain separate. Original sixteen source objects/null proof total, universal model/completion/AE-factorization, full C1/C2/C3–16 and necessary appendices remain required; whole Goal ACTIVE, no main/live/merge claim.
