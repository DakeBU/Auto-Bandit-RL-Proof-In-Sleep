# Private-seed IID source CONTRACT v2 review

Verdict: **accepted-with-explicit-delta for contract stabilization only**. No blocking mathematical or metadata repair found. Seven prospective propositions and one complete information definition are reviewed; none of the seven target proof bodies is accepted or claimed to exist.

Actor `/root/source_reviewer`, distinct reused staged automated source reviewer with prior source-review history. Requested GPT-6 Astra / medium; runtime/model/effort not attested. Not absolute-blind, human or external review. The decoder reconstructs neutral propositions and provides no source/proof acceptance.

All1143 indexed raw rows independently rehashed before and after review. Pinned PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 freshly matches. Both original PDF13/14 images were actually viewed at original detail and printed1–2 text reread: predict before reveal, IID variance benchmark, then minimum of EXPECTED FIXED loss outside expectation. The source's finite nonnegativity claim is the intended hinge, not its later asymptotic-success equivalence.

## Source coverage and counterexample search
The independent-private-tape formulation is a faithful explicit sufficient model of source causal randomization, not literal equivalence to every informal algorithm. Whole-process seed independence is essential: two fair bits X,Y and S=X xor Y give pairwise seed independence but allow (S,X) to recover Y. Thus R001 correctly requires independence from the entire pair; R002 correctly requires seed independence from the complete process and joint target independence. No pairwise substitution is accepted.

The exact generated comap is subordinate to the ambient measurable space when the seed and coordinates are measurable. R004/R006 then can derive ambient measurability; real a.s. boundedness supplies L2. No extra completeness or standard-Borel assumption is needed for these typed statements. F_t is a supplied subfield and need not be monotone; the enclosing generated information is the object whose monotonicity R003 must prove. Arbitrary completions/augmentations and AE-factorization are outside this contract.

R006 is a legitimate supplied information-restricted trace interface; it is not itself a construction of all algorithms. R005/R007 supply the concrete jointly measurable policy(seed, strict finite history) composition. Legal-cube feasibility holds for every seed value, stronger than just actual-path a.s. feasibility; target support stays a.s., and no off-cube boundedness is added. At t0 history is empty but private seed remains available, unlike a fixed half-initialized deterministic learner. Expectations integrate seed and targets under the SAME μ. No separate seed expectation, min/expectation swap, samplewise nonnegative regret, high-probability or limit claim follows.

Universal kernel representation, completed/general side-information coverage and source asymptotic-success equivalence remain required separate audits where needed for full source-wide closure. This bounded extension cannot close the phrase all algorithms. The distribution-known mean remains a benchmark oracle, not an unknown-law implementation.

## Per-target seven-slot comparison

### R001 BanditRL.OnlineLearning.independent_private_seed_pair
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Arbitrary measurable Ω,Seed,Χ,Ζ; maps S,X,Y on one probability space.
- quantifiers_order: All four universes, structures, μ, maps then measurability and two block-independence premises.
- assumptions_regularity: Measurable S,X,Y; S independent of (X,Y), X independent of Y.
- conclusion_metric: Actual pair (S,X) independent of Y.
- constants_normalization: No loss/horizon/constants.
- information_probability: Joint block factorization, not three pairwise conditions.
- boundary_source_delta: No standard-Borel/cardinality/nondegeneracy assumption; structural helper, not a printed source theorem.

### R002 BanditRL.OnlineLearning.private_seed_past_independent
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Seed and real target stream; actual seed plus finite tuple.
- quantifiers_order: For every natural t after global independence/measurability premises.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Same-law/support are NOT needed here.
- conclusion_metric: Actual (S,(Y_i)_{i<t}) independent of Y_t.
- constants_normalization: Strict range t, source t+1 corresponds Lean t.
- information_probability: Extract past/current from whole vector, regroup with R001; no current or future coordinate in prediction input.
- boundary_source_delta: t0 allows seed and empty history; arbitrary private tape, not arbitrary side information.

### R003 BanditRL.OnlineLearning.privateSeedPastInformation_monotone
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Arbitrary Ω, measurable Seed, maps S/Y; no ambient measurable Ω required.
- quantifiers_order: All S,Y; all s≤t through Monotone.
- assumptions_regularity: Only Seed measurable structure; no probability/measurability/boundedness assumptions.
- conclusion_metric: Generated comap sigma algebras grow monotonically.
- constants_normalization: Range s inclusion in range t; includes zero/equality.
- information_probability: Retain same seed and project later finite history to earlier history.
- boundary_source_delta: Not completion/augmentation/right-continuity; no claim that supplied F is monotone.

### R004 BanditRL.OnlineLearning.predictable_private_seed_independent
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Common probability data, one subordinate sigma field F and supplied real P.
- quantifiers_order: For every t,F≤generated-information,P measurable[F].
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Exact domain measurability in F, not only ambient measurability.
- conclusion_metric: IndepFun P (Y t) μ.
- constants_normalization: Single arbitrary t, no bounds or integrability conclusion.
- information_probability: Independence inherited through sub-sigma-field; not a policy factorization theorem.
- boundary_source_delta: Unbounded P allowed; F excludes arbitrary future-correlated or completed information.

### R005 BanditRL.OnlineLearning.randomized_history_policy_independent
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Common data and measurable policy on Seed times real strict-history tuple.
- quantifiers_order: Every measurable time-indexed policy, then every t.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Joint full-domain measurability; no feasibility yet.
- conclusion_metric: Independence of actual policy t (S,history) and current target.
- constants_normalization: No regret or normalization; empty initial history allowed.
- information_probability: Concrete function composition with exactly seed and strict past, not a supplied independence certificate.
- boundary_source_delta: Initial action may depend on seed; does not represent every stochastic kernel.

### R006 BanditRL.OnlineLearning.predictable_private_seed_expectedFixed_excess
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Common data, supplied F_t and supplied real prediction trace.
- quantifiers_order: All F_t subordinate, all F_t-measurable a.s. feasible predictions, every T.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. IdentDistrib with Y0; a.s. target/prediction support[0,1].
- conclusion_metric: Literal expectedFixedRegret equals sum of mean-deviation square integrals and is nonnegative.
- constants_normalization: Finite sum0..T-1; no division; mean integral of Y0.
- information_probability: Must derive ambient measurability/L2 from comap domination and support, and current independence via R004; still consumes supplied predictable trace.
- boundary_source_delta: T0 empty extension; F_t need not monotone. No AS/HP/pathwise nonnegativity or asymptotic success claim.

### R007 BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
Verdict: accepted-with-explicit-delta (statement only).
- objects_spaces: Common data and actual seed-history policy trajectory.
- quantifiers_order: Every jointly measurable policy; for every t,seed,legal history cube output is feasible; every T.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Same-law/a.s. target support; legal-history-only bound for ALL seeds, not just almost every seed.
- conclusion_metric: Exact cumulative mean-square excess identity and nonnegativity on the SAME composed policy process.
- constants_normalization: Same-prefix finite sum/mean; no division or rates.
- information_probability: Instantiate R006 with generated information; actual histories a.s. legal; no oracle loss/independence premise or replacement trajectory.
- boundary_source_delta: Off-cube outputs unrestricted; t0 seed output must be feasible. All-randomized-kernel/completed-field representation remains unproved.

### Full owned information definition
- objects_spaces: Arbitrary Ω and measurable Seed; S,Y,t.
- quantifiers_order: All data, then natural t.
- assumptions_regularity: No measure or ambient measurable Ω or measurable S/Y premise.
- conclusion_metric: Full comap of actual seed/strict-history map into product measurable space.
- constants_normalization: Finite subtype range t, excludes t.
- information_probability: Whole private tape available, current/future targets absent.
- boundary_source_delta: At zero seed information remains; exact generated field, not completion or arbitrary filtration.

## Evidence and proposed producer route
The arbitrary-universe draft/neutral seven closed-Prop equalities exit0 in actual identities-v3. They establish type agreement only; Q definitions and rfl between propositions do not prove those propositions. The neutral report matches these scopes, including no same-law premise for R002 and no probability premise for R003. Actual shared expectedFixedMinimum/expectedFixedRegret definitions preserve min E and signed excess. Existing IsLeast-to-csInf and cumulative decomposition bodies are real reusable parents. The old history loss API has stronger pointwise bounds and cannot silently replace the new a.s. support/legal-cube targets.

The intended DAG is coherent: R001 joint regrouping, R002 extraction of past/current, R004 subfield inheritance, R006 finite integration and benchmark identity, R007 actual policy instantiation; R003 structural monotonicity and R005 concrete independence are separate obligations. Future bodies must actually implement these producers, not assume their endpoints. Planned nondegenerate seed/IID and XOR canaries remain unproved validation obligations.

Explicit R002 API/DAG refinement: the listed old history_policy_independent accepts scalar-output policies and does not directly produce independence of the whole past tuple. Use the already-probed iIndepFun.indepFun_finset on range t and {t}, then measurable identity/singleton coordinate projection to obtain tuple/current independence, before R001. The frozen target remains correct; the draft dependency label is an indirect retrieval lead, not an actual compiled dependency or a valid direct tuple-producing call. Future BODY evidence must bind the actual imported value calls. This route refinement does not claim the body exists.

Operative source-statement-fingerprint-v2 and proof-obligations-current-draft-v2 hashes match all seven exact headers. Preliminary stale fingerprint/obligation copies and parser/API/universe/helper failures remain historical, explicitly superseded. No theorem-body success is inferred from their repaired type checks. Independently compared the old reference declaration multiset at exact base: all8786 rows survive with multiplicity in10822 rows;2036 additions are inventory of existing source declarations, not new mathematical proofs. Indexed old Lean files were byte-audited; this is not independent semantic reacceptance of every old module. A guessed History module filename produced a read-only file-not-found during this review; actual OnlineLearningHistory was then located and read, with no file mutation or mathematical repair.

## Exact future reader obligations

R1: Seed is independent of the WHOLE process, and target family jointly IID; pairwise seed-target independence cannot replace this. Current independence must be derived.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R2: Generated information is comap of seed+STRICT PAST; monotonicity is proved. General pre-reveal subfields are subordinate to this information; no arbitrary future-correlated side information or general kernel representation claim.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R3: Concrete jointly measurable seed+history policy instantiates general predictable endpoint. At t0 history is empty but seed is allowed; prediction cannot see current/future targets.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R4: Retain probability, measurable targets, same laws, a.s.unit support; derive ambient measurability and L2. Legal cube-only policy feasibility for every seed, no global off-cube strengthening.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R5: Literal minimum is minimum of expected FIXED losses outside expectation. Same-prefix expected excess identity and nonnegativity, no hindsight minimum or pathwise nonnegativity.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R6: Actual nondegenerate independent private seed/IID targets and XOR-style boundary canaries; T0 empty extension, source1..T=Lean0..T−1. Finite result only; source asymptotic successfulness remains REQUIRED.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

R7: Seven derived producer/interface proofs and one definition, not seven printed results or new rates. Shared root/Tests/fullharness/kernel/canary/fences/site/native/semantic review gates separate; original16/null/C1C2open/3–16unenumerated/appendices/oldfiveaudits/GoalACTIVE; OPENdraftPR194 exact b08 stack is not main/live.
Status: mandatory future reader/canary evidence, not discharged by CONTRACT.

Required mathematical repairs: none. Required metadata repairs: none. Bodies, canaries, kernel audits, current combined root/Tests/harness, site/reader FINAL, native acceptance and PR delivery remain separate future gates. Seven derived interface/producer results are not seven printed source theorems or new rates. Original16 C1 items/proof total null, five old audits, C1/C2 open, Chapters3–16 unenumerated, necessary appendices and whole Goal ACTIVE remain. Exact OPENdraft/unmerged PR194 b08 stack is not main/live. No chapter/Goal/source-package acceptance, merge/deploy or retirement.
