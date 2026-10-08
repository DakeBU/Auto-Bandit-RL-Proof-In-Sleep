# Private-seed IID actual BODY review v2

Verdict: **accepted-with-explicit-delta**, bounded actual candidate bodies only. No blocking mathematical or metadata repair found. Actor `/root/source_reviewer` is the reused distinct staged automated reviewer with prior CONTRACT/source history; requested GPT-6 Astra / medium, no runtime, human, external or absolute-blind attestation.

All1582 indexed raw inputs independently match before/after. All1143 original CONTRACT bindings resolve through the explicit immutable CONTRACT-original-input-resolutions-v2 snapshots; no normalization or old receipt rewrite. Pinned v10 PDF hash remains cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17; original PDF13/14 pixels were actually viewed at original detail again. Source predicts before reveal and minimizes expected FIXED loss, not expected hindsight loss. Seven exact public headers remain text-equal to frozen v2; the complete information comap is unchanged.

## Actual producers and seven slots

### R001 BanditRL.OnlineLearning.independent_private_seed_pair
Verdict: accepted-with-explicit-delta. Actual pushforward product-law equality, independent S/X extraction, measurable product associativity injection and prodAssoc_prod establish the regrouped law; no pairwise shortcut.
- objects_spaces: Arbitrary measurable Ω,Seed,Χ,Ζ; maps S,X,Y on one probability space.
- quantifiers_order: All four universes, structures, μ, maps then measurability and two block-independence premises.
- assumptions_regularity: Measurable S,X,Y; S independent of (X,Y), X independent of Y.
- conclusion_metric: Actual pair (S,X) independent of Y.
- constants_normalization: No loss/horizon/constants.
- information_probability: Joint block factorization, not three pairwise conditions.
- boundary_source_delta: No standard-Borel/cardinality/nondegeneracy assumption; structural helper, not a printed source theorem.

### R002 BanditRL.OnlineLearning.private_seed_past_independent
Verdict: accepted-with-explicit-delta. Actual indepFun_finset(range t){t}, identity/singleton projection and measurable whole-vector extraction establish tuple/current and seed/(tuple,current); R001 completes the regrouping. Old scalar helper is not misused.
- objects_spaces: Seed and real target stream; actual seed plus finite tuple.
- quantifiers_order: For every natural t after global independence/measurability premises.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Same-law/support are NOT needed here.
- conclusion_metric: Actual (S,(Y_i)_{i<t}) independent of Y_t.
- constants_normalization: Strict range t, source t+1 corresponds Lean t.
- information_probability: Extract past/current from whole vector, regroup with R001; no current or future coordinate in prediction input.
- boundary_source_delta: t0 allows seed and empty history; arbitrary private tape, not arbitrary side information.

### R003 BanditRL.OnlineLearning.privateSeedPastInformation_monotone
Verdict: accepted-with-explicit-delta. An actual measurable restriction map retains seed and restricts later history; comap_mono/comap_comp prove the correct sigma-field order, without probabilistic assumptions.
- objects_spaces: Arbitrary Ω, measurable Seed, maps S/Y; no ambient measurable Ω required.
- quantifiers_order: All S,Y; all s≤t through Monotone.
- assumptions_regularity: Only Seed measurable structure; no probability/measurability/boundedness assumptions.
- conclusion_metric: Generated comap sigma algebras grow monotonically.
- constants_normalization: Range s inclusion in range t; includes zero/equality.
- information_probability: Retain same seed and project later finite history to earlier history.
- boundary_source_delta: Not completion/augmentation/right-continuity; no claim that supplied F is monotone.

### R004 BanditRL.OnlineLearning.predictable_private_seed_independent
Verdict: accepted-with-explicit-delta. Ambient instance restored explicitly; R002 becomes independence of generated comap and current comap. hP.comap_le.trans hF and indep_of_indep_of_le_left restrict the left information. No completion/factorization assumption.
- objects_spaces: Common probability data, one subordinate sigma field F and supplied real P.
- quantifiers_order: For every t,F≤generated-information,P measurable[F].
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Exact domain measurability in F, not only ambient measurability.
- conclusion_metric: IndepFun P (Y t) μ.
- constants_normalization: Single arbitrary t, no bounds or integrability conclusion.
- information_probability: Independence inherited through sub-sigma-field; not a policy factorization theorem.
- boundary_source_delta: Unbounded P allowed; F excludes arbitrary future-correlated or completed information.

### R005 BanditRL.OnlineLearning.randomized_history_policy_independent
Verdict: accepted-with-explicit-delta. R002 independence is composed with the actual jointly measurable policy and identity on current target; same seed/history trajectory.
- objects_spaces: Common data and measurable policy on Seed times real strict-history tuple.
- quantifiers_order: Every measurable time-indexed policy, then every t.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Joint full-domain measurability; no feasibility yet.
- conclusion_metric: Independence of actual policy t (S,history) and current target.
- constants_normalization: No regret or normalization; empty initial history allowed.
- information_probability: Concrete function composition with exactly seed and strict past, not a supplied independence certificate.
- boundary_source_delta: Initial action may depend on seed; does not represent every stochastic kernel.

### R006 BanditRL.OnlineLearning.predictable_private_seed_expectedFixed_excess
Verdict: accepted-with-explicit-delta. Ambient measurability is derived from generated-comap domination; a.s. boundedness gives MemLp2; R004 derives current independence; actual benchmark identity and cumulative decomposition yield same-prefix deviation equality and integral/sum nonnegativity.
- objects_spaces: Common data, supplied F_t and supplied real prediction trace.
- quantifiers_order: All F_t subordinate, all F_t-measurable a.s. feasible predictions, every T.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. IdentDistrib with Y0; a.s. target/prediction support[0,1].
- conclusion_metric: Literal expectedFixedRegret equals sum of mean-deviation square integrals and is nonnegative.
- constants_normalization: Finite sum0..T-1; no division; mean integral of Y0.
- information_probability: Must derive ambient measurability/L2 from comap domination and support, and current independence via R004; still consumes supplied predictable trace.
- boundary_source_delta: T0 empty extension; F_t need not monotone. No AS/HP/pathwise nonnegativity or asymptotic success claim.

### R007 BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess
Verdict: accepted-with-explicit-delta. ae_all_iff produces simultaneous target support. Policy composition is measurable in exact generated comap; all-seed legal-history feasibility gives actual a.s. bound. The final proof invokes R006 with this concrete process and le_rfl.
- objects_spaces: Common data and actual seed-history policy trajectory.
- quantifiers_order: Every jointly measurable policy; for every t,seed,legal history cube output is feasible; every T.
- assumptions_regularity: Arbitrary-universe measurable probability space and arbitrary measurable seed space; measurable targets jointly independent and seed independent of the WHOLE infinite target vector. No supplied current-prediction independence. Same-law/a.s. target support; legal-history-only bound for ALL seeds, not just almost every seed.
- conclusion_metric: Exact cumulative mean-square excess identity and nonnegativity on the SAME composed policy process.
- constants_normalization: Same-prefix finite sum/mean; no division or rates.
- information_probability: Instantiate R006 with generated information; actual histories a.s. legal; no oracle loss/independence premise or replacement trajectory.
- boundary_source_delta: Off-cube outputs unrestricted; t0 seed output must be feasible. All-randomized-kernel/completed-field representation remains unproved.

The full information definition remains comap of the actual seed and finite strict-past tuple, with no measure/ambient measurable-space premise in its own signature. At t0 private seed information remains. R006 consumes a supplied restricted trace but derives its ambient measurability/L2/current independence; R007 genuinely supplies the concrete policy wiring. There is no assumed loss bound or supplied prediction/current independence at either terminal. All randomization is integrated under the same μ.

## Nonvacuity and audit evidence
Read the whole canary module, all29 named theorem proofs and nine fixture definitions, including both probability instances and the actual anonymous Fin4 measurable instances. The genuine coinLaw times infinite IID product gives whole-process seed independence and variance1/4. seedBit is measurable and feasible for every real seed; first prediction uses the random bit and later predictions use the strict latest past. The policy is legal on the cube but provably not bounded off cube. Actual R006 and R007 are separately invoked. The actual two-round excess is1/2, with two positive1/4 contributions, and T0 is zero. Current Y0 cannot be measurable in the initial private information: the proof derives impossible self-independence with positive variance. These are not vacuous or assumed endpoints.

Four equal atoms give actual XOR pairwise independences while the joint seed/past-current independence fails; a singleton event yields the contradiction. The final whole-pair counterexample calls R001 contrapositively. This directly protects the essential stronger seed-independence premise. No canary claims arbitrary stochastic-kernel representation or prediction of future targets.

Actual selected compiled environment has55 nodes,42 theorem-kind and13 definition-kind,3470 direct type/value occurrences. All26 prespecified pairs independently occur in actual VALUE dependency lists, including the R002 finite-group API and R007-to-R006 call. Standard-only55 kernel audit records,29 canary proposition identities/nine full fixtures/two probability types/two class identities and36 native guards are separate evidence. Guard success is not compilation. Actual focused/canary and kernel/export exits are successful; this review does not rerun Lean or promote pending combined gates.

Preserved failures include R002 finite-subtype inference, R004 ambient-instance shadowing, canary map/composition/sum proof repairs, finite ENNReal quarter arithmetic and accidental duplicate fixture extraction in an audit leaf. Their successful versions preserve the frozen statements. An initial guessed filename during this review was read-only and corrected to the indexed OnlineGuessingRandomizedIID path; no source edits or mathematical repair occurred.

## Exact future reader requirements

R1: Seed is independent of the WHOLE process, and target family jointly IID; pairwise seed-target independence cannot replace this. Current independence must be derived.
Status: future mandatory; not discharged by BODY.

R2: Generated information is comap of seed+STRICT PAST; monotonicity is proved. General pre-reveal subfields are subordinate to this information; no arbitrary future-correlated side information or general kernel representation claim.
Status: future mandatory; not discharged by BODY.

R3: Concrete jointly measurable seed+history policy instantiates general predictable endpoint. At t0 history is empty but seed is allowed; prediction cannot see current/future targets.
Status: future mandatory; not discharged by BODY.

R4: Retain probability, measurable targets, same laws, a.s.unit support; derive ambient measurability and L2. Legal cube-only policy feasibility for every seed, no global off-cube strengthening.
Status: future mandatory; not discharged by BODY.

R5: Literal minimum is minimum of expected FIXED losses outside expectation. Same-prefix expected excess identity and nonnegativity, no hindsight minimum or pathwise nonnegativity.
Status: future mandatory; not discharged by BODY.

R6: Actual nondegenerate independent private seed/IID targets and XOR-style boundary canaries; T0 empty extension, source1..T=Lean0..T−1. Finite result only; source asymptotic successfulness remains REQUIRED.
Status: future mandatory; not discharged by BODY.

R7: Seven derived producer/interface proofs and one definition, not seven printed results or new rates. Shared root/Tests/fullharness/kernel/canary/fences/site/native/semantic review gates separate; original16/null/C1C2open/3–16unenumerated/appendices/oldfiveaudits/GoalACTIVE; OPENdraftPR194 exact b08 stack is not main/live.
Status: future mandatory; not discharged by BODY.

## Limited future integration

condition: Later integration only with exact versioned pre-edit raw snapshots and separate FINAL review; no current reader acceptance.

root_imports: Each shared root and Tests root may append exactly one own import.

own_bookkeeping: Append only own four native status files and new own retrieval card; refresh shared retrieval only preserving every prior row.

reader: At online-foundations append one source-qualified private-seed/information card preserving all old cards/fields; exactly seven own proof notes preserving old notes; append own module glob; change only that chapter completion_blockers/open_gaps to truthful remaining obligations.

contribution_manifest: Versioned schema2 supersession of own draft manifest with precise assumptions, identical source-qualified declarations, actual evidence and pending FINAL gates; retain draft raw snapshot.

forbidden: No frozen header/definition/math change, old source modules/contracts, source16/null inventory or globalSGB change; no generated-site editing.

Required mathematical repairs: none. Required metadata repairs: none. BODY acceptance does not certify current reader, combined root/Tests/fullharness, shadow/contributor/registry/site/pixels/FINAL/native acceptance or PR delivery. The private-tape representation is an explicit sufficient source model; arbitrary stochastic kernels, completion/augmentation, AE-factorization and unrestricted side information are not represented. Their full-source coverage audit and source asymptotic-success equivalence remain REQUIRED. Seven derived producer/interface proofs and one definition are not seven printed results or new rates. Original16/null, five old audits, C1/C2 open,3–16 unenumerated, appendices and GoalACTIVE remain; OPENdraft/unmerged PR194 b08 stack is not main/live. No chapter/Goal completion.
