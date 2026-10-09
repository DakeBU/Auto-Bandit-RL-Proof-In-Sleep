from common_proving_v2 import *
fixed()
target=load(CONTRACT/'chapter-canary-targets-draft-v1.json')
assert len(target['targets'])==27
mapping={
'C1-GAME':['C001','C005','C006','C022'],
'C1-IID-MEAN':['C012','C013'],
'C1-IID-LOWER':['C012','C022','C023'],
'C1-EQ1.1-1.2':['C015','C027'],
'C1-REGRET':['C010','C011','C014','C016'],
'C1-NOREGRET':['C007','C008','C024'],
'Remark1.1':['C016'],
'C1-MEAN-PREFIX':['C017','C018'],
'C1-FTL':['C005','C006','C020','C024'],
'Lemma1.2':['C019'],
'Theorem1.3':['C020'],
'C1-STABILITY':['C021'],
'C1-REFINED-REGRET':['C020'],
'C1-LOG-UNAVOIDABLE':['C025'],
'C1-HARMONIC':['C026'],
'C1-SUCCESS':['C007','C008','C015','C024'],
'C1-FTL-ANY-INITIAL-GUARANTEE':['C001','C002','C003','C004','C007','C008','C009','C010']}
source=load(CONTRACT/'chapter-one-source-map-draft-v3.json')
assert set(mapping)=={r['source_id'] for r in source['original16_source_objects_preserved_verbatim']+source['additional_required_source_objects']}
write(CONTRACT/'chapter-canary-source-intent-draft-v1.json',dict(mapping=mapping,source_17_intact=True,canary_count=27,proof_total=None,purpose='Nondegenerate public instantiation and cross-metric/initialization/information checks; counts are not source coverage denominator or new mathematical results',old50_full_generic_public_endpoints_unchanged=True,new4_body_accepted_not_chapter=True,all_theorem_values_and_actual_dependency_pairs_required_after_canary_bodies=True,chapter_complete=False,goal_complete=False))
write(CONTRACT/'chapter-canary-source-intent-draft-v1.md','''# Proposed whole Chapter1 public canary contract

Twenty-seven meaningful public Test statements instantiate the17 audited source objects, preserving all fifty existing generic public terminals and four exact new initialized-FTL producers. The declaration count is not the source count or a completed-proof denominator. No new canary body exists, and no source/chapter acceptance is inferred from the actual closed-Prop typecheck. Exact CANARY headers require distinct blind reconstruction then SOURCE CONTRACT review before bodies; edits are limited to the sole reviewed Test module plus its later exact root import.

The new initial0/constant1 first true-best regret1 and refined1/3 bounds expose why the universal initial quarter is false. Falling unit data1,0 produces true-best regret3/2 at two rounds; comparator0 regret1 is different. Rising0,1 produces true-best+1/2 with signed first-loss correction-1/4, correcting the source-reviewer's immutable prior false negative example via v4. Outside real initial2/target3 only tests the general algebraic positive-horizon identity, never claims legal-unit performance. T0 gives two zero regrets while the first-loss correction is3/4, validating the positive-horizon boundary.

Recursive count/mean state starts at3/4, updates to0 then1/2, and changes after the current observation is revealed; two streams with the same strict past have equal pre-reveal state. Dyadic genuinely varying bounded data exercise all legal fixed initializers under upper-epsilon NoRegret and a concrete nonhalf3/4 under true-best ordinary zero average. The SAME actual half FTL on that stream satisfies upper and best-average0 while fixed0 regret has no finite ordinary limit and literal LimitNoRegret fails. Printed ordinary-limit definition, conditional convergence iff, this obstruction and the proposed source correction remain distinct, with no author-endorsement or false universal convergence claim.

Nonzero-variance IID coin data keep population minimum outside expectation: fixed two-round minimum1/2 versus expected realized hindsight minimum1/4. Actual strict-past mean regret1/4 and normalized1/8 contrast with the constant analytic population-mean oracle0. IID success includes both exact ordinary average0 and little-o total excess; constant correlated observations give negative expected FIXED regret-1/4 while IID gives+1/4. No independence-free lower guarantee is inferred. A single selected sampler realizes a decision kernel depending on actual past actions/observations, has two different next-round laws1/4 and3/4, and yields the SAME infinite process expected-fixed excessT/4 at every horizon under an exogenous IID law. The sampler is selected before the observation law/horizon; no clairvoyant future/all-protocol representation is asserted. AE unit support rather than pointwise legality of all real-coordinate sample paths remains explicit in the generic parent contracts.

W=[0,2] properly contains comparator V=[0,1]. The same output2/reference1 produces regret-2 for losses-x and-4 for losses-2x, so loss dependence and correct output-domain typing stay visible. Mean0,1 prefix minimum is1/2 and positive-prefix uniqueness gives comparator1/2; empty-prefix loss iszero for every feasible comparator, with no uniqueness. Concrete Boolean leaders produce BTL lhs-2 versusrhs0 using actual prefix minimizers and public Lemma1.2. Half FTL regret3/4, quarter-tail9/4 and4+4log2 remain separate; later same-stream stability gap3/4 andbound2 instantiate public stability. Positive stochastic seed lower chooses a binary two-round witness AFTER the fixed policy and seed measure, and compares seed expectation to log4/6; neither samplewise nor sharp printed minimax constants. Rational harmonic2=3/2 and <=1+log2 instantiate the actual upstream statement. The centered total5+3T has nonzero finite initial offset, little-o centered excess and the total-division T0 normalized boundary-3.

Canaries must call actual public producers where applicable and retain full theorem VALUE/axiom/fence/header checks; closed numerical computations are behavioral boundary checks, not generic proof replacements. Existing advanced AE/completed/kernel/private-randomness canaries and their public declarations remain in the same shared Tests root. Review requires all17 current source/54 generic public target semantics, not merely these27 tests. Focused canary, root/Tests/full harness, two-base contributor/OWN shadow/same declaration registry/source-qualified Book mapping/site/DOM/personal pixels/FINAL/native/post-native/scoped PR remain pending. No generated-site edits, globalSGB record mutation, main merge/deploy/whole-Goal completion. Reused distinct automated reviewers requestedAstra/medium, no human/external/runtime/absolute-blind attestations.
''')
write(RUN/'20_architect-chapter-canaries-draft-v1.md','Single lower route: await independent27header reconstruction/source contract; freeze exactTest terminal hashes, then write actual public Test bodies. Bounds/limits/BTL/minima/IID/kernel/loglower use actual existing/new public producers; numerical initial/index/metric/domain cases compute true nondegenerate behavioral values. Later actualVALUE constraints distinguish direct oldTest reuse from transitive public parents. New4canonicalproofmodule unchanged; exactRoot import done afterBODY, Tests import pending. Keep baseline/rawsnapshot guarded; one chapter only;27 is Testtarget count/17sourceobjects/proof-totalnull, no completion.')
fixed()
print('17 source objects mapped to27 draft meaningful canary types; separate semantic review/proofs pending.',flush=True)
