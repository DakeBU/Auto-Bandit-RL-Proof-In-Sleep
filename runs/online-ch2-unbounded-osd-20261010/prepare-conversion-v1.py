from common import *
fixed()
def snapshot(label):
    ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
    write(RUN/(label+'.json'),dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
snapshot('native-draft-exact-before-v1')
event('native-draft-event-v1','draft',dict(task=TASK,source='Orabona v10 Theorem5.4 printed52-53/PDF64-65; Chapter2 required forward',source_sha256=PDF_SHA,headers_sha256=sha(CONTRACT/'headers-draft-v1.json'),draft_terminal_count=11,definitions=4,root_goal='Persistent Chapters1-16 ACTIVE',chapter_complete=False,proofs_closed=0))
snapshot('native-conversion-exact-before-v1')
capture('native-conversion-create-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','conversion-window',TASK,'--title','Actual unbounded OSD switching-loss lower bound')
window=ROOT/'conversion-windows'/(TASK+'.md')
write(RUN/'native-conversion-template-RAW-v1.json',dict(path=window.as_posix(),sha256=sha(window),raw_base64=base64.b64encode(window.read_bytes()).decode('ascii'),provenance='Contemporaneous actual CLI-created template, before draft filling'))
text='''# Conversion Window: Actual unbounded OSD failure

Task id: `ONLINE-CH2-UNBOUNDED-OSD-20261010`
Source: frozen Orabona v10 arXiv1912.13213,2026-06-21,SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17; Theorem5.4 printed52-53/PDF64-65, required Chapter2 printed14/PDF26 forward dependency.

## Natural-Language Statement

For every alpha in(0,1) and natural horizon T with T>=2/((1-alpha)phi(alpha)), actual unprojected OSD initialized0 with source eta_t=t^(-alpha) suffers regret at comparator0 at least phi(alpha)T^(2-alpha)/2 on some convex1-Lipschitz loss sequence. The witness is first ceil(T/2) losses -x and then floor(T/2) losses+x; in positive dimension use a unit vector. Retain the printed strict phi range(0,1-ln2) and limit at1 equal1-ln2>=0.3. No supplied desired regret bound, iterate identity, phi positivity, attainment assumption or lower-bound consumer replaces this production chain.

## Lean Mapping

| Source object | Actual shared/new Lean object | Index / role |
| --- | --- | --- |
| R^d, d>=1 | finite-dimensional real inner-product E; Nontrivial E for final existence | Scalar and unit-vector helpers separate |
| V=R^d | OnlineHuber.fullSpace, shared Domain/projection | Existing full-space projection identity reused |
| eta_t=t^-alpha | powerSteps alpha i=((i+1):R)^(-alpha) | Source round1 maps Lean0 |
| current subgradient | actual OnlineSubgradientDescent.currentSubgradient | Affine full singleton forces actual chosen vector |
| x_t | actual shared iterate at i=t-1 | Initial0/current action before loss |
| loss_t | switchLoss T v i, coerced to EReal in actual OSD | Losses real finite everywhere; source convex/Lipschitz facts proved |
| ceil(T/2),floor(T/2) | (T+1)/2,T/2 natural division | Exact odd/even count and split retained |
| Regret_T(0) | shared OnlineSubgradientDescent.regret fullSpace powerSteps coercedloss 0 0 T | Same actual recursion; no alternate algorithm |
| phi(alpha) | exact new phi formula | Denominators1-alpha/2-alpha; strict open alpha interval |

## Assumption Ledger

Full endpoint: finite-dimensional real E, Nontrivial E, 0<alpha<1, natural T satisfying exact real threshold. Convexity and LipschitzWith1 of witness losses produced, not assumed. CompleteSpace follows from finite dimension. Nontrivial removes the impossible zero-dimensional positive lower bound; pinned proof assumes d1 and embeds for d>=2. All losses finite globally; coercion/toReal needs no defaults. Step/iterate affine helpers need no eta positivity or alpha restriction. Power positivity holds for any real alpha because every played base i+1>0. Identity permits T0, though the source failure endpoint never does. No bounded domain, comparator distance oracle, random process, future-aware algorithm, computable/measurable selector or uniform guarantee over all algorithms is asserted.

## Local API and Proof Route

Actual declaration retrieval v1 failed on three namespace names; v2 actual0 verifies corrected global strictConcaveOn_log_Ioi/integral_rpow and Real.hasStrictDerivAt_const_rpow. Shared affine_subdifferential/fullSpace/project_fullSpace/currentSubgradient/step/iterate/regret are retrieved with actual complete scopes. No external library/toolchain upgrade. One lower route from singleton selection to actual step/unroll, signed finite sum identity, sum-integral bounds and exact threshold; then unit-vector lift and source existential witness. Phi range/limit required as parallel analytic dependencies, not assumptions.

## Proof DAG and Conversion

See dependency-DAG-draft-v1.json and eleven exact headers/scopes in headers-draft-v1.json, plus four complete prospective definitions. Type probe v1 failed only because the zero-binder phi_limit generated `fun =>`; version2 fixes the type-probe syntax and leaves every mathematical header/definition unchanged. It elaborates eleven Prop types, not eleven theorem proofs. Distinct neutral decoder and anti-anchored source review precede stabilization/lowering. Own task/session/trials/journal only; global SGB/frontier/registry remain unchanged.

## Gaps and Acceptance Boundary

All eleven draft terminals open; no theorem body lowered. Required source lower bound, phi range/limit, same-policy public canaries, proof VALUE dependencies, axiom/frozen/body review, root/Tests/full harness and source-qualified shared registry/reader/site/pixel/native/delivery gates remain required. A first helper does not close the lower bound. All8Chapter2forward containers remain required/open pending dedicated reconciliation. Chapter2partial/null, Chapters3-16unenumerated/null, persistent Goal ACTIVE. No Chapter5whole, main/merged/live/deployment/retirement claim.
'''
window.write_bytes(text.encode('utf8'))
write(RUN/'conversion-window-filled-v1.json',dict(path=window.as_posix(),after_sha256=sha(window),before_receipt='native-conversion-template-RAW-v1.json',status='draft filled before stabilization'))
write(ROOT/'proof-obligations'/(TASK+'.md'),'# '+TASK+'\n\nAll eleven exact targets in headers-draft-v1.json are draft/open. Four proposed definitions; no proof bodies. Full actual OSD failure terminal plusphi strict range/limit required. First finite leaf currentSubgradient_affine after independent contract review and freeze; lower-bound consumer is insufficient. Chapter2 source container remainsrequired/open, chaptertotalnull, wholeGoalACTIVE.\n')
write(ROOT/'research-wiki/retrieval-index'/(TASK+'.md'),'# '+TASK+'\n\nActual API retrievalv1 failed3namespace names; v2 correctedandactual0, raw outputs preserved. Shared affine singleton/fullSpace projection/current selector/actualrecursiveOSD/regret reused; sum-integral comparisons, globalintegral_rpow, logtwo numericalbound retrieved. No externaldependency or newproject. Initialsource/contract draft; no proof acceptance.\n')
write(RUN/'canary-design-draft-v1.md','''# Required prospective public canaries

Scalar short run: alpha1/2,T2, firstnegative thenpositive, actualcanonical states0->1->1-2^(-1/2), differentpositive steps1 and2^(-1/2), actualregretat0=1. This checks actual selector/step/unroll and sourceindex; T2 does not meet sourcefailurethreshold, so it must not masquerade as a source theorem instance.

Full finite source endpoint: alpha1/2,T64, prove exactthreshold fromphi(1/2)>=1/15 and prove varyingpositive schedule. In an actual EuclideanSpace R(Fin2) unitfirstcoordinate, allwitnesslosses convex1-Lipschitz, actualearlystate equals thatunitvector. Invoke new switching_vector_lower_bound or theorem_5_4 on SAMEcanonicaltrajectory; retain >=(1/2)*(1/15)*64^(3/2)>=17 numeric branch through selected new endpoint VALUE, no unused call or independent norm_num inequality. Four complete definitions/elevenproductionproofs are not canary/node/source/chapter counts. Exact canary headers need separate type/review/freeze before Test lowering.
''')
write(RUN/'memory-digest-draft-v1.md','Persistent wholebookGoalACTIVE; PR213 delivered exact2f039d5unmerged. CurrentboundedTheorem5.4 dependency draft11/4; sourcepages64/65 visuallyread; actualAPIv2/targettypev2 only. No sourcecontractacceptance/proofclosed. Firstreadyselectoronlyafterdistinctreview/freeze. Preserveoldregistry/roots/readers/nativebaseline.\n')
fixed()
print('Actual scoped draft event and conversion window created/filled; source review and freeze pending.')
