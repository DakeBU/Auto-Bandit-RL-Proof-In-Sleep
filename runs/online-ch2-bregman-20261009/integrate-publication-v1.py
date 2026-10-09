from common import *
fixed()
binding=load(RUN/'publication-review-binding-v2.json')
rp=RUN/'canary-BODY-publication-review-v2.json';r=load(rp)
assert sha(rp)==binding['review_sha256']
assert r['BODY_verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
for row in load(RUN/'canary-BODY-publication-review-inputs-v2.json')['rows']:
    assert sha(row['path'])==row['sha256'],row['path']
plan=load(CONTRACT/'exact-publication-plan-v2.json')
assert sha(CONTRACT/'exact-publication-plan-v2.json')==binding['plan_sha256']
assert plan['rows']==r['approved_five_rows']
for row in plan['rows']:
    assert sha(row['path'])==row['before_sha256'] and sha(row['after_snapshot'])==row['after_sha256']
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v1 import fixed as published_fixed,CONTRIBUTION,CANARY
published_fixed()
p=load(RUN/'reader-proposal-v2.json');d=load(CONTRACT/'stabilized-v1.json')
names=[d['definition']['declaration']]+[t['declaration'] for t in d['targets']]
tests=[t['declaration'] for t in load(CONTRACT/'canary-stabilized-v1.json')['targets']]
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-2',frontier_cell='online-ogd',source_facing=True,
 source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor='Chapter2 printed14/PDF26 -> Definition6.4/Lemma6.7 printed63–64/PDF75–76 -> Algorithm15.8/Theorem15.30 proof-step dependency printed265–266/PDF277–278. General source container still open.',url='https://arxiv.org/pdf/1912.13213v10'),
 target='Canonical actual-fderiv Bregman algebra and a real nonsmooth proximal one-step comparison preserving both negative residuals. '+p['boundary'],
 affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json'],declarations=names,
 reuse_plan=dict(classification='adapt',decision='new_shared',searched_existing=['Pinned typed mathlib APIv1/v2 and actual public-declaration retrieval in RUN; PR208 exact accepted real minimizer comparison reused. No separate Optlib/toolchain/library introduced.'],reused_declarations=['BanditRL.OnlineProximal.convex_minimizer_comparison','ConvexOn.le_slope_of_hasDerivAt','ConvexOn.comp_affineMap','HasGradientAt.fderiv_apply','HasFDerivAt.comp','HasFDerivAt.sub','HasFDerivAt.const_smul'],new_shared_declarations=names,known_consumers=tests+['BanditRL.OnlineBregman.proximal_one_step'],planned_consumers=['Required attained current-loss causal source producer, finite extended-real loss bridge and same-run fixed/variable telescopes (OPEN, not compiled here)'],no_duplicate_wrapper=True,decision_reason='One canonical actual derivative formula and direct algebra/support/calculus proofs. Two real concrete canary families consume the public one-step and gradient conversion. No fake free-gradient wrapper, assumed regret/stability or future-sequence algorithm consumer.'),
 reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
 semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict='accepted-with-explicit-delta',remaining_semantic_delta='Distinct staged CONTRACT/BODY/two-canary CONTRACT/BODY and exact reader materialization accepted at SHA-bound inputs. '+p['boundary']+' Reused related automated actor history disclosed, no human/external/absolute-blind/runtime attestation. Not FINAL/package acceptance.'),
 graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Canonical continuous-dual/gradient representation and proximal algebra in one setting; no newly certified cross-setting map or functor.',focus_targets=names,visual_review='Selected compiled8nodes/1619coalesced direct TYPE_VALUE presences/8requiredVALUEpairs and two individually selected numeric final branches inspected. Complete registry/site/DOM/pixels pending.',edge_semantics='formal-solid; overlays-dashed'),
 progress_updates=dict(teaching_route='updated: existing online-ogd additive1module/goal/completion suffix,1sourcequalified bounded card and6production notes. All old IDs/formulas/links and otherBooks preserved.',banditrlwiki='no-change-with-reason: deterministic proximal foundation does not change Bandit policies/settings.',results_ledger='no-change-with-reason: helper bundle does not accept general source performance orChapter2; bounded OWN milestone separate.',roadmap='no-change-with-reason: all8Chapter2forwards/generalprescient remainOPEN; whole16GoalACTIVE,Ch3–16unenumerated/null; globalSGBunchanged.',website_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json']),truth_boundary=p['boundary'],
 verification=dict(focused_checks=['Actual production2391/Tests2439cached-inclusive jobs0; seven full public VALUEs/fourteen standard-onlyaxiom outputs/sevenfrozenheaders+canonicaldefinition/nativeguards. Actual compiled8nodes/8VALUEpairs and both selected numeric tails retain actual publicproximal_one_step. Prior proof/API implementation failures retained; no target weakening.'],bandit_check='Pending current combined root/Tests/full tools/bandit.py check; focused builds are separate evidence.',site_build='Pending applicable full Lean gate and clean isolated site build; generated website/_site untouched.',site_check='Pending exact complete shared registry and actual browser DOM/geometry/original pixels; no deployed/live claim.',independent_review='Distinct staged source/CONTRACT/BODY/canary/reader/exact5paths accepted-with-explicit-delta '+sha(rp)+'. FINAL/native/postnative/concrete delivery pending.',owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
 contributor=dict(name='Codex for Ji Cheng',role='Formalizer with distinct staged automated decoder and anti-anchored source reviewer'))
write(CONTRIBUTION,manifest)
write(RUN/'publication-integrated-v1.json',dict(review_sha256=sha(rp),plan_sha256=sha(CONTRACT/'exact-publication-plan-v2.json'),exact_five_old_transitions_only=True,production_sha256=sha(PUBLIC),test_sha256=sha(CANARY),source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
published_fixed()
print('Exact reviewed5oldpaths and OWN contribution materialized; combined gates pending.')
