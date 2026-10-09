from common import *
fixed()
br=RUN/'five-BODY-review-v1.json'; pr=RUN/'publication-plan-review-v1.json'
for rp in [br,pr]:
    r=load(rp)
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256']
assert load(br)['BODY_verdict'] in ['accepted','accepted-with-explicit-delta']
assert load(br)['canary_BODY_verdict'] in ['accepted','accepted-with-explicit-delta']
assert load(pr)['materialization_verdict'] in ['accepted','accepted-with-explicit-delta']
for name in ['five-BODY-review-inputs-v1.json','publication-plan-review-inputs-v1.json']:
    for row in load(RUN/name)['rows']:
        assert sha(row['path'])==row['sha256'],row['path']
plan=CONTRACT/'exact-publication-plan-v1.json'; p=load(plan)
assert load(pr)['approved_five_rows']==p['rows'] and load(pr)['approved_plan_sha256']==sha(plan)
write(RUN/'publication-review-binding-v1.json',dict(BODY_review_sha256=sha(br),publication_review_sha256=sha(pr),plan_sha256=sha(plan),selected_graph_sha256=sha(RUN/'selected-value-graph-v2.json'),production_sha256=sha(PUBLIC),Test_sha256=sha(ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean'),exact_five_rows=p['rows'],source_container_closed=False,whole_Goal_status='ACTIVE'))
for row in p['rows']:
    assert sha(row['path'])==row['before_sha256'] and sha(row['after_snapshot'])==row['after_sha256']
for row in p['rows']: Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
from publication_guard_v1 import fixed as published_fixed,CONTRIBUTION,CANARY
published_fixed()
proposal=load(RUN/'reader-proposal-v1.json')
names=[t['declaration'] for t in load(CONTRACT/'stabilized-v1.json')['targets']]
tests=[t['declaration'] for t in load(CONTRACT/'canary-stabilized-v1.json')['targets']]
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-2',frontier_cell='online-ogd',source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor='Chapter2 required prescient forward dependency: Definition6.4 printed63/PDF75; Algorithm15.8/Theorem15.30 printed265-266/PDF277-278. Five conditional derived cumulative proofs; full source remains open.',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Same actual partial recursion yields signed fixed/variable cumulative bounds, then printed forms via certified terminal nonnegativity. '+proposal['boundary'],
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json'],declarations=names,
    reuse_plan=dict(classification='adapt',decision='new_shared',searched_existing=['Pinned actual Mathlib and project declarations in RUN; canonical actual iterate_one_step, weighted_potential_sum, divergence_nonneg, exact Finset telescope/max API. No pins/toolchain/dependency upgrade.'],reused_declarations=['BanditRL.OnlinePrescientBregman.iterate_one_step','BanditRL.OnlineGradientDescent.weighted_potential_sum','BanditRL.OnlineBregman.divergence_nonneg','Finset.sum_range_sub\u0027','Finset.le_sup\u0027'],new_shared_declarations=names,known_consumers=tests+names[1:],planned_consumers=['Required source loss/generator hypothesis transport and full source valid-run wrapper; OPEN.'],no_duplicate_wrapper=True,decision_reason='Derive one-step comparison from actual consecutive Option outputs, sum and telescope, reuse canonical weighted potential with a=2B/C=2M. Exact finite max and actual new-minimum concrete decreasing-step canary. No assumed desired regret bound/independent trajectory.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict='accepted-with-explicit-delta',remaining_semantic_delta='Separate staged neutral production/canary reconstructions, CONTRACT/BODY and exact five-path reader plan reviewed; exact hashes in RUN. Reused automated actor related history disclosed, no human/external/absolute-blind/runtime attestation. '+proposal['boundary']+' FINAL/package acceptance pending.'),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Same-setting signed-potential telescopes reuse a canonical weighted-potential theorem; no new certified cross-setting transport.',focus_targets=names,visual_review='Actual selected7public/7total nodes and1885coalesced direct TYPE_VALUE presences;8production and5canary required VALUE pairs. Four independently selected numeric proof branches have Eq.mpr heads and their specific new production constants. Not full transitive graph or source denominator. Complete registry/site/pixels pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: online-ogd appends one module/goal/completion suffix, one exact source-qualified card and five canonical production notes. Every old field/link/ID and other Book preserved.',banditrlwiki='no-change-with-reason: deterministic prescient conditional cumulative package does not change Bandit policies or settings.',results_ledger='no-change-with-reason: no full source container or Chapter2 accepted; OWN bounded milestone separate.',roadmap='no-change-with-reason: all8Chapter2forward source containers/full source transport remain REQUIREDOPEN, Chapter2partial/null, Ch3-16unenumerated/null and wholeGoalACTIVE; globalSGB untouched.',website_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json']),
    truth_boundary=proposal['boundary'],
    verification=dict(focused_checks=['Actual5production focused builds0, complete public values5/standard-only axiom lists5 and8required VALUE pairs. Both16/22conjunct canaries actualfocused0; complete public values2/standard-only axiom lists2,5required canary VALUE pairs,4individually selected Eq.mpr numeric proofs retain required new constants. Seven frozen headers/native fences preserved; all failures and equivalent proof-body repairs retained. Counts are bounded package evidence only.'],bandit_check='Pending actual combined root/Tests/full harness; focused compiler evidence separate.',site_build='Pending applicable combined Lean gate and clean isolated site output; generated website/_site untouched.',site_check='Pending full shared registry, browser DOM/geometry and personal/distinct original-pixel review; no main/live claim.',independent_review='Distinct staged BODY accepted '+sha(br)+' and exact five-path prospective materialization accepted '+sha(pr)+'. FINAL/native/post-native/delivery pending.',owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer with distinct staged automated decoder and source reviewer'))
write(CONTRIBUTION,manifest)
write(RUN/'publication-integrated-v1.json',dict(BODY_review_sha256=sha(br),publication_review_sha256=sha(pr),exact_five_old_transitions_only=True,all_old_fields_preserved=True,production_sha256=sha(PUBLIC),Test_sha256=sha(CANARY),full_gates_pending=True,whole_Goal_status='ACTIVE'))
published_fixed()
print('Exact reviewed five old paths and OWN contribution materialized; combined gates remain pending.')
