from common_integrated_v1 import *
r=body_fixed()
proposal=load(RUN/'reader-proposal-v2.json')
for p in READERS+[Path('Tests.lean')]: assert p.read_bytes()==baseline(p)
Path('Tests.lean').write_bytes(baseline('Tests.lean')+b'\nimport Tests.OnlineLearningCoreAuditCanary\n')
p=Path('website/content/readings.json');d=load(p)
row=next(x for x in d['readings'] if x['slug']==ROUTE)
assert len(row['source_theorems'])==14
row['source_theorems'].append(proposal['card'])
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=Path('website/content/highlights.json');d=load(p)
replacements={n['full_name']:n for n in proposal['replacements']}
names={n['full_name'] for n in d['highlights']}
assert all(n['full_name'] not in names for n in proposal['notes'])
d['highlights']=[replacements.get(n['full_name'],n) for n in d['highlights']]+proposal['notes']
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=Path('website/content/chapters.json');d=load(p)
row=next(x for x in d['chapters'] if x['slug']==ROUTE)
for k in ['completion_blockers','open_gaps']: row[k].append(proposal['boundary'])
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
names=[r['name'] for r in load(CONTRACT/'targets-v2.json')['targets']]
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,
    source_facing=True,source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
    version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor='Lemma1.2 printed4/PDF16; eleven derived/generic/regularity/normalization APIs from IID motivation printed1/PDF13 and actual learner printed3-4/PDF15-16',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Source-correction: five existing core module audits and twelve reused exact public proofs; comments only, no header/body edits or new production proof. '+proposal['boundary'],
    affected_files=[p.as_posix() for p in MODULES+READERS],declarations=names,
    reuse_plan=dict(classification='reuse',decision='reuse_existing',
    searched_existing=['Actual native mathlib/paper/weapon/memory/public exact declaration queries; pinned API searches; actual publicVALUE/wholeProp identities and compiled TYPE_VALUE graph'],
    reused_declarations=names,new_shared_declarations=[],known_consumers=[PRE+'theorem_1_3',PRE+'meanPredict_expectedFixed_excess',PRE+'randomized_history_policy_expectedFixed_excess'],planned_consumers=[],
    no_duplicate_wrapper=True,decision_reason='Revalidate and publish the old proofs with exact legacy assumption deltas; reuse later AE/history producers separately, not duplicate per-book wrappers.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],
    remaining_semantic_delta='Bounded CONTRACT/BODY accepted with explicit generalization and stronger pointwise/global bounds. Exact R1-R8/FINAL readers/site/native audit remains pending. '+proposal['boundary']),
    graph_contribution=dict(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',
    functor_reason='Revalidation/source correction of existing prefix/variance/history facts; no new cross-setting transport claim.',focus_targets=names,
    visual_review='Actual68 unique axiom outputs/70 compiler nodes/4134 TYPE_VALUE occurrences/19 required VALUE pairs; unchanged shared registry and current reader/site/pixel review pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: one own source card, ten absent API notes and two explicitly corrected old notes; unrelated cards/notes preserved',
    banditrlwiki='no-change-with-reason: no Bandit setting/case or result changed',results_ledger='updated: own five source audit candidates, zero new production proofs, source16/null and full C1 open',
    roadmap='no-change-with-reason: sequential whole16 Goal active and globalSGB frontier untouched',website_surfaces=[p.as_posix() for p in READERS]),
    truth_boundary=proposal['boundary'],verification=dict(focused_checks=['Actual focused9102jobs, twelve wholeProp/public proofVALUE and mean Def identity; original7 and new34 canary proofs/4 test definitions; standard axioms and19 actual VALUE pairs; frozen twelve headers/original bodies'],
    bandit_check='Combinedroot/Tests/fullharness/stacked+originmain contributor/ownshadow pending; prior PR196 remote build SUCCESS and main-relative five-module contributor FAILURE retained',
    site_build='Applicable isolated local site after combined gate pending; no deployment',site_check='Old10935 registry IDs/URLs/hash preservation and current12notes/header pixels pending',
    independent_review='Distinct staged CONTRACT93/BODY185 accepted-with-explicit-delta; exactR1-R8 future FINAL pending; automated reused actors, no absolute-blind/human/external/runtime attestation',
    owned_test_files=[CANARY.as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer/source correction; distinct staged automated decoder/source reviewer'))
write(MANIFEST,manifest)
write(RUN/'reader-integration-bindings-v1.json',dict(reader_proposal_sha256=sha(RUN/'reader-proposal-v2.json'),
    BODY_receipt_sha256=BODY_SHA,source_review_receipt_sha256=RECEIPT_SHA,
    public_files_sha256={p.as_posix():sha(p) for p in MODULES},canary_sha256=sha(CANARY),
    old_source_cards_preserved=14,new_source_cards=1,ten_added_notes=10,two_permitted_old_note_corrections=2,
    old_shared_registry_nodes=10935,new_public_nodes=0,new_production_proofs=0,
    actual_R1_R8=r['reader_requirements'],combined_and_FINAL_pending=True,chapter_complete=False,goal_complete=False))
from tools.check_contributor_contract import validate_contract
data,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-validation-v1.json',dict(errors=errors,semantic_status='CONTRACT/BODY only',FINAL_pending=True,chapter_complete=False,goal_complete=False))
assert not errors,errors
fixed_integrated()
print('Exact authorized Test import/readers/schema2 integrated; shared registry nodes unchanged; combined/FINAL pending.')
