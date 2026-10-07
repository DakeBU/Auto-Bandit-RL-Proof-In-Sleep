from common_accepted_v1 import *
accepted_fixed()
requirements = load(RUN/'stabilized-contract-v1.json')['original_reader_requirements']
final = load(RUN/'final-reader-receipt-v1.json')
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:
    assert not final.get(key, []), key
assert set(final['reader_requirement_verdicts']) == {'R'+str(n) for n in range(1,9)}
for row in requirements:
    v = final['reader_requirement_verdicts'][row['id']]
    assert v['verdict']=='satisfied' and v['requirement']==row['requirement']
audits = validate_reviews()
for label in ['combined-root-v2','combined-Tests-v2','full-harness-v2','candidate-frontier-shadow-v1','contributor-committed-exact-base-v3','contributor-pre-FINAL-v1','site-build-v2','site-check-v2','registry-check-v2','current-reader-capture-v2','scoped-diff-pre-FINAL-v5']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0, label
i = load(RUN/'integrated-gates-v3.json')
r = load(RUN/'registry-v1.json')
p = load(RUN/'pixel-review-v1.json')
assert i['committed_production_paths']==6 and i['committed_manifests']==1
assert r['status']==p['status']=='passed' and r['new_registry_nodes']==12
assert r['new_public_proofs']==9 and r['new_public_definitions']==3
assert r['preserved_base_node_IDs_URLs_and_hashes']==10894 and not r['source_dirty'] and r['lean_verified']
assert p['all_12_individually_viewed'] and len(p['images'])==12
scope = 'C1-NOREGRET source reconciliation only: ordinary finite-real-limit semantics kept separate from eventual upper-epsilon control. Nine derived bridge/separation proofs and three definitions; iff requires actual per-comparator finite real convergence and permits negative comparator-dependent limits. ONE fixed signed affine stream on [0,1], constant-zero causal learner, positive even/odd -1/0 yields actual same-process strict separation. Not nine printed theorems, squared/bounded losses, or meanPredict nonconvergence. Three reused proofs including actual strict-past mean upper producer; fifteen named canary proofs and one fixture.'
remaining = 'C1 full regret/best-minimum and five OTHER main-relative source-module audits remain required/unwaived. Original16 C1 source items, mandatory proof total null; Chapter1 open, Chapter2 incomplete, Chapters3-16 unenumerated and necessary appendices required. Total Goal ACTIVE. Exact OPENdraft/unmerged PR191 stack; no main/live/merge/deploy/retirement. Generic supplied-trace bridges are not generic algorithm/minimizer producers; no probability/rate/uniform-comparator claim.'
boundary = dict(source_package_accepted=True, chapter_complete=False, goal_complete=False, merged=False, live=False,
                new_public_proofs=9, new_public_definitions=3, reused_public_proofs=3,
                new_source_subobligation_closures=1, new_public_registry_nodes=12, new_named_validation_proofs=15)
write(RUN/'accepted-binding-audit-v1.json', dict(status='passed', reviews=audits,
    exact_old_Asymptotic_prefix_and_reviewed_comment='Asymptotic-source-append-applied-v3.json',
    approved_old_root_reader_resolutions='source-scope-pre-FINAL-v1.json',
    mutable_FINAL_metadata_snapshots='FINAL-metadata-snapshots-v1.json', all_prior_raw_bytes_preserved=True))
write(RUN/'accepted-reader-discharge-v1.json', dict(status='passed', original_requirements=requirements,
    actual_FINAL_verdicts=final['reader_requirement_verdicts']))
write(RUN/'accepted-decision-v1.json', dict(status=final['verdict'], scope=scope, remaining_required=remaining,
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY), contract_version=1,
    body_bindings=load(RUN/'body-bindings-v1.json'), applicable_integrated=i,
    registry_record_sha256=sha(RUN/'registry-v1.json'), applicable_site_commit=r['source_commit'],
    pixel_record_sha256=sha(RUN/'pixel-review-v1.json'), final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),
    exact_base_PR=191, exact_base_head=BASE, PR_delivery_pending=True, **boundary))
write(RUN/'source-inventory-acceptance-overlay-v1.json', dict(old_inventory='docs/contracts/online-book-v1/source-inventory.json',
    old_inventory_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'), old_inventory_unchanged=True,
    source_subobligation='C1-NOREGRET', printed_page=2, pdf_page=14,
    source_scope='Ordinary lim display versus upper at-most-sublinear prose, explicitly reconciled with conditional equivalence and strict obstruction.',
    terminal=PRE+'NoRegretCounterexample.strict_separation', full_C1_Regret_best_minimum_open=True,
    chapter1_source_items=16, chapter1_required_proof_total=None, remaining_required=remaining, **boundary))
digest = TASK+' '+scope+' '+remaining+' Distinct required reused automated roles/history disclosed/requestedAstra-medium; no human/external/runtime attestation. Actual34kernel declarations,12neutral/15canary Prop identities,7definition identities,24native guards,19VALUEpairs; root9095/Tests9249/harness472skip7. Actual10894old registry IDsURLshashes preserved plus12new;12current images individually viewed. Separately accepted677-byte Asymptotic comment append preserves complete1407-byte code prefix; postappend combined gates apply. All failed proof/API/audit/native/contributor attempts retained, including vacuous N/A superseded and exact raw-log diff exceptions. Only fixed nine-terminal contract progresses9to0; no chapter/program completion.'
write(RUN/'memory-digest-accepted-v1.md', digest)
write(RUN/'retrieval-index-accepted-v1.md', digest)
statement = load(RUN/'full-header-fences-v1/public-strict_separation.json')
terminal = PRE+'NoRegretCounterexample.strict_separation'
native('accepted-reviewer-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','NO-REGRET-V1','--statement-hash',statement['statement_hash'],'--new-declaration',terminal,'--verifier-evidence',RUN/'final-reader-receipt-v1.json','--harness','hierarchical','--progress-class','terminal','--reviewer-validated','--obligations-before','9','--obligations-after','0','--notes',digest)
own = [json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip() and json.loads(s).get('task')==TASK]
assert sum(x.get('status')=='accepted' and x.get('role')=='reviewer' for x in own)==1
write(RUN/'accepted-scoped-trials-v1.jsonl', '\n'.join(json.dumps(x,ensure_ascii=False) for x in own))
native('accepted-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(run_id=RUN.name, contract_version=1, accepted_decision=(RUN/'accepted-decision-v1.json').as_posix(), scope_only='C1-NOREGRET', **boundary)))
native('accepted-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only C1 no-regret reconciliation accepted','--leaf',TASK,'--kind','lean','--statement',statement['statement'],'--declaration',terminal,'--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','lean:'+PRE+'NoRegretCounterexample.no_limit:compiled','--dependency','review:source-reader:accepted','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
native('accepted-frontier-shadow-v1','frontier-shadow','--trials',RUN/'accepted-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow = json.loads((RUN/'accepted-frontier-shadow-v1.log').read_text(encoding='utf8'))
assert not shadow['mismatches'] and not shadow['would_mutate']
native('accepted-memory-record-v1','memory-record','--type','verified_lemma','--task',TASK,'--provenance-kind','source-reviewed-compiled-semantic-reconciliation','--provenance',RUN/'accepted-decision-v1.json','--declaration',terminal,'--file',PUBLIC,'--status','accepted','--verifier',RUN/'final-reader-receipt-v1.json','--role','reviewer','--details-json',json.dumps(dict(scope=scope, remaining_required=remaining, **boundary)),'--output',RUN/'accepted-memory-record-v1.json')
native('accepted-retrieval-record-v1','retrieval-record','--task',TASK,'--query','Ordinary finite real limit versus eventual upper no-regret: conditional equivalence and fixed affine-stream strict separation','--candidate',PRE+'limitNoRegret_iff_noRegret_of_converges','--candidate',terminal,'--compiled-scratch',CANARY,'--provenance',RUN/'public-canary-build-v2-exit.json','--output',RUN/'accepted-retrieval-record-v1.json')
manifest = load(MANIFEST)
manifest['semantic_roundtrip']['remaining_semantic_delta'] = load(CONTRACT/'source-card-v1.json')['delta']+' Actual distinct CONTRACT/BODY/FINAL accepted-with-explicit-delta; exact R1-R8 satisfied. Decoder reconstructs only; no human/external/runtime attestation.'
manifest['verification']['independent_review'] = 'Actual distinct source CONTRACT/BODY/FINAL accepted with explicit delta. FINAL receipt '+sha(RUN/'final-reader-receipt-v1.json')+'; exact R1-R8 satisfied. Package only; chapter and total Goal remain open.'
manifest['verification']['bandit_check'] = 'Actual combined-root-v2 9095 jobs, combined-Tests-v2 9249 jobs, full-harness-v2 472 tests/7 skips; after separately reviewed source-comment append.'
manifest['verification']['site_build'] = 'Actual clean41a225 source with lean_verified=true and applicable combined gates; local site-build-v2/site-check-v2 only, not deployed.'
manifest['verification']['site_check'] = 'Actual10894old IDs/URLs/statementhashes preserved,12new public registry nodes,12current images root individually viewed and separately FINAL reviewed.'
manifest['graph_contribution']['visual_review'] = 'Actual34compiled scoped nodes/27proofs/7definitions and19VALUEpairs;12new shared registry nodes; current reader DOM/pixels and separate FINAL accepted.'
MANIFEST.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',one_accepted_reviewer_trial=True,progress_class='terminal',obligations_before=9,obligations_after=0,obligation_count_scope='Only fixed nine derived reconciliation terminals, never whole chapter/program',globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    path=Path(folder)/(TASK+'.md')
    path.write_bytes(path.read_bytes()+('\n\n## Actual no-regret reconciliation accepted; delivery pending\n\n'+digest+'\n').encode('utf8'))
write(RUN/'40_reviewer_decision-v1.md','Actual distinct staged source/FINAL reviewer accepted-with-explicit-delta, separately bound by raw receipt; formalizer validates exact bindings/R1-R8 discharge and records native acceptance. '+digest)
accepted_fixed()
print('Only C1-NOREGRET source package/native acceptance recorded. PR delivery pending; total Goal ACTIVE.')
