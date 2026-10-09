from common_proving_v2 import *
import copy,gzip
fixed()
assert load(RUN/'combined-gates-inspected-v1.json')['actual_shared_root_Tests_fullharness_passed']
r=load(RUN/'publication-scope-receipt-v4.json')
assert sha(RUN/'publication-scope-receipt-v4.json')=='55daad9c2492f90d36dca59365fab26d49c21d86de5b549dead91f5a0cd72095'
assert r['approved_future_exact_scope_v4']==load(CONTRACT/'future-mutation-scope-draft-v4.json')
proposal=load(RUN/'reader-proposal-v1.json')
paths=[ROOT/p for p in r['approved_future_exact_scope_v4']['future_reader_files']]
assert len(paths)==4
bind=[]
for i,p in enumerate(paths):
    snap=RUN/'snapshots'/('before-readers-v1-%02d.raw'%i);write(snap,p.read_bytes())
    old=load(p);new=copy.deepcopy(old)
    if p.name=='chapters.json':
        row=next(x for x in new['chapters'] if x['slug']=='online-foundations')
        assert 'historical_completion_audits' not in row
        row['historical_completion_audits']=[dict(scope='Exact pre-current-audit Chapter1 completion definition/summary/blockers/gaps; historical package/head boundaries, not current unresolved conclusions.',summary=row['summary'],completion_definition=row['completion_definition'],completion_blockers=copy.deepcopy(row['completion_blockers']),open_gaps=copy.deepcopy(row['open_gaps']))]
        row['summary']=proposal['current_summary'];row['completion_definition']=proposal['completion_definition']
        row['completion_blockers']=proposal['current_blockers'];row['open_gaps']=proposal['current_gaps']
        row['module_globs'].append('BanditRLProof/OnlineFTLInitializationRegret.lean')
        assert [x for x in new['chapters'] if x['slug']!='online-foundations']==[x for x in old['chapters'] if x['slug']!='online-foundations']
    elif p.name=='readings.json':
        row=next(x for x in new['readings'] if x['slug']=='online-foundations')
        row['source_theorems'].append(proposal['card'])
        row['teaching_route'] += [n['full_name'] for n in proposal['notes']]
        older=next(x for x in old['readings'] if x['slug']=='online-foundations')
        assert row['source_theorems'][:-1]==older['source_theorems'] and row['teaching_route'][:-4]==older['teaching_route']
        assert {k:v for k,v in row.items() if k not in ['source_theorems','teaching_route']}=={k:v for k,v in older.items() if k not in ['source_theorems','teaching_route']}
        assert [x for x in new['readings'] if x['slug']!='online-foundations']==[x for x in old['readings'] if x['slug']!='online-foundations']
    elif p.name=='highlights.json':
        assert not {n['full_name'] for n in proposal['notes']} & {n['full_name'] for n in old['highlights']}
        new['highlights'] += proposal['notes']
        assert new['highlights'][:-4]==old['highlights']
    elif p.name=='coverage.json':
        older=next(x for x in old['chapters'] if x['chapter']==1)
        idx=next(i for i,x in enumerate(new['chapters']) if x['chapter']==1)
        new['chapters'][idx]=dict(chapter=1,status='candidate-current-source-audit',accepted=False,mandatory_count=None,source_audit_object_count=17,unknown_required_proof_leaf_count=None,current_generic_proof_contract_count=54,complementary_canary_count=27,evidence=RUN.relative_to(ROOT).as_posix(),boundary=proposal['boundary'],historical_previous_rows=[older])
        assert [x for x in new['chapters'] if x['chapter']!=1]==[x for x in old['chapters'] if x['chapter']!=1]
        assert {k:v for k,v in new.items() if k!='chapters'}=={k:v for k,v in old.items() if k!='chapters'}
    else:raise AssertionError(p)
    result=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    p.write_bytes(result)
    bind.append(dict(path=p.resolve().as_posix(),before=snap.as_posix(),before_sha256=sha(snap),result_sha256=sha(p),planned_result_snapshot=None))
    result_snap=RUN/'snapshots'/('reader-result-candidate-v1-%02d.raw'%i);write(result_snap,result)
    bind[-1]['planned_result_snapshot']=result_snap.as_posix()
write(RUN/'reader-integration-bindings-v1.json',dict(rows=bind,proposal_sha256=sha(RUN/'reader-proposal-v1.json'),scope_receipt_sha256=sha(RUN/'publication-scope-receipt-v4.json'),existing_parsed_records_preserved=True,current_source_cards_added=1,current_shared_notes_added=4,other15_chapter_rows_and_counts_preserved=True,source_audit_objects=17,proof_total=None,chapter_complete=False,goal_complete=False))
old_registry=ROOT/'tmp/online-ftl-obstruction-site-v1/books/registry.json'
old=load(old_registry);assert len(old['nodes'])==10977 and old['lean_verified']
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(old_registry.read_bytes(),mtime=0))
write(RUN/'registry-baseline-bindings-v1.json',dict(actual_prior_registry=old_registry.as_posix(),actual_sha256=sha(old_registry),copied_gzip_sha256=sha(RUN/'registry-baseline-v1.json.gz'),complete_old_nodes=len(old['nodes']),source_commit=old['source_commit'],scope='Old complete canonical registry node records, not prior site as current gate. Four new public proofs expected; Test probes not production nodes.'))
print('Current candidate reader overlay integrated; exact old snapshots/parsed records and10977 complete registry nodes retained.',flush=True)
