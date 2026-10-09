from common_reader_v7 import *

fixed()
# Pre-build field audit caught an own status list written under a new key.
p=ROOT/'website/content/chapters.json';data=load(p)
c=next(x for x in data['chapters'] if x['slug']=='online-foundations')
assert 'known_gaps' in c and 'open_gaps' in c
write(RUN/'snapshots/before-post-FINAL-field-repair-v2.raw',p.read_bytes())
c['open_gaps']=c.pop('known_gaps')
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
bindings=load(RUN/'reader-integration-bindings-v4.json')
row=next(r for r in bindings['rows'] if Path(r['path']).name=='chapters.json')
write(RUN/'snapshots/reader-result-post-FINAL-field-repair-v5.raw',p.read_bytes())
row['result_sha256']=sha(p);row['planned_result_snapshot']=(RUN/'snapshots/reader-result-post-FINAL-field-repair-v5.raw').as_posix()
bindings['status_field_repair']='Pre-build field audit caught newly added known_gaps; only existing open_gaps is used. No mathematical or otherBook field changed.'
write(RUN/'reader-integration-bindings-v5.json',bindings)
write(RUN/'common_reader_v8.py',(RUN/'common_reader_v7.py').read_text('utf8').replace('reader-integration-bindings-v4.json','reader-integration-bindings-v5.json'))
before=load(RUN/'post-FINAL-metadata-before-v1.json')
old={r['path']:r for r in before['rows']}
old_reader=load(RUN/'reader-integration-bindings-v3.json')
changes=[]
names={t['name'] for t in load(CONTRACT/'general-initialization-targets-stabilized-v3.json')['new_targets']}
for row in bindings['rows']:
    p=Path(row['path']);o=load(old[p.as_posix()]['snapshot']);n=load(p)
    if p.name=='chapters.json':
        oo=next(x for x in o['chapters'] if x['slug']=='online-foundations');nn=next(x for x in n['chapters'] if x['slug']=='online-foundations')
        assert o.keys()==n.keys() and len(o['chapters'])==len(n['chapters'])
        assert [x for x in o['chapters'] if x['slug']!='online-foundations']==[x for x in n['chapters'] if x['slug']!='online-foundations']
        changed={k for k in oo.keys()|nn.keys() if oo.get(k)!=nn.get(k)}
        assert changed=={'summary','completion_blockers','open_gaps'}
    elif p.name=='readings.json':
        oo=next(x for x in o['readings'] if x['slug']=='online-foundations');nn=next(x for x in n['readings'] if x['slug']=='online-foundations')
        assert [x for x in o['readings'] if x['slug']!='online-foundations']==[x for x in n['readings'] if x['slug']!='online-foundations']
        assert oo['source_theorems'][:-1]==nn['source_theorems'][:-1]
        assert {k:v for k,v in oo.items() if k!='source_theorems'}=={k:v for k,v in nn.items() if k!='source_theorems'}
        a,b=oo['source_theorems'][-1],nn['source_theorems'][-1]
        assert {k:v for k,v in a.items() if k!='local_status'}=={k:v for k,v in b.items() if k!='local_status'}
        assert a['local_status']['status']==b['local_status']['status']=='compiled'
        changed={'source_theorems[-1].local_status.label','source_theorems[-1].local_status.boundary'}
    elif p.name=='highlights.json':
        assert len(o['highlights'])==len(n['highlights'])
        assert [x for x in o['highlights'] if x['full_name'] not in names]==[x for x in n['highlights'] if x['full_name'] not in names]
        for a,b in zip(o['highlights'],n['highlights']):
            if a['full_name'] in names:assert {k:v for k,v in a.items() if k!='lean_notes'}=={k:v for k,v in b.items() if k!='lean_notes'}
        changed={'own4.lean_notes.status_boundary_only'}
    else:
        assert p.name=='coverage.json'
        assert [x for x in o['chapters'] if x['chapter']!=1]==[x for x in n['chapters'] if x['chapter']!=1]
        assert {k:v for k,v in o.items() if k!='chapters'}=={k:v for k,v in n.items() if k!='chapters'}
        a=next(x for x in o['chapters'] if x['chapter']==1);b=next(x for x in n['chapters'] if x['chapter']==1)
        changed={k for k in a.keys()|b.keys() if a.get(k)!=b.get(k)}
        assert changed=={'status','boundary','FINAL_receipt'} and b['accepted'] is False and b['mandatory_count'] is None
    changes.append(dict(path=p.as_posix(),changed_fields=sorted(changed),before_sha256=old[p.as_posix()]['before_sha256'],after_sha256=sha(p)))
suffixes=[]
for name,count in [('trials.jsonl',6),('lifecycle-sessions.jsonl',1),('retrieval-index-v1.jsonl',1)]:
    p=RUN/name;a=Path(old[p.as_posix()]['snapshot']).read_bytes();b=p.read_bytes();assert b.startswith(a)
    appended=[json.loads(s) for s in b[len(a):].decode('utf8').splitlines() if s.strip()]
    assert len(appended)==count
    assert all(x.get('task',x.get('session_id'))==TASK for x in appended)
    suffixes.append(dict(path=p.as_posix(),exact_old_prefix=True,appended_rows=count,own_task_only=True,after_sha256=sha(p)))
assert sha(RUN/'own-artifact-journal.md')==old[(RUN/'own-artifact-journal.md').as_posix()]['before_sha256']
a=load(old[CONTRIBUTION.as_posix()]['snapshot']);b=load(CONTRIBUTION)
top={k for k in a.keys()|b.keys() if a.get(k)!=b.get(k)}
assert top=={'truth_boundary','semantic_roundtrip','verification','graph_contribution'}
write(RUN/'post-FINAL-field-suffix-audit-v2.json',dict(reader_changes=changes,native_suffixes=suffixes,
    contribution_changed_top_fields=sorted(top),journal_unchanged=True,
    task_obligations_conversion_old_RAW_preserved=True,new_source17_ledger='chapter-one-post-native-v5.json',
    permission_sha256=sha(RUN/'FINAL-receipt-v1.json'),metadata_field_repair=True,
    chapter_complete=False,goal_complete=False))
write(RUN/'post-FINAL-status-field-repair-v2.md','Pre-build field audit identified the new key known_gaps in OWN Chapter1 chapter row. Its intended status list was moved to the existing open_gaps field and the own new key removed, with exact pre-repair RAW and new reader bindingsv5. OtherBook rows, mathematical notes and source assumptions unchanged. This is a bounded status-field repair caught before any site build, not a mathematical target change or a claimed failed compiler.')
write(RUN/'post-FINAL-shadow-memory-v1.md','Task: `'+TASK+'`\n\nCurrent17 source objects source-reconciled-native after distinct FINAL; chapter gate pending updated status site/post-native/delivery. Last accepted verifier is distinct reviewer FINAL, recorded via actual owned CLI. Whole16GoalACTIVE.\n')
native('post-FINAL-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; current Chapter1 source17 reconciliation only',
    '--leaf',TASK,'--kind','review','--statement','All17 source audit objects reconciled after actual same-run4proofs/27canaries/combined gates and distinct FINAL. Current status-site/post-native/delivery gate pending; no chapter/Goal completion.',
    '--file',str(RUN/'FINAL-review-v1.md'),'--source-status','accepted','--leaf-status','gate-pending',
    '--dependency','review:source17-FINAL:accepted','--trials',str(RUN/'trials.jsonl'),'--memory',str(RUN/'memory-index-post-FINAL-v1.jsonl'),
    '--shadow-status','pending','--output',str(RUN/'post-FINAL-frontier-v1.json'))
native('post-FINAL-frontier-shadow-v1','frontier-shadow','--trials',str(RUN/'trials.jsonl'),'--memory-digest',str(RUN/'post-FINAL-shadow-memory-v1.md'),'--frontier',str(RUN/'post-FINAL-frontier-v1.json'))
s=load(RUN/'post-FINAL-frontier-shadow-v1.log');assert not s['mismatches'] and s['inferred_frontier']['source_status']=='accepted'
write(RUN/'post-FINAL-shadow-gate-v1.json',dict(actual_shadow=s,actual_exit=0,global_mutation=False,chapter_complete=False,goal_complete=False))
print('Exact own fields/prefixes audited; native shadow passed; updated clean site and distinct post-native review required.')
