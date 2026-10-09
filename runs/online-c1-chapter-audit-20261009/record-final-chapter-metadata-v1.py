from common_reader_v8 import *
import copy
fixed()
post=load(RUN/'post-native-receipt-v1.json')
assert sha(RUN/'post-native-receipt-v1.json')=='4cf9879ed2a67f32754eed9323aa01cb2659dbd7b38f5912a215200148affd1b'
assert sha(post['report'])==post['report_sha256']=='03276bc705a18feec0c5e1d53818090d50a99d61b8a6ce10abddb9000925e78f'
assert post['verdict']=='accepted-with-explicit-delta' and not post['required_repairs']
assert post['chapter_accepted_local_metadata_authorized'] and post['final_exact_head_review_required']
for r in load(RUN/'post-native-inputs-v1.json')['rows']:assert sha(r['path'])==r['sha256'],r['path']
coverage=ROOT/'docs/contracts/online-book-v1/coverage.json'
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
mutables=[coverage,CONTRIBUTION,*docs,RUN/'trials.jsonl']
before=[]
for i,p in enumerate(mutables):
 s=RUN/'snapshots'/('before-final-chapter-v1-'+str(i).zfill(2)+'.raw');write(s,p.read_bytes())
 before.append(dict(path=p.as_posix(),before_sha256=sha(p),snapshot=s.as_posix()))
write(RUN/'final-chapter-metadata-before-v1.json',dict(rows=before,permission_sha256=sha(RUN/'post-native-receipt-v1.json')))
status='accepted-local-with-explicit-source-correction'
ledger=load(CONTRACT/'chapter-one-post-native-v5.json')
for row in ledger['rows']:
 row['historical_source_state']=row.get('state');row['state']=status
 row['status']=status;row['current_gate_status']=status
 row['post_native_verdict']='accepted-with-explicit-delta'
 row['post_native_receipt_sha256']=sha(RUN/'post-native-receipt-v1.json')
ledger.update(accepted_source_objects_this_current_chapter_gate=17,chapter_complete=True,goal_complete=False,
 chapter_gate_scope='Only the17 exhaustively reviewed Chapter1 maintext source objects, with explicit ordinary-limit correction; not all16chapters, all exercises, or a false theorem proof.',
 source_FINAL_receipt_sha256=sha(RUN/'FINAL-receipt-v1.json'),post_native_receipt_sha256=sha(RUN/'post-native-receipt-v1.json'),
 final_exact_head_delivery_review_required=True,
 final_exact_head_delivery_review_path=(ROOT/'tmp/online-c1-chapter-audit-final-delivery-review-v1.json').as_posix(),
 delivery_boundary='Existing mathematical/source/current-reader head14567d01 published and independently reviewed. Final OWN metadata/evidence commit and non-force push must receive the required short exact-head review before starting Chapter2. That review is an ignored local receipt to avoid recursive publication.',
 whole_Goal_status='ACTIVE',main_live_updated=False,merged=False,deployed=False)
write(CONTRACT/'chapter-one-accepted-v6.json',ledger)
d=load(coverage);old=copy.deepcopy(d);c=next(x for x in d['chapters'] if x['chapter']==1)
c.update(status=status,accepted=True,post_native_receipt=(RUN/'post-native-receipt-v1.json').relative_to(ROOT).as_posix(),
 current_acceptance_ledger=(CONTRACT/'chapter-one-accepted-v6.json').relative_to(ROOT).as_posix(),
 final_exact_head_delivery_review_required=True,
 final_exact_head_delivery_review_path='tmp/online-c1-chapter-audit-final-delivery-review-v1.json')
assert c['mandatory_count'] is None and c['unknown_required_proof_leaf_count'] is None
assert {k:v for k,v in d.items() if k!='chapters'}=={k:v for k,v in old.items() if k!='chapters'}
assert [r for r in d['chapters'] if r['chapter']!=1]==[r for r in old['chapters'] if r['chapter']!=1]
coverage.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
bindings=load(RUN/'reader-integration-bindings-v5.json')
for r in bindings['rows']:
 if Path(r['path'])==coverage:
  s=RUN/'snapshots'/'reader-result-final-chapter-v6.raw';write(s,coverage.read_bytes())
  r['planned_result_snapshot']=s.as_posix();r['result_sha256']=sha(coverage)
bindings['post_native_final_C1_status_only']=True;bindings['post_native_receipt_sha256']=sha(RUN/'post-native-receipt-v1.json')
write(RUN/'reader-integration-bindings-v6.json',bindings)
guard=(RUN/'common_reader_v8.py').read_text('utf8').replace('reader-integration-bindings-v5.json','reader-integration-bindings-v6.json')
write(RUN/'common_final_v9.py',guard)
names=ledger['rows'][-1]['lean_names'];assert len(names)==4
oldsentence='Updated status reader/site, own shadow, separate post-native and PR203 delivery review remain prerequisites to chapter acceptance.'
newsentence=('Own native/shadow, current SITE4/registry/browser, all10 distinct current pixels and post-native/published-head review now pass in their separate scopes. '
 'The source17 Chapter1 gate is accepted locally with explicit source correction; required final metadata/evidence commit/push and short exact-head review are recorded separately before Chapter2 work. '
 'See chapter-one-accepted-v6.json and post-native-receipt-v1.json; no runtime claim that a single command enforces the full scholarly workflow.')
for p in docs:
 text=p.read_text('utf8');assert oldsentence in text
 text=text.replace('Status: `source-reconciled-native; chapter gate pending`','Status: `'+status+'`').replace(oldsentence,newsentence)
 lines=text.splitlines();matches=[i for i,s in enumerate(lines) if s.startswith('| C1-FTL-ANY-INITIAL-GUARANTEE |')];assert len(matches)==1
 lines[matches[0]]='| C1-FTL-ANY-INITIAL-GUARANTEE | accepted-with-explicit-delta | '+', '.join('`'+n+'`' for n in names)+' |'
 p.write_bytes(('\n'.join(lines)+'\n').encode('utf8'))
d=load(CONTRIBUTION)
d['semantic_roundtrip']['remaining_semantic_delta']='Chapter1 source17 and post-native/current-reader/published-head review accepted-with-explicit-delta. Ordinary-limit correction, explicit IID models and derived constants remain visible. Final metadata/evidence exact-head delivery check required separately; wholeGoalACTIVE/mainliveunchanged.'
d['truth_boundary']+=' Current source17 Chapter1 gate accepted locally with explicit source correction after distinct post-native review. Final metadata/evidence exact-head delivery check remains required before Chapter2; no book/merge/live completion.'
d['verification']['site_build']='Actual clean SITE4 source14567d019c31f8f307ac5ab765144ae7d71f1ea1 built with unchanged applicable combined Lean gate; no further website JSON/code/pin changes. No deployment.'
d['verification']['site_check']='Actual SITE4/check/registry passed; complete10977oldrecords+4publictheorems preserved; current Node0 AND wrapper0 and all10 current pixels personally viewed by formalizer and distinct reviewer. Two NONEMPTY contributor bases passed. Historical failures retained.'
d['verification']['independent_review']='Distinct automated source FINAL b10f8558/receipt7f0ade24 and post-native03276bc7/receipt4cf9879e accepted-with-explicit-delta. Fixed1264 RAW/current10pixels/native/source17/delivery14RAWexceptions adjudicated. Short final exact-head metadata delivery review required; no human/external/absolute-blind/runtime model attestation.'
d['progress_updates']['results_ledger']='updated: current source17 Chapter1 accepted-local-with-explicit-source-correction in chapter-one-accepted-v6.json and coverage.json; original Sept14 seven-group history retained; proof_totalnull; exact final metadata delivery review required before Chapter2.'
CONTRIBUTION.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
native('final-chapter-review-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
 '--attempt-id','C1-POST-NATIVE-DELIVERY-V1','--reviewer-validated','--run-id',RUN.name,'--progress-class','diagnostic',
 '--notes','Formalizer records distinct post-native/current10pixels/published14567head review accepted-with-explicit-delta. Source17 Chapter1 local gate status authorized; no new mathematical proof/count or wholeGoal/main/live claim. Final metadata commit/push requires one short exact-head check before Chapter2.',
 '--verifier-evidence',str(RUN/'post-native-receipt-v1.json'),'--verifier-evidence',str(RUN/'post-native-review-v1.md'))
native('final-chapter-memory-v1','memory-record','--type','checkpoint','--task',TASK,'--provenance-kind','distinct_post_native_delivery',
 '--provenance',str(RUN/'post-native-receipt-v1.json'),'--status',status,'--verifier',str(RUN/'post-native-receipt-v1.json'),
 '--role','reviewer','--details-json',json.dumps(dict(source_objects=17,proof_total=None,whole_Goal_status='ACTIVE',final_exact_head_delivery_review_required=True)),
 '--output',str(RUN/'memory-index-final-chapter-v1.jsonl'))
write(RUN/'final-chapter-shadow-memory-v1.md','Task: `'+TASK+'`\n\nDistinct post-native source17/current-reader/published-head acceptance recorded; final OWN metadata delivery check required before Chapter2. Whole1-16GoalACTIVE, main/live unchanged. No new mathematics or proof-denominator claim.')
native('final-chapter-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; current Chapter1 source17 local gate only',
 '--leaf',TASK,'--kind','review','--statement','Chapter1 source17 local gate accepted-with-explicit-source-correction after actual mathematical/native/site/post-native/published-head gates. Final OWN metadata/evidence exact-head delivery review required; wholeGoalACTIVE.',
 '--file',str(RUN/'post-native-review-v1.md'),'--source-status','accepted','--leaf-status','accepted','--dependency','review:post-native-delivery:accepted',
 '--trials',str(RUN/'trials.jsonl'),'--memory',str(RUN/'memory-index-final-chapter-v1.jsonl'),'--shadow-status','pending','--output',str(RUN/'final-chapter-frontier-v1.json'))
native('final-chapter-frontier-shadow-v1','frontier-shadow','--trials',str(RUN/'trials.jsonl'),'--memory-digest',str(RUN/'final-chapter-shadow-memory-v1.md'),'--frontier',str(RUN/'final-chapter-frontier-v1.json'))
s=load(RUN/'final-chapter-frontier-shadow-v1.log');assert not s['mismatches']
write(RUN/'final-chapter-own-shadow-v1.json',dict(actual_exit=0,actual_shadow=s,global_mutation=False,whole_Goal_status='ACTIVE',final_exact_head_delivery_review_required=True))
audits=[]
for r in before:
 p=Path(r['path']);a=Path(r['snapshot']).read_bytes();b=p.read_bytes()
 if p.name=='trials.jsonl':
  assert b.startswith(a);suffix=[json.loads(x) for x in b[len(a):].decode('utf8').splitlines() if x.strip()]
  assert len(suffix)==1 and suffix[0]['task']==TASK
  audit=dict(exact_old_prefix=True,owned_appended_rows=1)
 elif p.suffix=='.json':
  old=json.loads(a.decode('utf8'));new=json.loads(b.decode('utf8'))
  if p==coverage:
   old=next(x for x in old['chapters'] if x['chapter']==1);new=next(x for x in new['chapters'] if x['chapter']==1)
   allowed={'status','accepted','post_native_receipt','current_acceptance_ledger','final_exact_head_delivery_review_required','final_exact_head_delivery_review_path'}
  else:allowed={'semantic_roundtrip','truth_boundary','verification','progress_updates'}
  changes={k for k in old.keys()|new.keys() if old.get(k)!=new.get(k)};assert changes==allowed,(p,changes)
  audit=dict(changed_fields=sorted(changes))
 else:audit=dict(own_status_paragraph_and_last_convenience_table_cell_only=True,exact_old_RAW_preserved=True)
 audits.append(dict(path=p.as_posix(),before_sha256=r['before_sha256'],after_sha256=sha(p),audit=audit))
web=[ROOT/'website/content'/n for n in ['chapters.json','readings.json','highlights.json']]
indexed={r['path']:r['sha256'] for r in load(RUN/'post-native-inputs-v1.json')['rows']}
assert all(sha(p)==indexed[p.as_posix()] for p in web)
write(RUN/'final-chapter-field-suffix-audit-v1.json',dict(rows=audits,three_website_JSONs_unchanged=True,source_math_roots_Tests_pins_unchanged=True,other_15_chapters_unchanged=True,source17_proof_total_null=True,final_exact_head_review_required=True,whole_Goal_status='ACTIVE'))
snapshots={sha(p):p for p in (RUN/'snapshots').rglob('*') if p.is_file()}
changed=[];same=0
for r in load(RUN/'post-native-inputs-v1.json')['rows']:
 if sha(r['path'])==r['sha256']:same+=1;continue
 assert r['sha256'] in snapshots,r['path']
 changed.append(dict(path=r['path'],post_native_sha256=r['sha256'],exact_before_snapshot=snapshots[r['sha256']].as_posix(),current_sha256=sha(r['path'])))
assert len(changed)==6
write(RUN/'final-chapter-post-native-historical-resolution-v1.json',dict(input_count=1264,unchanged_live_count=same,changed=changed,all_changes_snapshot_bound=True))
print('Scoped Chapter1 final status recorded; exact6 before-bindings/fields and own shadow audited. Final commit/push/short distinct exact-head check remains.')
