from common_v1 import *
fixed(True);assert load(RUN/'contributor-exact-v1-exit.json')['exit_code']==1
raw=(RUN/'contributor-exact-v1.log').read_text(encoding='utf-8');assert 'not changed protected/production surfaces' in raw
p=Path('research-wiki/contribution-contracts/online-foundations-public-20261007.json')
write(RUN/'snapshots/contributor-before-schema-repair-v1.raw',p.read_bytes());c=load(p)
assert c['affected_files']==[PUBLIC.as_posix(),CANARY.as_posix(),'Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
c['affected_files']=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
note='The actual contributor CLI matches affected_files to changed protected/production surfaces for the selected Git base. Tests.lean/new Tests module are validated separately by explicit owned-test metadata, native fences and full Tests/root gate; this CLI version does not classify them as protected production surfaces. The public Foundations module is reused byte-for-byte and is not a current-branch production delta. Therefore ALL NINE Chapter1 origin/main contributor gaps, INCLUDING retained Foundations, remain FAILUNWAIVED until a reviewed main-relative integration package addresses them. Eight OTHER modules still require current semantic migration; this package is a bounded source/test/reader revalidation, not a completed main-relative Foundations integration.'
c['truth_boundary']+=' '+note
c['verification']['contributor_scope']=note
p.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
for path,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('full_name')==PRE+'lemma_1_2'),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 d=load(path);x=next(a for a in d[key] if pred(a))
 if key=='readings':x['source_theorems'][0]['local_status']['boundary']+=' '+note;x['worked_example']['boundary']+=' '+note
 elif key=='highlights':x['lean_notes']+=' '+note
 else:x['completion_blockers'].append(note);x['open_gaps'].append(note)
 Path(path).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'contributor-metadata-repair-v2.json',dict(failed_gate_sha256=sha(RUN/'contributor-exact-v1-exit.json'),failed_log_sha256=sha(RUN/'contributor-exact-v1.log'),source_checker_SHA256=sha('tools/check_contributor_contract.py'),cause='affected_files incorrectly included unchanged public file and test surfaces absent from this actual CLI production set',repair='Limit manifest affected_files to three actual changed production JSONs; retain separate full test ownership/fences/root gate; explicitly retain all nine main-relative Chapter1 gaps including this unchanged public module.',mathematical_contract_version=1,all_source_public_tests_headers_and_bodies_unchanged=True,native_statement_hash=fixed(True)['native_header_hash'],main_relative_gate_not_waived=True,original_failure_preserved=True,actual_recheck_pending=True))
write(RUN/'contributor-gap-boundary-v2.md',note)
fixed(True);print('Concrete base-specific manifest metadata corrected; nine main-relative gaps explicitly retained; actual gates pending.')
