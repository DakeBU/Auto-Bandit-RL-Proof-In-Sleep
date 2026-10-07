from common_v1 import *
fixed(proving=True,integrated=True)
assert load(RUN/'site-check-v1-exit.json')['exit_code']==1 and 'one to six explicit featured teaching notes' in (RUN/'site-check-v1.log').read_text(encoding='utf-8')
p=Path('website/content/highlights.json');d=load(p);before=p.read_bytes();write(RUN/'snapshots/reader-feature-before-v2-highlights.raw',before)
r=next(x for x in load('website/content/readings.json')['readings'] if x['slug']=='online-foundations');route=set(r['teaching_route']);assert len(route)==4
changed=[]
for n in d['highlights']:
 if n['full_name'] in route:
  assert n['featured'] is False;n['featured']=True;changed.append(n['full_name'])
assert set(changed)==route
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
cpath=Path('research-wiki/contribution-contracts/online-ftl-state-20261007.json');c=load(cpath)
c['progress_updates']['teaching_route']='updated: Preserve all6 old sourcecards/oldnote mathematics/text and4 curated IDs; mark those4 existing actual-route notes featured, as required when total notes exceed6. Append one full state sourcecard/9notes.'
c['verification']['site_check']='Same10823old IDsURLs/nativehashes+12new production nodes expected; seven sourcecards, nine newnotes, four existing curated route IDs retained with explicit featured metadata. Actual site-v1 metadata failure retained; current repaired site/registry/pixels pending.'
cpath.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'reader-feature-repair-v2.json',dict(actual_site_v1_check_exit=1,actual_failure='online-foundations needs one to six explicit featured teaching notes',exact_checker='When chapter has >6 notes it requires1..6 featured=True; renderer uses existing reading.teaching_route independently, no fallback selection. Prior commentary fallback explanation was inaccurate; corrected here.',changed_metadata=[dict(name=n,field='featured',before=False,after=True) for n in changed],same_four_existing_actual_teaching_route_ids=True,allold_note_text_math_headers_proofbodies_definitions_Books_unchanged=True,allold6_sourcecards_unchanged=True,new9notes_and_complete_sourcecard_unchanged=True,failed_v1site_and_logs_preserved=True,source_contract_terminal_unchanged=True,chapter_complete=False,goal_complete=False))
native('reader-feature-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(scope='Four existing teaching-route metadata flags only',repair=(RUN/'reader-feature-repair-v2.json').as_posix(),source_math_unchanged=True)))
native('reader-feature-candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(scope='Same compiled public terminals; repaired metadata pending current site checks',source_math_unchanged=True)))
s=(RUN/'audit-scope-v1.py').read_text(encoding='utf-8')
old="if key=='highlights':assert c[key][:len(a[key])]==a[key] and {x['full_name'] for x in c[key]}-{x['full_name'] for x in a[key]}==names"
new="""if key=='highlights':
  route=set(next(x for x in load('website/content/readings.json')['readings'] if x['slug']=='online-foundations')['teaching_route'])
  for oldnote,newnote in zip(a[key],c[key][:len(a[key])]):
   if oldnote['full_name'] in route:
    assert oldnote['featured'] is False and newnote['featured'] is True
    assert {k:v for k,v in oldnote.items() if k!='featured'}=={k:v for k,v in newnote.items() if k!='featured'}
   else:assert oldnote==newnote
  assert {x['full_name'] for x in c[key]}-{x['full_name'] for x in a[key]}==names"""
assert old in s;s=s.replace(old,new).replace('allold6cards_notes_math_links_globs_Books_preserved=True','allold6cards_note_text_math_links_globs_Books_preserved=True,four_existing_route_featured_flags_explicit_only=True')
write(RUN/'audit-scope-v2.py',s)
s=(RUN/'verify-registry-v1.py').read_text(encoding='utf-8').replace('online-ftl-state-site-v1','online-ftl-state-site-v2').replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'")
write(RUN/'verify-registry-v2.py',s)
for suffix in ['py','cjs']:
 s=(RUN/('capture-reader-v1.'+suffix)).read_text(encoding='utf-8').replace('-v1','-v2')
 write(RUN/('capture-reader-v2.'+suffix),s)
write(RUN/'continue-reader-site-v3.py','''from common_v1 import *
fixed(proving=True,integrated=True)
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Repair FTL-state explicit teaching metadata after actual site failure'],check=True)
gate('contributor-reader-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v3')
gate('source-scope-reader-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','reader-v3')
native('full-harness-reader-v3','check')
raw=(RUN/'full-harness-reader-v3.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
write(RUN/'combined-gates-reader-v3.json',{**load(RUN/'combined-gates-reader-v2.json'),'current_feature_metadata_repair_checked':True,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v3.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Bind current FTL-state source and repaired reader gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-state-site-v2');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-state-site-build-v2.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes());write(RUN/'site-build-v2-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
fixed(proving=True,integrated=True)
''')
# Version all prepared future consumers so FINAL sees which sequence is applicable.
for n in ['record-acceptance','prepare-publication','prepare-delivery']:
 s=(RUN/(n+'-v1.py')).read_text(encoding='utf-8').replace('registry-v1.json','registry-v2.json').replace('pixel-review-v1.json','pixel-review-v2.json').replace('registry-v1/site-v1','registry-v2/site-v2')
 if n=='prepare-publication':s=s.replace('digest-name/read-only retrieval failures','digest-name/diagnostic-parser/site-feature/read-only retrieval failures')
 write(RUN/(n+'-v2.py'),s)
s=(RUN/'complete-publication-v1.py').read_text(encoding='utf-8').replace('prepare-publication-v1.py','prepare-publication-v2.py').replace("RUN/'audit-scope-v1.py'","RUN/'audit-scope-v2.py'")
write(RUN/'complete-publication-v2.py',s)
write(RUN/'publication-tools-before-FINAL-v2.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['record-acceptance-v2.py','prepare-publication-v2.py','create-pr-v1.py','complete-publication-v2.py','prepare-delivery-v2.py','audit-committed-raw-v1.py']],scope='Current active prepared sequence ONLYv2 acceptance/publication/delivery. V1 retained unexecuted plan, disabled by absent registry-v1. Applicable registry-v2/site-v2 explicit, no earlier failed-site claim. DistinctFINAL stillpending.',source_math_unchanged=True,chapter_complete=False,goal_complete=False))
s=(RUN/'prepare-final-review-v1.py').read_text(encoding='utf-8').replace('formula-render-v1','formula-render-v2').replace('registry-v1','registry-v2').replace('pixel-review-v1','pixel-review-v2').replace('online-ftl-state-site-v1','online-ftl-state-site-v2').replace('combined-gates-reader-v2','combined-gates-reader-v3')
s=s.replace("'site-build-v1','site-check-v1','registry-v2','formula-render-v2'","'contributor-reader-v3','scoped-diff-reader-v3','source-scope-reader-v3','full-harness-reader-v3','site-build-v2','site-check-v2','registry-v2','formula-render-v2'")
s=s.replace('alloldnotes/math/4curatedlinks/moduleglobs/otherBooks preserved','allold note text/math/4curatedIDs/moduleglobs/otherBooks preserved; only those4 old featured flags false→true metadata repair')
s=s.replace('Prepared user-authorized nativeacceptance/push/draftPR/delivery helpers are FIXEDinputs','Actual site-v1check failed because >6notes require1..6 explicit featured flags. Versionedrepair ONLYmarks the4old actualroute notes featured=true; no math/text/route-ID change, no oldnote removal, new9notes stilladditional. Corrected earlier root commentary: this is checker metadata, renderer uses four explicit teaching_route IDs, no fallback selection. Current v3harness/source/contributor checks and cleanv2site passed; earlier failedv1site/logs preserved. Prepared ACTIVEv2 nativeacceptance/publication/delivery ONLY per publication-tools-before-FINAL-v2; originalv1plans retained/unexecuted/disabled absentregistry-v1. These current helpers are FIXEDinputs')
write(RUN/'prepare-final-review-v2.py',s)
