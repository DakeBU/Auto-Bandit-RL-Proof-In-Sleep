from common_integrated_v1 import *
fixed_integrated()
assert load(RUN/'registry-v2.json')['new_registry_nodes']==59
changes=[]
for file in ['website/content/readings.json','website/content/highlights.json']:
 p=Path(file);data=load(p)
 if file.endswith('readings.json'):
  items=[next(x for x in data['readings'] if x['slug']==ROUTE)['source_theorems'][-1]]
 else:items=[x for x in data['highlights'] if x['full_name'] in [PRE+'randomized_harmonic_lower',PRE+'randomized_log_lower']]
 for item in items:
  old=item['math'];assert old.count(r'\\[\forall h:')==1
  item['math']=old.replace(r'\\[\forall h:',r'\\{}[\forall h:')
  changes.append(dict(file=file,target=item.get('full_name',item.get('label')),before_math=old,after_math=item['math']))
 p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'formula-render-repair-v3.json',dict(cause='Actual pixels displayed italic forallh rather than the full history universal quantifier: TeX aligned rowbreak immediately followed by [ is parsed as optional row spacing.',repair='Insert empty group after rowbreak, before assumption bracket in precisely three new source/public formulas. All assumptions/quantifiers/numerical content and all Lean bytes unchanged.',actual_prior_images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in ['log-lower-source-card-v1.png','public-note-6-v1.png','public-note-7-v1.png']],prior_captures_retained=True,changed_formulas=changes,source_contract_version_unchanged=1,old_eight_cards_all_old_notes_preserved=True,new_site_gate='site-build-v3 pending',chapter_complete=False,goal_complete=False))
native('render-repair-event-v3','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Actual pixel audit detected universal-history quantifier misrender',repair_evidence=(RUN/'formula-render-repair-v3.json').as_posix(),Lean_contract_unchanged=True,source_package_accepted=False)))
native('render-recandidate-event-v3','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='Exact formula rowbreak syntax repaired, no mathematical target change',render='pending-v2',source_package_accepted=False)))
s=(RUN/'verify-registry-v2.py').read_text(encoding='utf8').replace('tmp/online-log-lower-site-v1','tmp/online-log-lower-site-v2').replace("RUN/'registry-v2.json'","RUN/'registry-v3.json'")
write(RUN/'verify-registry-v3.py',s)
s=(RUN/'capture-reader-v1.cjs').read_text(encoding='utf8').replace('-v1','-v2')
write(RUN/'capture-reader-v2.cjs',s)
s=(RUN/'capture-reader-v2.py').read_text(encoding='utf8').replace('tmp/online-log-lower-site-v1','tmp/online-log-lower-site-v2').replace("RUN/'registry-v2.json'","RUN/'registry-v3.json'").replace("RUN/'capture-reader-v1.cjs'","RUN/'capture-reader-v2.cjs'").replace('formula-render-v1','formula-render-v2').replace('playwright-v1-profile','playwright-v2-profile')
write(RUN/'capture-reader-v3.py',s)
fixed_integrated()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Repair randomized lower quantifier rendering from actual pixel audit']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Clean rendering repair commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
