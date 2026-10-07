from common_integrated_v1 import *
fixed_integrated()
failed=load(RUN/'site-build-v1-exit.json');assert failed['exit_code']==1
log=(RUN/'site-build-v1.log').read_text(encoding='utf8');assert 'missing_highlight_dependencies' in log and 'log_add_one_le_harmonic' in log
p=Path('website/content/highlights.json');data=load(p);note=next(x for x in data['highlights'] if x['full_name']==PRE+'randomized_log_lower')
assert note['dependencies']==[PRE+'randomized_harmonic_lower','log_add_one_le_harmonic']
assert 'Mathlib log_add_one_le_harmonic' in note['proof_idea']
note['dependencies']=[PRE+'randomized_harmonic_lower']
p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'site-dependency-repair-v2.json',dict(failed_gate='site-build-v1',exit_code=1,log_sha256=sha(RUN/'site-build-v1.log'),cause='Existing website validate_content dependencies are shared ABRL production registry declarations; Mathlib declaration is correctly not scanned into that registry.',repair='Remove only Mathlib from the new note dependencies array. Its full name/proof explanation remains visible and actual VALUE pair remains in compiled graph. No scanner/schema/pin changes and no public/canary proof/header changes.',changed_file=p.as_posix(),changed_sha256=sha(p),statement_contract_version_unchanged=1,all_r1_to_r8_requirements_preserved=True,chapter_complete=False,goal_complete=False))
native('site-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,reason='Actual website registry dependency validation failure',repair_evidence=(RUN/'site-dependency-repair-v2.json').as_posix(),mathematical_contract_unchanged=True,source_package_accepted=False)))
native('site-recandidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,reason='Website shared declaration dependency presentation repaired; actual mathlib VALUE pair unchanged',combined_Lean_gate='integrated-gates-v2',site_gate='pending-v2',source_package_accepted=False)))
fixed_integrated()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Repair shared registry dependency presentation for lower reader']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Clean metadata repair commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
