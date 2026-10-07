from common_integrated_v1 import *
fixed_integrated()
gate('contributor-exact-base-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
text=(RUN/'contributor-exact-base-v1.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in text and 'changed contribution contracts: 1' in text and 'Contributor contract passed.' in text
label='contributor-origin-main-diagnostic-v1';log=RUN/(label+'.log');assert not log.exists();start=time.time()
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main']
with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/(label+'-exit.json'),dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log),purpose='All-stacked main-relative diagnostic; unrelated required gaps remain unwaived'))
text=log.read_text(encoding='utf8');missing=re.search(r'production paths missing from all changed contribution manifests: (.*)',text)
gaps=missing.group(1).strip().split(', ') if missing else []
assert child.returncode==1 and gaps==['BanditRLProof/OnlineLearningAsymptotic.lean','BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningHistory.lean','BanditRLProof/OnlineLearningIID.lean','BanditRLProof/OnlineLearningInformation.lean','BanditRLProof/OnlineLearningStochastic.lean'],gaps
gate('scope-committed-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','committed-v1')
write(RUN/'integrated-gates-v2.json',dict(status='Actual root/Tests/fullharness/shadow and nonvacuous exact-base contributor passed',source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),root_gate='combined-root-v1',Tests_gate='combined-Tests-v1',harness_gate='full-harness-v1',contributor_gate='contributor-exact-base-v1',committed_production_paths=5,committed_manifests=1,main_relative_other_gaps=gaps,main_relative_gaps_waived=False,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Record integrated lower proof validation and contribution gate']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(child.stdout.decode('utf8',errors='replace'),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Clean validated engineering source commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
