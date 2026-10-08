from common_integrated_v2 import *
fixed_integrated()
native('Asymptotic-repair-proving-v3','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(reason='Exact source-comment append independently reviewed and applied, mathematical terminals/bodies/types unchanged',evidence=(RUN/'Asymptotic-source-append-applied-v3.json').as_posix(),combined_gates='pending-rerun')))
gate('source-scope-post-comment-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','post-comment-v3')
gate('combined-root-v2','lake','build')
gate('combined-Tests-v2','lake','build','Tests')
native('full-harness-v2','check')
# Scoped commit precedes the actual diff-aware contributor check; no N/A promotion.
owned=load(RUN/'owned-commit-paths-v2.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Qualify the mean-predictor no-regret source boundary and preserve gate repairs']]:
 r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);print('\n'.join(r.stdout.decode('utf8',errors='replace').splitlines()[-7:]),flush=True);assert r.returncode==0,cmd
gate('contributor-committed-exact-base-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
log=(RUN/'contributor-committed-exact-base-v3.log').read_text(encoding='utf8')
assert 'affected production paths: 6' in log and 'changed contribution contracts: 1' in log and 'N/A' not in log
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];out=RUN/'main-relative-diagnostic-v3.log';start=time.time()
with out.open('wb') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v3-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=r.returncode,seconds=round(time.time()-start,3),log_sha256=sha(out),scope='Actual committed full-stack main-relative diagnostic. Failures remain required/unwaived.',chapter_complete=False,goal_complete=False))
text=out.read_text(encoding='utf8');missing=[f'BanditRLProof/OnlineLearning{n}.lean' for n in ['Foundations','History','IID','Information','Stochastic']]
assert r.returncode==1 and all(p in text for p in missing) and 'BanditRLProof/OnlineLearningAsymptotic.lean' not in text,text
gate('scoped-diff-v3','git','diff','--check',BASE)
write(RUN/'integrated-gates-v3.json',dict(status='Actual combined root/Tests/fullharness and NONVACUOUS committed exact-base contributor/diff gates passed after separately reviewed source-comment append',root_gate='combined-root-v2',Tests_gate='combined-Tests-v2',full_harness_gate='full-harness-v2',own_shadow_gate='candidate-frontier-shadow-v1',actual_contributor_gate='contributor-committed-exact-base-v3',committed_production_paths=6,committed_manifests=1,v1_contributor_claim_superseded='Precommit zero-path N/A is not acceptance; v2 actual unchanged-file rejection retained, v3 six real production paths controls.',committed_source=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),Asymptotic_source_comment_sha256=sha(APPEND_PATH),remaining_main_relative_modules=missing,main_relative_diagnostic_exit=1,main_relative_gaps_unwaived=True,clean_site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
native('Asymptotic-recandidate-v3','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='Applicable combined gates and nonvacuous six-path contributor check passed; five other main-relative modules remain open',integrated=(RUN/'integrated-gates-v3.json').as_posix(),source_package_accepted=False)))
fixed_integrated();print(log);print(text[-1400:]);print('New applicable combined gates passed. Clean site/FINAL/delivery remain.')
