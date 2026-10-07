from common_v1 import *
fixed(integrated=True)
oldlog=(RUN/'contributor-exact-base-v2.log').read_text(encoding='utf-8');assert 'changed paths: 0' in oldlog and 'Contributor contract: N/A' in oldlog
write(RUN/'contributor-order-correction-v3.json',dict(original_command_exit=0,original_result='N/A: no affected committed surfaces',reason='Checker compares BASE...HEAD, excluding working changes. Prior precommit exact-base command was not a nonvacuous contributor gate.',original_record_preserved=True,applicable_current_gate='contributor-exact-base-v3',mathematical_target_changed=False,actual_source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()))
gate('contributor-exact-base-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
text=(RUN/'contributor-exact-base-v3.log').read_text(encoding='utf-8');assert 'affected production paths: 4' in text and 'changed contribution contracts: 1' in text and 'Contributor contract passed.' in text
label='contributor-origin-main-diagnostic-v3';log=RUN/(label+'.log');assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run([sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'],stdout=stream,stderr=subprocess.STDOUT)
write(RUN/(label+'-exit.json'),dict(command='tools/check_contributor_contract.py --base origin/main',cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log),unrelated_required_gaps_waived=False))
text=log.read_text(encoding='utf-8');missing=re.search(r'production paths missing from all changed contribution manifests: (.*)',text)
gaps=missing.group(1).strip().split(', ') if missing else []
assert child.returncode==1 and gaps==['BanditRLProof/OnlineLearningAsymptotic.lean','BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningHistory.lean','BanditRLProof/OnlineLearningIID.lean','BanditRLProof/OnlineLearningInformation.lean','BanditRLProof/OnlineLearningStochastic.lean'],gaps
write(RUN/'main-relative-gaps-v3.json',dict(status='Actual main diagnostic FAILUNWAIVED for6other legacy modules; current Regret source-publication coverage resolved',missing_production_paths=gaps,current_Regret_covered=True,prior7gap_log_retained=True,gate_scope='Contribution-manifest integration only, not source/math/chapter closure',chapter_complete=False,goal_complete=False))
gate('scoped-diff-committed-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','committed-v3')
gate('source-scope-committed-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','committed-v3')
write(RUN/'integrated-gates-v3.json',dict(status='Actual root/Tests/fullharness-v2 and nonvacuous committed exact-base contributor-v3 passed',source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),root_gate='combined-root-v1',Tests_gate='combined-Tests-v1',harness_gate='full-harness-v2',actual_python_tests=472,existing_skips=7,contributor_gate='contributor-exact-base-v3',committed_production_paths=4,committed_manifests=1,prior_vacuous_NA_not_acceptance=True,main_relative_other_gaps=gaps,raw_source_current_unchanged=True,new_production_math=0,site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed(integrated=True)
