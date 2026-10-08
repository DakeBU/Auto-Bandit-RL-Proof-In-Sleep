from common_integrated_v2 import *
fixed_integrated()
gate('contributor-committed-exact-base-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
log=(RUN/'contributor-committed-exact-base-v2.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in log and 'changed contribution contracts: 1' in log,log
assert 'contributor contract passed' in log.lower(),log
write(RUN/'integrated-gates-v2.json',dict(status='Actual combined root/Tests/full harness/own shadow and nonvacuous committed exact-base contributor passed.',
    source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),affected_production_paths=5,changed_contracts=1,
    root_jobs=9097,Tests_jobs=9253,harness_tests=472,harness_skips=7,
    committed_contributor_receipt_sha256=sha(RUN/'contributor-committed-exact-base-v2-exit.json'),
    root_log_sha256=sha(RUN/'combined-root-v2.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v2.log'),harness_log_sha256=sha(RUN/'full-harness-v2.log'),
    no_vacuous_zero_path_acceptance=True,inherited_main_five_modules_unwaived=True,globalSGB_unchanged=True,
    clean_site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
expected=['BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningHistory.lean','BanditRLProof/OnlineLearningIID.lean',
    'BanditRLProof/OnlineLearningInformation.lean','BanditRLProof/OnlineLearningStochastic.lean']
command=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main']
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'inherited-main-relative-contributor-v2.log',child.stdout)
text=child.stdout.decode('utf8',errors='replace')
assert child.returncode!=0 and all(p in text for p in expected),text
write(RUN/'inherited-main-relative-contributor-v2.json',dict(command=command,actual_exit_code=child.returncode,
    log_sha256=sha(RUN/'inherited-main-relative-contributor-v2.log'),unwaived_modules=expected,
    status='Actual inherited main-relative rejection retained; REQUIRED future audits, not accepted by this package.',
    does_not_replace_exact_stacked_base_gate=True,chapter_complete=False,goal_complete=False))
print('Actual committed gate:5production paths/1contract passes; inherited5main audits remain REQUIRED.')
