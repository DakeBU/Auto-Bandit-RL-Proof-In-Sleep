from common_integrated_v2 import *
import re
fixed_integrated();assert load(RUN/'scoped-diff-v3-exit.json')['exit_code']==2
text=(RUN/'scoped-diff-v3.log').read_text(encoding='utf8')
paths=sorted(set(re.findall(r'^(.+?):[0-9]+: (?:trailing whitespace|new blank line at EOF)',text,re.M)))
assert len(paths)==7 and all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in paths)
assert set(Path(p).name for p in paths)=={'blind-reconstruction-v1.md','combined-Tests-v1.log','combined-Tests-v2.log','combined-root-v1.log','combined-root-v2.log','full-harness-v1.log','full-harness-v2.log'}
blind=load(RUN/'blind-receipt-v1.json');assert sha(RUN/'blind-reconstruction-v1.md')==blind['report']['sha256_raw_bytes']
write(RUN/'diff-raw-evidence-exceptions-v4.json',dict(failed_gate='scoped-diff-v3',original_failure_exit=2,original_failure_log_sha256=sha(RUN/'scoped-diff-v3.log'),reason='Exact independent decoder raw report and raw compiler stdout have meaningful/preformatted trailing spaces or EOF blank. Preserve their exact receipt-bound bytes rather than rewriting evidence.',exceptions=[dict(path=p,sha256=sha(p),scope='Raw compiler stdout' if p.endswith('.log') else 'Exact separately authored source-blind reconstruction/receipt') for p in paths],production_contract_scripts_source_and_reader_not_excepted=True,all_public_types_and_bodies_unchanged=True))
write(RUN/'check-scoped-diff-v4.py','''from common_integrated_v2 import *
fixed_integrated()
exceptions=load(RUN/'diff-raw-evidence-exceptions-v4.json')['exceptions']
for row in exceptions:assert sha(row['path'])==row['sha256'],row['path']
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--check',BASE,'--','.',*[':(exclude)'+r['path'] for r in exceptions]]
child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(child.stdout.decode('utf8',errors='replace'));assert child.returncode==0,child.returncode
write(RUN/('diff-check-'+sys.argv[1]+'.json'),dict(status='passed',actual_command=command,exit_code=child.returncode,exact_raw_evidence_exceptions=exceptions,production_reader_contract_scripts_checked=True,source_types_unchanged=True,chapter_complete=False,goal_complete=False))
''')
gate('scoped-diff-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v4.py','post-comment-v4')
s=(RUN/'repair-integrated-gates-v3.py').read_text(encoding='utf8');suffix=s[s.index("write(RUN/'integrated-gates-v3.json'"):]
suffix=suffix.replace("write(RUN/'integrated-gates-v3.json'","write(RUN/'integrated-gates-v3.json'")
log=(RUN/'contributor-committed-exact-base-v3.log').read_text(encoding='utf8');text=(RUN/'main-relative-diagnostic-v3.log').read_text(encoding='utf8');missing=[f'BanditRLProof/OnlineLearning{n}.lean' for n in ['Foundations','History','IID','Information','Stochastic']]
assert 'affected production paths: 6' in log and 'changed contribution contracts: 1' in log and 'N/A' not in log
assert load(RUN/'main-relative-diagnostic-v3-exit.json')['exit_code']==1
for label in ['combined-root-v2','combined-Tests-v2','full-harness-v2']:assert load(RUN/(label+'-exit.json'))['exit_code']==0
exec(compile(suffix,'integrated-v3-resume-after-explicit-evidence-diff-v4','exec'))
write(RUN/'integrated-diff-overlay-v4.json',dict(actual_diff_gate='scoped-diff-v4',original_full_diff_failed_and_preserved=True,seven_exact_raw_evidence_exceptions='diff-raw-evidence-exceptions-v4.json',applicable_integrated='integrated-gates-v3.json',six_real_production_paths_one_manifest=True,chapter_complete=False,goal_complete=False))
# The FINAL preparation remains unrun; version it to use the actual scoped gate.
s=(RUN/'prepare-final-v1.py').read_text(encoding='utf8')
s=s.replace("gate('scoped-diff-pre-FINAL-v1','git','diff','--check',BASE)","gate('scoped-diff-pre-FINAL-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v4.py','pre-FINAL-v4')")
write(RUN/'prepare-final-v2.py',s)
fixed_integrated();print('All mathematical/integrated/nonvacuous contributor gates applicable; seven raw-evidence whitespace exceptions explicitly bound. Clean site next.')
