from common_v1 import *
fixed(proving=True,integrated=True);assert load(RUN/'contributor-exact-v1-exit.json')['exit_code']==1
gate('full-harness-metadata-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
raw=(RUN/'full-harness-metadata-v2.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
combined=load(RUN/'combined-gates-v1.json');combined.update(effective_full_harness='full-harness-metadata-v2',current_contributor_prefix_repair_included=True,mathematical_bodies_unchanged=True)
write(RUN/'combined-gates-metadata-v2.json',combined)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Repair contributor progress schema without changing FTL mathematics'],check=True)
gate('contributor-exact-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v2')
gate('source-scope-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','v2')
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];log=RUN/'main-relative-diagnostic-v1.log';assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
assert child.returncode in [0,1];raw=log.read_text(encoding='utf-8');gaps=[]
for line in raw.splitlines():
 if 'production paths missing from all changed contribution manifests:' in line:gaps+=re.findall(r'BanditRLProof/OnlineLearning\w+\.lean',line)
gaps=sorted(set(gaps))
if child.returncode:
 expected=['BanditRLProof/OnlineLearning'+n+'.lean' for n in ['Asymptotic','Foundations','History','IID','Information','Mean','Regret','Stochastic']];assert gaps==sorted(expected),dict(actual=gaps,expected=expected)
write(RUN/'main-relative-diagnostic-v1.json',dict(status='passed' if child.returncode==0 else 'failed-unwaived',actual_exit_code=child.returncode,actual_production_gaps=gaps,FTL_own_production_gap_resolved='BanditRLProof/OnlineLearningFTL.lean' not in gaps,other_required_gaps=len(gaps),Foundations_gap_unwaived='BanditRLProof/OnlineLearningFoundations.lean' in gaps,exact_PR187_base_separately_passed=True,no_waiver=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Record exact-base FTL gates and actual eight unwaived chapter gaps'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-sharp-site-v1');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-sharp-site-build-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes());write(RUN/'site-build-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed(proving=True,integrated=True)
