from common_v1 import *
fixed(proving=True,integrated=True)
actual_exit=load(RUN/'main-relative-diagnostic-v1-exit.json')['exit_code']
raw=(RUN/'main-relative-diagnostic-v1.log').read_text(encoding='utf-8')
gaps=sorted(set(re.findall(r'BanditRLProof/OnlineLearning\w+\.lean',raw)))
assert actual_exit==1 and len(gaps)==7
write(RUN/'main-relative-diagnostic-v1.json',dict(status='passed' if actual_exit==0 else 'failed-unwaived',actual_exit_code=actual_exit,actual_production_gaps=gaps,Mean_gap_resolved='BanditRLProof/OnlineLearningMean.lean' not in gaps,other_required_gaps=len(gaps),Foundations_gap_unwaived='BanditRLProof/OnlineLearningFoundations.lean' in gaps,exact_PR188_base_separately_passed=True,no_waiver=True,chapter_complete=False,goal_complete=False))
chapterpath=Path('website/content/chapters.json');chapterdata=load(chapterpath);chapter=next(x for x in chapterdata['chapters'] if x['slug']=='online-foundations')
chapter['completion_blockers'][1]='General initial prediction and recursive mean/count terminal are locally compiled and BODY-reviewed. The actual main-relative gate resolves Mean and preserves seven other required production gaps: Asymptotic, Foundations, History, IID, Information, Regret and Stochastic. These are FAILUNWAIVED; no chapter acceptance or main integration.'
chapterpath.write_bytes((json.dumps(chapterdata,ensure_ascii=False,indent=2)+'\n').encode())
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Record actual seven main gaps and diagnostic parser repair'],check=True)
gate('contributor-reader-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v2')
gate('source-scope-reader-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','reader-v2')
native('full-harness-reader-v2','check')
raw=(RUN/'full-harness-reader-v2.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
write(RUN/'combined-gates-reader-v2.json',{**load(RUN/'combined-gates-v1.json'),'current_reader_main_gap_boundary_checked':True,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v2.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Bind current FTL-state reader and source-scope gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-state-site-v1');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-state-site-build-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes());write(RUN/'site-build-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
fixed(proving=True,integrated=True)
