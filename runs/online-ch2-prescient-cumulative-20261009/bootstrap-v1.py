from common import *
assert Path.cwd() == ROOT and sha(PDF) == PDF_SHA
capture('fresh-fetch-v1','git','fetch','origin')
_,current = capture('initial-head-v1','git','rev-parse','HEAD')
assert current.strip() == BASE
_,oldbranch = capture('initial-branch-v1','git','branch','--show-current')
assert oldbranch.strip() == 'codex/research-online-ch2-prescient-causal'
_,status = capture('initial-status-v1','git','status','--porcelain=v1','-z')
assert all('runs/online-ch2-prescient-cumulative-20261009/' in x for x in status.split('\0') if x)
capture('active-worktrees-v1','git','worktree','list','--porcelain')
capture('shared-git-v1','git','rev-parse','--git-common-dir')
code,_ = capture('base-not-on-main-v1','git','merge-base','--is-ancestor',BASE,'origin/main',required=False)
assert code == 1
_,main = capture('origin-main-v1','git','rev-parse','origin/main')
_,pr = capture('parent-PR211-v1','gh','pr','view','211','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergeCommit')
pj=json.loads(pr)
assert pj['state']=='OPEN' and pj['headRefOid']==BASE and pj['headRefName']==oldbranch.strip() and pj['mergeCommit'] is None
_,branches = capture('new-branch-absent-v1','git','branch','--list',BRANCH)
assert not branches.strip() and not PUBLIC.exists()
tracked=subprocess.check_output(['git','ls-files','-z']).decode('utf8').split('\0')
write(RUN/'baseline-v1.json',dict(base=BASE, origin_main=main.strip(), rows=rows(ROOT/p for p in tracked if p), parent_PR=pj, stacked=True))
capture('create-stacked-branch-v1','git','switch','-c',BRANCH,BASE)
write(RUN/'native-scoped.py',(ROOT/'runs/online-ch2-prescient-causal-20261009/native-scoped.py').read_bytes())
fixed()
from pypdf import PdfReader
reader=PdfReader(str(PDF))
for n in [26,28,29,75,76,277,278]:
    write(RUN/('source-pdf%d.txt'%n), reader.pages[n-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization', author='Francesco Orabona', url='https://arxiv.org/pdf/1912.13213v10', version='v10', version_date='2026-06-21', pdf=PDF.as_posix(), pdf_sha256=sha(PDF), pages=rows(RUN/('source-pdf%d.txt'%n) for n in [26,28,29,75,76,277,278]), anchors=['Algorithm15.8 printed265/PDF277','Theorem15.30 printed265-266/PDF277-278 incl mandatory fixed-step statement whose proof is left as exercise','Definition6.4 printed63/PDF75','Chapter2 forward dependency only; not early Chapter6/15 acceptance']))
for name in ['--help','lifecycle-event','trial-log','frontier-shadow','statement-fence','safe-verify','reference-index','list-papers','list-scenarios','list-weapons','search-memory','list-lean-decls']:
    args=[sys.executable,'-B','-X','utf8','tools/bandit.py',name]+([] if name=='--help' else ['--help'])
    capture('CLI-help-'+name.replace('--','')+'-v1',*args)
for name in ['list-papers','list-scenarios','list-weapons']:
    capture('roadmap-'+name+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py',name)
capture('roadmap-search-prescient-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','search-memory','prescient')
capture('own-shadow-initial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow')
write(RUN/'audit-inspected-v1.json',dict(actual_stacked_base=BASE,origin_main=main.strip(),ancestor_command_actual_exit=code,parent_PR=pj,shared_packages=str((ROOT/'.lake/packages').resolve()),baseline_tracked_files=len(load(RUN/'baseline-v1.json')['rows']), source_pdf_sha256=sha(PDF),read_only_reference_index_deferred='Actual CLI writes shared reference indexes and global journal. Will run isolated native writer at candidate integration, not overwrite baseline/global SGB during draft.',route='Chapter2 required forward dependency', no_source_or_chapter_acceptance=True,whole_Goal_status='ACTIVE'))
fixed()
print('Fresh stack audit and source extraction complete; no proof or source acceptance.')
