from common import *
assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
capture('fresh-fetch-v1','git','fetch','origin')
_,head=capture('initial-head-v1','git','rev-parse','HEAD');assert head.strip()==BASE
_,branch=capture('initial-branch-v1','git','branch','--show-current');assert branch.strip()=='codex/research-online-ch2-prescient-cumulative'
_,status=capture('initial-status-v1','git','status','--porcelain=v1','-z')
assert all(RUN.relative_to(ROOT).as_posix()+'/' in s for s in status.split('\0') if s)
capture('active-worktrees-v1','git','worktree','list','--porcelain')
capture('shared-git-v1','git','rev-parse','--git-common-dir')
capture('canonical-research-status-v1','git','-C','E:/ABRL/research','status','--porcelain=v1','-z')
code,_=capture('base-not-on-main-v1','git','merge-base','--is-ancestor',BASE,'origin/main',required=False);assert code==1
_,main=capture('origin-main-v1','git','rev-parse','origin/main')
_,out=capture('parent-PR212-v1','gh','pr','view','212','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt')
pr=json.loads(out);assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE and pr['headRefName']==branch.strip()
_,branches=capture('new-branch-absent-v1','git','branch','--list',BRANCH);assert not branches.strip() and not PUBLIC.exists()
tracked=subprocess.check_output(['git','ls-files','-z']).decode('utf8').split('\0')
write(RUN/'baseline-v1.json',dict(base=BASE,origin_main=main.strip(),rows=rows(ROOT/p for p in tracked if p),parent_PR=pr,stacked=True))
capture('create-stacked-branch-v1','git','switch','-c',BRANCH,BASE)
write(RUN/'native-scoped.py',(ROOT/'runs/online-ch2-prescient-cumulative-20261009/native-scoped.py').read_bytes())
fixed()
from pypdf import PdfReader
reader=PdfReader(str(PDF))
for n in [26,28,29,75,76,277,278]:write(RUN/('source-pdf%d.txt'%n),reader.pages[n-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',author='Francesco Orabona',url='https://arxiv.org/pdf/1912.13213v10',version='v10',version_date='2026-06-21',pdf=PDF.as_posix(),pdf_sha256=sha(PDF),pages=rows(RUN/('source-pdf%d.txt'%n) for n in [26,28,29,75,76,277,278]),anchors=['Chapter2 prescient forward dependency printed14/PDF26','Definitions2.16/2.18/2.20 printed16/PDF28','Definition6.4 printed63/PDF75','Algorithm15.8/Theorem15.30 printed265-266/PDF277-278 including mandatory fixed-step statement'],scope='Source hypothesis transport and conditional actual source-update identification; no universal attainment or Chapter15 acceptance.'))
for name in ['--help','lifecycle-event','trial-log','conversion-window','statement-fence','frontier-shadow','safe-verify','list-lean-decls']:
    capture('CLI-help-'+name.replace('--','')+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py',name,*([] if name=='--help' else ['--help']))
capture('own-shadow-initial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow')
write(RUN/'audit-inspected-v1.json',dict(actual_stacked_base=BASE,origin_main=main.strip(),ancestor_actual_exit=code,parent_PR=pr,shared_packages=str((ROOT/'.lake/packages').resolve()),shared_git='E:/ABRL/research/.git',baseline_tracked_files=len(load(RUN/'baseline-v1.json')['rows']),source_pdf_sha256=sha(PDF),old_PR212_source_or_Lean_unchanged=True,whole_Goal_status='ACTIVE',chapter_complete=False,source_container_closed=False))
write(RUN/'00_context.md', '# Source-loss and actual source-update transport\n\nPersistent Orabona Chapters1-16 Goal ACTIVE. Chapter2 partial/null; all eight source forward containers remain required/open. Current package stacks on OPEN draft unmerged PR212 exact '+BASE+'. Reuses accepted conditional cumulative module from that PR, same project/toolchain/registry. No canonical-main edit, merge/deploy/retirement or new per-Book library.\n\nDraft intent: derive properness from nonempty finite feasible domain and globally no-bottom source loss; prove strict convexity and uniqueness of the actual penalized objective; identify every given valid source argmin trajectory with the existing current-loss Option recursion, rather than assume hseq. Transport fixed/variable source bounds through that actual identification. Source generator represented on X by an ambient representative, closedness via canonical real-coercion plus extendedIndicator, with interior derivatives licensed explicitly. No closed/strict-to-universal-attainment inference; prior exponential nonattainment canary prevents it. Exact semantic/source-obligation review must distinguish source conditional valid-run theorem from any historical overbroad unconditional obligation wording before any closure classification.\n\nRoot acts director/architect/formalizer/worker in separated phases, one lower route. Reuse distinct semantic actors under required local roundtrip; requested Astra/medium, no human/external/absolute-blind/runtime attestation. Draft is not stabilized, proved, compiled or source-accepted. Proofs only after exact headers/context/type-probe/neutral reconstruction/source review/fences/native conversion window.\n')
fixed()
print('Fresh stacked source audit complete; draft targets/source classification still pending.')
