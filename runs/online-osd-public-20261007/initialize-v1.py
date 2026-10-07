"""Audit exact delivered parent before freezing the existing OSD producer chain."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,datetime
RUN=Path(__file__).resolve().parent;ROOT=RUN.parents[1];assert Path('.').resolve()==ROOT
BASE='2ee95f4c340266847ae577a8e018f5bbf55451b9';TASK='ONLINE-OSD-PUBLIC-20261007'
CONTRACT=Path('docs/contracts/online-osd-public-v1');PUBLIC=Path('BanditRLProof/OnlineSubgradientDescent.lean');CANARY=Path('Tests/OnlineSubgradientDescentCanary.lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),label,*map(str,args)],check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-convex-uncountability'
dirty=subprocess.check_output(['git','status','--porcelain'],text=True).splitlines()
assert all(line.startswith('?? runs/online-osd-public-20261007/') for line in dirty),dirty
gate('fresh-fetch-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','fetch','origin')
canonical='E:/ABRL/research'
assert not subprocess.check_output(['git','-C',canonical,'status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','-C',canonical,'rev-parse','HEAD'],text=True).strip();remote_main=subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip();assert main==remote_main
raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/178']);write(RUN/'base-PR178-fresh-v1.json',raw);parent=json.loads(raw)
assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
branch='codex/research-online-osd-migration';assert not subprocess.check_output(['git','branch','--list',branch],text=True).strip()
subprocess.run(['git','switch','-c',branch,BASE],check=True)
audit=dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical_path=canonical,canonical_main=main,origin_main=remote_main,canonical_clean=True,exact_parent_PR=178,exact_parent_head=BASE,parent_state='OPEN-DRAFT-unmerged',branch=branch,shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),shared_lake_packages_junction='E:/ABRL/research/.lake/packages',website_hub_junction='E:/ABRL/research/website',prior_DIRECT_audit=dict(head=BASE,clean=True,local_remote_REST_equal=True,raw_files=391,PR='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/178'),main_updated=False,live_updated=False,worktree_retained=True)
write(RUN/'canonical-worktree-audit-v1.json',audit)
frozen=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
for d in ['online-osd-v1','online-osd-v2','online-osd-v3','online-osd-causality-v1','online-osd-performance-v1']:frozen.extend(p.as_posix() for p in Path('docs/contracts',d).glob('*') if p.is_file())
snap=[]
for p in frozen:
 dest=RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());snap.append(dict(original_path=p,snapshot=dest.as_posix(),sha256=sha(dest)))
headers={n:m.strip() for n,m in [(x.group(1),x.group(0)) for x in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= :=)',PUBLIC.read_text(encoding='utf-8'))]};assert len(headers)==15
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native={n:hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest() for n in headers};rawhash={n:hashlib.sha256(t.encode()).hexdigest() for n,t in headers.items()}
write(CONTRACT/'headers.json',headers);write(CONTRACT/'raw-statement-fingerprints-v1.json',rawhash);write(CONTRACT/'native-statement-fingerprints-v1.json',native)
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
reader=PdfReader(pdf)
for page in [25,26,27,28,31,32,33]:write(RUN/f'source-pdf{page}-v1.txt',reader.pages[page-1].extract_text())
context=Path('docs/contracts/online-osd-causality-v1/context.txt').read_bytes();write(CONTRACT/'actual-context-v1.txt',context)
write(CONTRACT/'source-card.json',dict(source='Orabona arXiv1912.13213v10 21June2026',PDF_url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),sha256=sha(pdf),anchors=['Definition2.20 inherited proper-function/global-support meaning printed16/PDF28','Lemma2.31 printed19/PDF31','Algorithm2.2 printed20/PDF32','Unnumbered OGD-to-OSD Theorem2.13/eq2.1 transfer printed19/PDF31; coarse fixed formula printed21/PDF33'],scope='Exact arbitrary-current supplied-support lemma and one permitted current-function/current-point canonical OSD recurrence with its same-run fixed/variable/tuned guarantees.',remaining='Generic deterministic legal finite-history policy family separately REQUIRED; Example2.32/linearization/unitanalysis/remaining Chapter1/2/nine OTHERChapter1 gaps/necessary appendices mandatory, total Goal ACTIVE.'))
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files={p:sha(p) for p in frozen},before_snapshots=snap,raw_headers=rawhash,native_headers=native,retained_public_proofs=15,retained_public_definitions=5,retained_public_abbreviations=1,retained_canary_proofs=24,retained_canary_definitions=7,retained_canary_abbreviations=1,new_proofs=0,new_definitions=0,reuse_decision='reuse_existing',compiled_current_focused=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory'
write(RUN/'paper-boundary-v1.json',dict(title=title,authoritative_local_path='E:/ABRL/papers/long/main/harness.tex',SHA256=sha('E:/ABRL/papers/long/main/harness.tex'),private_manuscript_copied=False,single_runtime_does_not_enforce_all_source_role_file_conventions=True))
write(RUN/'00_context.md','Whole Chapters1-16 Goal ACTIVE unbudgeted, requested GPT6Astra medium, no runtime attestation. Exact delivered OPENdraft unmerged PR178 '+BASE+'; actual DIRECT clean/localremoteREST/all391 own raw files verified before this new run. Fresh fetch/canonical clean/main/origin '+main+', shared stores/worktrees/links preserved. Existing OSD public producer chain retained,15 proofs/5 definitions/1 abbreviation; existing24 canary proofs/7 definitions/1 abbreviation. Draft is actual source/semantic/public integration audit, not new theorem-count productivity. Old contracts, rejected versions, source proofs and SGB remain frozen. No merge/deploy/main/live/retirement or chapter/Goal completion.')
print('Existing15-public-proof OSD chain frozen as draft; actual types/retrieval/neutral/source reviews and focused body gates remain.')
