"""Fresh exact-base/source/worktree audit and immutable existing policy targets."""
from common_v1 import *
import datetime
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-osd-migration'
dirty=subprocess.check_output(['git','status','--porcelain'],text=True).splitlines()
assert all(s.startswith('?? runs/online-osd-policy-public-20261007/') for s in dirty),dirty
gate('fresh-main-fetch-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','fetch','origin','refs/heads/main:refs/remotes/origin/main')
canonical='E:/ABRL/research'
assert not subprocess.check_output(['git','-C',canonical,'status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','-C',canonical,'rev-parse','HEAD'],text=True).strip()
remote_main=subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip();assert main==remote_main
parent_raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/179']);write(RUN/'base-PR179-fresh-v1.json',parent_raw)
parent=json.loads(parent_raw);assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
old_raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/149']);write(RUN/'historical-PR149-fresh-v1.json',old_raw)
branch='codex/research-online-osd-policy-migration';assert not subprocess.check_output(['git','branch','--list',branch],text=True).strip()
subprocess.run(['git','switch','-c',branch,BASE],check=True)
write(RUN/'canonical-worktree-audit-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical=canonical,canonical_main=main,origin_main=remote_main,canonical_clean=True,exact_stacked_PR=179,exact_stacked_head=BASE,parent='OPEN-DRAFT-unmerged',branch=branch,shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),prior_actual_DIRECT=dict(head=BASE,clean=True,local_remote_REST_equal=True,own_raw_files=673,PR=179),shared_links_preserved=True,other_worktrees_not_edited=True,main_live_unchanged=True))
frozen=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof/OnlineSubgradientDescent.lean','Tests/OnlineSubgradientDescentCanary.lean','BanditRLProof/OnlineGuessingSubgradient.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean','BanditRLProof/OnlineLipschitzSubgradient.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-OSD-POLICY-20261004.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
for d in ['online-osd-policy-v1','online-osd-public-v1']:
 frozen.extend(p.as_posix() for p in Path('docs/contracts',d).glob('*') if p.is_file())
refs=['runs/online-osd-policy-20261004/accepted-decision.json','runs/online-osd-policy-20261004/delivery.json','runs/online-osd-policy-20261004/accepted-binding-audit.json','runs/online-osd-policy-20261004/source-contract-review-v3.md','runs/online-osd-policy-20261004/source-contract-receipt-v3.json','runs/online-osd-policy-20261004/public-body-review-v2.md','runs/online-osd-policy-20261004/public-body-receipt-v2.json','runs/online-osd-policy-20261004/final-reader-review-v2.md','runs/online-osd-policy-20261004/final-reader-receipt-v2.json','runs/online-osd-public-20261007/accepted-decision-v1.json','runs/online-osd-public-20261007/delivery-obligations-overlay-v1.json','runs/online-osd-public-20261007/native-metadata-repair-receipt-v1.json','runs/online-osd-public-20261007/native-metadata-repair-review-v1.md']
assert all(Path(p).is_file() for p in frozen+refs)
snap=[]
for p in frozen:
 dest=RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());snap.append(dict(original_path=p,snapshot=dest.as_posix(),sha256=sha(dest)))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
text=PUBLIC.read_text(encoding='utf-8')
headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by)',text)};assert len(headers)==21
native_headers={n:hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest() for n in headers}
for n,h in headers.items():assert ' '.join(h.split())==lean_declaration_header(PUBLIC,n)
raw_headers={n:hashlib.sha256(h.encode()).hexdigest() for n,h in headers.items()}
write(CONTRACT/'headers-v1.json',headers);write(CONTRACT/'raw-statement-fingerprints-v1.json',raw_headers);write(CONTRACT/'native-statement-fingerprints-v1.json',native_headers)
context=text.split('\ntheorem history_zero',1)[0];assert context.count('\ndef ')==7 and context.count('\nabbrev ')==2
write(CONTRACT/'actual-context-v1.txt',context)
counts=dict(retained_public_proofs=21,retained_public_definitions=7,retained_public_abbreviations=2,retained_canary_proofs=74,retained_canary_definitions=11,retained_canary_abbreviations=7,new_public_proofs=0,new_definitions=0,new_canary_proofs=0)
for path,c in [(PUBLIC,(21,7,2)),(CANARY,(74,11,7))]:
 t=path.read_text(encoding='utf-8');assert tuple(len(re.findall(r'(?m)^'+k+r'\s+',t)) for k in ['theorem','def','abbrev'])==c
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files={p:sha(p) for p in frozen+refs},before_snapshots=snap,raw_headers=raw_headers,native_headers=native_headers,proof_bodies_preexist_current_draft=True,source_package_accepted=False,chapter_complete=False,goal_complete=False,**counts))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
reader=PdfReader(pdf)
for page in [25,26,27,28,31,32,33]:write(RUN/f'source-pdf{page}-v1.txt',reader.pages[page-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(source='Orabona arXiv1912.13213v10,21June2026',PDF_url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),SHA256=sha(pdf),anchors=['Definition2.18/2.20 printed16/PDF28','Lemma2.31 and explicit Theorem2.13/eq2.1 transfer printed19/PDF31','Algorithm2.2 printed20/PDF32','Fixed coarse formula printed21/PDF33','Gradient guarantee reference printed13-15/PDF25-27'],scope='Actual exogenous deterministic finite-history played-legal support policy family, same actual projection recursion and sharp fixed/variable/tuned bounds; canonical identity adapters. Existing historical PR149 accepted proof package, current source/public migration evidence required.',historical_PR149_state=json.loads(old_raw)['state'],new_math=False,remaining='Example2.32/linearization/unitanalysis/remaining Chapter1/2/nine OTHERChapter1 main-relative contracts/necessary appendices REQUIRED; Chapter2 total incomplete;3-16 unenumerated; whole Goal ACTIVE.'))
write(RUN/'dependency-references-v1.json',dict(scope='Exact accepted historical PR149 evidence and current delivered PR179 canonical substrate only; not recursive older-history reacceptance',rows=[dict(path=p,sha256=sha(p)) for p in refs]))
write(RUN/'00_context.md','Whole Chapters1-16 Goal ACTIVE unbudgeted; requested GPT6Astra/medium, not runtime-attested. Current canonical main/origin '+main+' clean after actual fresh fetch. Exact OPENdraft unmerged PR179 '+BASE+' and prior DIRECT clean/localremoteREST/all673 ownraw files PASS. Existing historical PR149 accepted-local policy bodies/21proofs7defs2abbr and full74canaryproofs11defs7abbr stay byte-frozen. This bounded source/public migration audit adds ZERO proofs/definitions; do not call the old source-inventory candidate snapshot a new mathematical obstruction or count this as newly proved performance. Same shared Lean/Lake registry; only task-owned files and online-osd-policy reader route may change after source stabilization/body gates. Old raw evidence/targets/otherBooks/SGB/pins/sharedlinks/ignoredruntime retained. No merge/deploy/main/live/retirement or chapter/Goal completion.')
fixed();print('Draft21 exact policy terminals/full74canaries frozen; independent current semantic/body/integrated gates pending.')
