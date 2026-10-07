"""Audit the exact delivered parent and actual source, then create the bounded draft."""
from common_v1 import *
import datetime
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-guessing-osd-migration'
dirty=subprocess.check_output(['git','status','--porcelain'],text=True).splitlines();assert all(s.startswith('?? '+RUN.relative_to(ROOT).as_posix()+'/') for s in dirty),dirty
gate('fresh-fetch-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','fetch','origin')
canonical='E:/ABRL/research';assert not subprocess.check_output(['git','-C',canonical,'status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','-C',canonical,'rev-parse','HEAD'],text=True).strip();assert main==subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip()
raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/183']);write(RUN/'base-PR183-fresh-v1.json',raw);parent=json.loads(raw)
assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
old_raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/150']);write(RUN/'historical-PR150-fresh-v1.json',old_raw)
assert not subprocess.check_output(['git','branch','--list',BRANCH],text=True).strip()
subprocess.run(['git','switch','-c',BRANCH,BASE],check=True)
write(RUN/'canonical-worktree-audit-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical=canonical,canonical_main=main,origin_main=main,canonical_clean=True,worktree=ROOT.as_posix(),branch=BRANCH,stacked_PR=183,stacked_head=BASE,parent_state='OPEN-DRAFT-unmerged',previous_DIRECT=dict(head=BASE,clean=True,local_remote_REST_equal=True,raw_files=361,source='Immediately preceding actual terminal DIRECT audit; no file write.'),shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),old_branch_retained='codex/research-online-linearization historical PR150; not overwritten',main_live_unchanged=True,other_worktrees_untouched=True))
frozen=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','BanditRLProof/OnlineSubgradientPolicy.lean','BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineLearningRegret.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-LINEARIZATION-20261004.json','runs/online-linearization-20261004/accepted-decision.json','runs/online-linearization-20261004/pr-delivery.json','runs/online-guessing-public-20261007/accepted-decision-v1.json','runs/online-guessing-public-20261007/delivery-obligations-overlay-v1.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
frozen.extend(p.as_posix() for p in sorted(Path('docs/contracts/online-linearization-v1').glob('*')) if p.is_file())
snap=[]
for p in frozen+['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl']:
 dest=RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());snap.append(dict(original_path=p,snapshot=dest.as_posix(),sha256=sha(dest)))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
t=PUBLIC.read_text(encoding='utf-8');headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= :=)',t)};assert len(headers)==18
rawhash={n:hashlib.sha256(h.encode()).hexdigest() for n,h in headers.items()};nativehash={n:hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest() for n in headers}
write(CONTRACT/'headers-v1.json',headers);write(CONTRACT/'raw-statement-fingerprints-v1.json',rawhash);write(CONTRACT/'native-statement-fingerprints-v1.json',nativehash)
for n in headers:assert nativehash[n]==load(Path('docs/contracts/online-linearization-v1')/(n+'.json'))['statement_hash'],n
write(CONTRACT/'actual-context-v1.txt',t[:t.index('theorem outputHistory_last')])
counts={}
for label,p in [('public',PUBLIC),('canary',CANARY)]:
 s=p.read_text(encoding='utf-8');counts[label]={k:len(re.findall(r'(?m)^'+k+r'\s+',s)) for k in ['theorem','def','abbrev']}
assert counts=={'public':{'theorem':18,'def':9,'abbrev':3},'canary':{'theorem':25,'def':8,'abbrev':2}},counts
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files={p:sha(p) for p in frozen},before_snapshots=snap,raw_headers=rawhash,native_headers=nativehash,counts=counts,named_checks=65,proof_bodies_preexist_current_draft=True,new_proofs=0,new_definitions=0,new_source_math_obligation_closures=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
reader=PdfReader(pdf)
for page in [13,14,15,28,31,32,33,34]:write(RUN/f'source-pdf{page}-v1.txt',reader.pages[page-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv1912.13213v10,2026-06-21',PDF_url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),SHA256=sha(pdf),anchors=['Section2.3 unnumbered reduction printed22/PDF34','Algorithm2.2 and Lemma2.31 printed19/PDF31','Source global support/properness printed16/PDF28','Online protocol printed1-3/PDF13-15'],scope='Existing18 proofs/9defs/3abbreviations; current source/public reuse migration only, one unnumbered maintext reduction plus explicit library refinements.',historical_PR150_state=json.loads(old_raw)['state'],new_mathematics=False))
write(RUN/'paper-boundary-v1.json',dict(title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',authoritative_local_path='E:/ABRL/papers/long/main/harness.tex',SHA256=sha('E:/ABRL/papers/long/main/harness.tex'),private_manuscript_copied=False,single_runtime_does_not_enforce_all_role_source_file_conventions=True))
write(RUN/'00_context.md',f'''# Existing causal linearization current source/public audit
Total Chapters1-16 Goal ACTIVE/unbudgeted, freshly get_goal verified; requested GPT-6 Astra/medium, runtime not independently attested. Exact delivered OPEN draft PR183 {BASE}; immediately preceding DIRECT361 raw files/localremoteREST/clean PASS. Fresh canonical main/origin {main} clean. Shared Git/.lake/packages/website junction and other worktrees retained. New branch {BRANCH}; historical PR150 branch retained.
Existing18 public proofs/9 definitions/3 abbreviations and whole25canary proofs/8defs/2abbr remain byte-frozen. ZERO new mathematics/definitions/source-terminal closures/registry nodes. Current revalidation of same causal A/generated support run, ambient support gap, universal OLO transport and feasible canonical producer; no guarantee producer for arbitrary A, stochastic law or algorithm existence chosen from complete future losses.
Source/exact closed types/retrieval -> distinct required neutral decoder/anti-anchored CONTRACT -> stabilized one lower existing-body route -> focused/65named/18guards/actualVALUE/canary -> combined root/Tests/fullharness/own shadow/exactbase/sharedregistry/clean local site/pixels -> distinct FINAL -> native accepted -> scoped draftPR. No optional agents. Old contracts/runs/root/Tests/pins/otherBooks/globalSGB frozen. Avoid previous reader-hash ambiguity: immutable CONTRACT/BODY input manifests bind explicit before-reader snapshots rather than mutable live website JSON; FINAL separately binds actual current reader bytes.
Remaining optimal-step/unit-analysis current migration, Chapter1/2 maintext and nine OTHERChapter1 origin/main contracts, necessary appendices REQUIRED. Chapter2 total null/incomplete; Chapters3-16 unenumerated. No chapter/Goal/merge/deploy/main/live/retirement completion.
Readonly prelook mistakenly guessed old delivery.json; actual filename pr-delivery.json discovered before use. This was a preserved tool-level read failure, no source/proof/target mutation.
''')
for command in [None,'new-task','lifecycle-event','trial-log','statement-fence','safe-verify','frontier-refresh','frontier-shadow','memory-record','retrieval-record']:
 args=[] if command is None else [command];native('help-'+(command or 'root')+'-v1',*args,'--help')
native('new-task-v1','new-task',TASK,'--kind','theorem','--title','Causal convex-to-linear reduction current source/public reuse audit','--target-lean',PRE+'canonical_regret_comparison')
native('draft-event-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,new_proofs=0,new_definitions=0,exact_stacked_base=BASE,chapter_complete=False,goal_complete=False)))
fixed();print('Fresh exact parent/source and eighteen full existing targets frozen; current draft, source fidelity not yet reviewed.')
