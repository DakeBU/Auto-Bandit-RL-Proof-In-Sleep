"""Fresh exact-parent/source/worktree audit and truthful draft registration."""
from common_v1 import *
import datetime
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-linearization-migration'
dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).splitlines();assert all(s.startswith('?? '+RUN.relative_to(ROOT).as_posix()+'/') for s in dirty),dirty
gate('fresh-fetch-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','fetch','origin')
canonical='E:/ABRL/research';assert not subprocess.check_output(['git','-C',canonical,'status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','-C',canonical,'rev-parse','HEAD'],text=True).strip();assert main==subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip()
raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/184']);write(RUN/'base-PR184-fresh-v1.json',raw);parent=json.loads(raw)
assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
old_raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/151']);write(RUN/'historical-PR151-fresh-v1.json',old_raw)
assert not subprocess.check_output(['git','branch','--list',BRANCH],text=True).strip()
subprocess.run(['git','switch','-c',BRANCH,BASE],check=True)
write(RUN/'canonical-worktree-audit-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical=canonical,canonical_main=main,origin_main=main,canonical_clean=True,worktree=ROOT.as_posix(),branch=BRANCH,stacked_PR=184,stacked_head=BASE,parent_state='OPEN-DRAFT-unmerged',previous_DIRECT=dict(head=BASE,clean=True,local_remote_REST_equal=True,raw_files=454,source='Immediately preceding actual terminal DIRECT audit; no file write.'),shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),old_branch_retained='codex/research-online-optimal-step historical PR151; not overwritten',main_live_unchanged=True,other_worktrees_untouched=True))
frozen=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineSubgradientPolicy.lean','BanditRLProof/OnlineLinearization.lean','Tests/OnlineLinearizationCanary.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-OPTIMAL-STEP-20261004.json','runs/online-optimal-step-20261004/accepted-decision.json','runs/online-optimal-step-20261004/pr-delivery.json','runs/online-linearization-public-20261007/accepted-decision-v1.json','runs/online-linearization-public-20261007/delivery-obligations-overlay-v1.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
frozen.extend(p.as_posix() for p in sorted(Path('docs/contracts/online-optimal-step-v1').glob('*')) if p.is_file())
snap=[]
for p in frozen+['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl']:
 dest=RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes());snap.append(dict(original_path=p,snapshot=dest.as_posix(),sha256=sha(dest)))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
t=PUBLIC.read_text(encoding='utf-8');headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by\b)',t)};assert len(headers)==11
rawhash={n:hashlib.sha256(h.encode()).hexdigest() for n,h in headers.items()};nativehash={n:hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest() for n in headers}
write(CONTRACT/'headers-v1.json',headers);write(CONTRACT/'raw-statement-fingerprints-v1.json',rawhash);write(CONTRACT/'native-statement-fingerprints-v1.json',nativehash)
for n in headers:assert nativehash[n]==load(Path('docs/contracts/online-optimal-step-v1')/(n+'.json'))['statement_hash'],n
write(CONTRACT/'actual-context-v1.txt',t[:t.index('theorem gap_identity')])
counts={}
for label,p in [('public',PUBLIC),('canary',CANARY)]:
 s=p.read_text(encoding='utf-8');counts[label]={k:len(re.findall(r'(?m)^(?:noncomputable )?'+k+r'\s+',s)) for k in ['theorem','def','abbrev']}
assert counts=={'public':{'theorem':11,'def':2,'abbrev':0},'canary':{'theorem':23,'def':4,'abbrev':1}},counts
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files={p:sha(p) for p in frozen},before_snapshots=snap,raw_headers=rawhash,native_headers=nativehash,counts=counts,named_checks=41,proof_bodies_preexist_current_draft=True,new_proofs=0,new_definitions=0,new_source_math_obligation_closures=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
reader=PdfReader(pdf)
for page in [26,27,28]:write(RUN/f'source-pdf{page}-v1.txt',reader.pages[page-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv1912.13213v10,2026-06-21',PDF_url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),SHA256=sha(pdf),anchors=['Section2.1.2 unnumbered fixed-distance/energy scalar minimization printed15/PDF27','Same page future gradients depend on eta and unknown comparator-distance warning','Same page exogenous diameter/gradient/horizon loose-bound scalar tuning and equation(2.1)'],scope='Existing11 proofs/2 definitions; current source/public reuse only. Two unnumbered scalar calculations and library equality/degenerate refinements, not11 source results.',historical_PR151_state=json.loads(old_raw)['state'],new_mathematics=False))
write(RUN/'paper-boundary-v1.json',dict(title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',authoritative_local_path='E:/ABRL/papers/long/main/harness.tex',SHA256=sha('E:/ABRL/papers/long/main/harness.tex'),private_manuscript_copied=False,single_runtime_does_not_enforce_all_role_source_file_conventions=True))
write(RUN/'00_context.md',f'''# Existing fixed-coefficient step-size minimization current audit
Total Chapters1-16 Goal ACTIVE/unbudgeted; requested GPT-6 Astra/medium, runtime not independently attested. Exact delivered OPEN draft PR184 {BASE}; preceding actual DIRECT454 raw files/localremoteREST/clean PASS. Fresh canonical main/origin {main} clean. Shared Git/.lake/packages/website junction and all other worktrees retained. New branch {BRANCH}; historical PR151 branch retained.
Existing11 public proofs/2 definitions and whole23 canary proofs/4 definitions/1 abbreviation frozen byte-for-byte. ZERO new mathematics/definitions/source-terminal closures/registry nodes. Fixed nonnegative coefficients/positive step; positive attained unique argmin, one-zero strict improving alternatives, both-zero algebraic extension; real sqrt/division totalization is not an admissible optimizer. Actual same-loss projected OGD canary has eta-dependent energy, so scalar fixed-coefficient minimization is not future-informed learner or optimized regret across reruns. Existing sharp OGD terminal residual remains untouched, only coarser scalar expression optimized.
Source/exact types/retrieval -> required distinct neutral decoder/anti-anchored CONTRACT -> stabilized one lower existing-body route -> focused/41 named/11 full guards/actual VALUE/full canary -> combined root/Tests/full harness/own shadow/exact base/shared registry/clean local site/pixels -> distinct FINAL -> actual native accepted -> bounded draft PR. No optional agents. Old contracts/runs/root/Tests/pins/otherBooks/globalSGB immutable. CONTRACT/BODY reader hashes bind exact before-snapshots; FINAL separately binds current reader bytes. No escaping changes inferred from JSON serialized representations; inspect decoded strings first if an actual failure occurs.
Unit-analysis current migration, remaining Chapter1/2 maintext, nine OTHER Chapter1 origin/main contributor gaps and necessary appendices REQUIRED. Chapter2 total null/incomplete; Chapters3-16 unenumerated. No chapter/Goal/merge/deploy/main/live/retirement completion.
''')
for command in [None,'new-task','lifecycle-event','trial-log','statement-fence','safe-verify','frontier-refresh','frontier-shadow','memory-record','retrieval-record']:
 args=[] if command is None else [command];native('help-'+(command or 'root')+'-v1',*args,'--help')
native('new-task-v1','new-task',TASK,'--kind','theorem','--title','Frozen-coefficient step-size minimization current source/public audit','--target-lean',PRE+'source_argmin')
native('draft-event-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,new_proofs=0,new_definitions=0,exact_stacked_base=BASE,chapter_complete=False,goal_complete=False)))
fixed();print('Fresh exact parent/source and11 full existing targets frozen; actual draft, current source CONTRACT pending.')
