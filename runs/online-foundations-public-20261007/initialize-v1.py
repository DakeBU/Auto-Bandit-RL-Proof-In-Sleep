from common_v1 import *
import datetime
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()==BASE_BRANCH
assert all(s.startswith('?? '+RUN.relative_to(ROOT).as_posix()+'/') for s in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).splitlines())
gate('fresh-fetch-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','fetch','origin')
canonical='E:/ABRL/research'
assert not subprocess.check_output(['git','-C',canonical,'status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','-C',canonical,'rev-parse','HEAD'],text=True).strip()
assert main==subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip()
raw=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/186']);write(RUN/'base-PR186-fresh-v1.json',raw)
parent=json.loads(raw);assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
write(RUN/'historical-PR117-fresh-v1.json',subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/117']))
assert not subprocess.check_output(['git','branch','--list',BRANCH],text=True).strip()
subprocess.run(['git','switch','-c',BRANCH,BASE],check=True)
write(RUN/'canonical-worktree-audit-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical=canonical,canonical_main=main,origin_main=main,canonical_clean=True,branch=BRANCH,exact_stacked_PR=186,exact_stacked_head=BASE,parent_state='OPEN-DRAFT-unmerged',prior_DIRECT=dict(head=BASE,raw_files=450,clean=True,local_remote_REST_equal=True,source='Immediately preceding actual terminal DIRECT output'),shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),shared_links_preserved=True,main_live_unchanged=True))
frozen=[PUBLIC.as_posix(),'Tests/OnlineLearningChapterOneCanary.lean','BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json','runs/online-unit-scaling-public-20261007/accepted-decision-v1.json','runs/online-unit-scaling-public-20261007/delivery-obligations-overlay-v1.json']
frozen.extend(p.as_posix() for p in sorted(Path('BanditRLProof').glob('OnlineLearning*.lean')) if p.as_posix() not in frozen)
frozen.extend(p.as_posix() for p in sorted(Path('docs/contracts/online-book-v1').glob('*')) if p.is_file() and p.as_posix() not in frozen)
snap=[]
for p in frozen+['MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl']:
 dest=RUN/'snapshots'/(p.replace('/','--')+'.raw');write(dest,Path(p).read_bytes());snap.append(dict(original_path=p,snapshot=dest.as_posix(),sha256=sha(dest)))
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
text=PUBLIC.read_text(encoding='utf-8');m=re.search(r'(?m)^theorem lemma_1_2\b[\s\S]*?(?= := by\b)',text);assert m
header=m.group(0).strip();nativeheader=lean_declaration_header(PUBLIC,'lemma_1_2');nh=hashlib.sha256(nativeheader.encode()).hexdigest()
assert nh==load('docs/contracts/online-book-v1/lemma_1_2-v2.json')['statement_hash']
assert len(re.findall(r'(?m)^theorem ',text))==1 and not re.search(r'(?m)^(?:noncomputable )?(def|abbrev) ',text)
write(CONTRACT/'header-v1.txt',header);write(CONTRACT/'context-v1.txt',text[:m.start()]);write(CONTRACT/'native-header-v1.txt',nativeheader)
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files={p:sha(p) for p in frozen},snapshots=snap,raw_header_hash=hashlib.sha256(header.encode()).hexdigest(),native_header_hash=nh,existing_public_proofs=1,existing_public_definitions=0,new_public_math=0,new_source_math_closures=0,new_named_canary_tests_planned=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
assert sha(PDF)==PDF_SHA
from pypdf import PdfReader
r=PdfReader(PDF)
for page in range(13,20):write(RUN/f'source-pdf{page}-v1.txt',r.pages[page-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,2026-06-21',url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=PDF.as_posix(),SHA256=sha(PDF),anchor='Lemma1.2 Be-the-Leader, printed4/PDF16',review_context_pages='Chapter1 maintext printed1-6/PDF13-18; history/exercises printed7/PDF19 separate',delta='Source V subset real Euclidean space; existing theorem generalizes to arbitrary ambient type X since only evaluations, finite sums and order are used. Positive-prefix minimizers assumed, not constructed. Zero horizon extension vacuous.',historical_mathematics_preexists=True,current_package_new_public_math=0))
write(RUN/'00_context.md',f'''# Current Chapter1 Lemma1.2 package
Persistent Chapters1-16 Goal ACTIVE/unbudgeted, requested GPT-6 Astra/medium. Fresh canonical main/origin {main} clean; exact OPEN draft PR186 base {BASE}. Previous actual DIRECT450 ownrawfiles, clean/localremoteREST equality passed. Same shared Lean/Lake/registry; Git stores/.lake/website links/all other worktrees preserved. New branch {BRANCH}; historical public proof and Chapter1 canary bytes immutable.
Existing single public Be-the-Leader lemma, ZERO new public/source mathematical closures. Source-positive prefix argmin and membership, auxiliary hindsight leaders, no causal algorithm existence or performance premise. Arbitrary ambient-type generalization and T0 extension explicitly reviewed. Current named tests will produce nondegenerate Bool prefix argmins, strict comparison -2<0, zero/one horizons, and a concrete failure without prefix optimality. Tests are validation declarations, not new book results or duplicate public wrappers.
Use actual native help/schema, source/exact statement/signature/DAG/conversion freeze, distinct mandatory blind decoder and anti-anchored CONTRACT, one ready existing-body/test route, BODY/kernel/guards/directVALUE/axiom audits, combined root/Tests/harness, exactbase and main-relative contributor distinctions, own shadow, sharedregistry/current source reader/site/pixels, distinct FINAL/nativeaccepted/actual draftdelivery. The paper's conventions are not all enforced by one runtime. No independent human/external/model-runtime attestation. Global SGB frontier unchanged.
Nine Chapter1 modules initially need current contributor/semantic migration including this module; eight OTHER modules remain mandatory after this bounded reuse. Chapter1 completion not inherited from stale historic accepted-local coverage. Chapter2 mandatory total null/incomplete; Chapters3-16 unenumerated; appendices required. No merge/deploy/main/live/retirement or wholeGoal completion.
''')
write(RUN/'paper-boundary-v1.json',dict(title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',path='E:/ABRL/papers/long/main/harness.tex',sha256=sha('E:/ABRL/papers/long/main/harness.tex'),private_manuscript_not_copied=True))
for cmd in [None,'new-task','lifecycle-event','trial-log','statement-fence','safe-verify','frontier-refresh','frontier-shadow','memory-record','retrieval-record']:
 native('help-'+(cmd or 'root')+'-v1',*([cmd] if cmd else []),'--help')
native('new-task-v1','new-task',TASK,'--kind','theorem','--title','Chapter1 Be-the-Leader current source and named canary audit','--target-lean',PRE+'lemma_1_2')
native('draft-event-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,existing_public_proofs=1,new_public_math=0,exact_stacked_base=BASE,chapter_complete=False,goal_complete=False)))
fixed();print('Fresh parent/source/single complete target frozen; current contract and tests pending.')
