from common_v1 import *
import re
from pypdf import PdfReader
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash

assert Path.cwd() == ROOT and sha(PDF) == PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip() == BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip() == BRANCH
assert not PUBLIC.exists() and not CANARY.exists()
prior = load(ROOT / 'tmp/online-kernel-causal-final-ready-v1.json')
assert prior['actual_final_head'] == BASE and prior['worktree_clean']
paths = ['lean-toolchain','lakefile.lean','lake-manifest.json', 'runs/active_frontier.json',
    'runs/lifecycle_memory.jsonl', 'BanditRLProof/OnlineLearningMean.lean',
    'BanditRLProof/OnlineLearningFTL.lean', 'BanditRLProof/OnlineLearningRegret.lean',
    'BanditRLProof/OnlineLearningAsymptotic.lean', 'BanditRLProof/OnlineSquareMinimum.lean',
    'BanditRLProof/OnlineNoRegretSemantics.lean', 'BanditRLProof/OnlineGuessingKernelCausal.lean',
    'docs/contracts/online-kernel-causal-v1/chapter-one-source-ledger-accepted-v1.json',
    'docs/contracts/online-book-v1/coverage.json', 'research-wiki/mathlib/theorem-cards.md']
write(RUN / 'baseline-v1.json', dict(base=BASE, basePR=200, canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc',
    rows=[dict(path=p,sha256=sha(ROOT/p)) for p in paths]))
write(RUN / '00_context.md', 'Whole Chapters1-16 Goal ACTIVE, unbudgeted. Requested GPT-6 Astra/medium; no runtime attestation. '
    'Clean reused Online worktree on codex/research-online-c1-source-reconcile stacked on OPEN draft unmerged PR200 exact71c73d727e0a19ed68751994c3b1319aa9c3d756. '
    'Canonical research main/origin main freshly fetched, clean6847b678a73db68dee5101d6f05c2453c1405afc; shared Git/packages and all other worktrees preserved. '
    'No merge/deploy/retirement/anonymous/private-paper edit. This bounded FTL limit hinge is derived mathematics attached to C1-REGRET/C1-NOREGRET/C1-SUCCESS and Theorem1.3, not five printed theorems. '
    'Original16 source objects/null unknown proof total and required chapters/appendices remain. Contract review precedes all new production bodies. '
    'One lower route; reused distinct decoder and source reviewer required by local skill, disclosed prior actor history. No experiment/absolute blindness/human review claim.')
reader = PdfReader(str(PDF))
for page in [14,16,18]:
    write(RUN / ('source-pdf%d-text-v1.txt' % page), reader.pages[page-1].extract_text())
write(CONTRACT / 'source-card-v1.json', dict(title='Online Learning: A Modern Introduction Using Convex Optimization',
    author='Francesco Orabona',url='https://arxiv.org/pdf/1912.13213v10',version='arXiv:1912.13213v10',date='2026-06-21',
    pdf_sha256=PDF_SHA,cache=PDF.resolve().as_posix(),anchors=[dict(printed_page=2,pdf_page=14),
        dict(printed_page=4,pdf_page=16),dict(printed_page=6,pdf_page=18)], root_reread_original=True,
    maintext_source_objects=['C1-REGRET','C1-NOREGRET','Theorem1.3','C1-SUCCESS'],new_printed_theorem_claim=0))
write(CONTRACT / 'source-intent-v1.md', 'Orabona v10 printed2/PDF14 first defines signed regret against the minimum fixed comparator in[0,1], then defines comparator-wise regret. '
    'The no-regret sentence displays an ordinary limit <=0. Printed4/PDF16 Theorem1.3 gives actual strict-past mean predictions with initial1/2 and best-fixed regret <=4+4lnT; printed6/PDF18 concludes sublinear growth. '
    'Existing upper-epsilon NoRegret and literal finite-real-limit LimitNoRegret remain distinct, existing headers/bodies untouched. The previously accepted abstract signed-unbounded-affine obstruction is not a bounded-square-loss FTL counterexample.\n\n'
    'Freeze five DERIVED hinge obligations: F1 actual meanPredict cumulative loss minus empirical-mean comparator loss is nonnegative for EVERY real observation stream and every naturalT including0, by prefix minimization and the actual strict-past prediction. '
    'F2 exact fixed-comparator decomposition for all realy,u andT including0: actual regret(u,T)=actual regret(empMean_T,T)-T*(u-empMean_T)^2. '
    'F3 for one infinite unit observation stream, the ACTUAL interval-minimum signed best regret divided byT tends to0, using F1 plus source4log upper; no regret lower/upper oracle is input. '
    'F4 for the SAME actual FTL and every real fixedu,a, ordinary normalized regret tends toa IFF (u-empMean_T)^2 tends to-a. '
    'F5 when the stream empirical mean tends tom, every real comparator limit is-(u-m)^2; restricting comparators to[0,1] produces literal LimitNoRegret. The extra empirical-mean convergence is an explicit sufficient condition; do not attribute it to the arbitrary-stream source theorem.\n\n'
    'No probability/expectation/high-probability/minE exchange/pathwise-best-regret nonnegativity for arbitrary algorithms. F1 uses a produced hindsight empirical mean, not a caller minimizer/stability premise. F1/F2 unbounded-stream statements do not claim valid unit game outputs for unbounded observations. '
    'F3/F4/F5 retain all-time unit observations. T0 normalization uses Lean total division by0=0 and is irrelevant to atTop; finite F2 includesT0 by empty sums. '
    'No unconditional ordinary limit for every arbitrary bounded stream is claimed. A concrete bounded oscillating-mean same-FTL counterexample and exact all-comparator converse remain separate required source-semantics reconciliation work, not silently excluded or declared false here. '
    'This package does not complete C1 or the whole Goal; original source obligations and subsequent chapters remain.')
context = 'import BanditRLProof.OnlineSquareMinimum\nimport BanditRLProof.OnlineNoRegretSemantics\n\nopen Filter\n\nnamespace BanditRL.OnlineLearning\n'
write(CONTRACT / 'context-v1.lean.txt', context + '\nend BanditRL.OnlineLearning\n')
text = (CONTRACT / 'targets-v1.lean.txt').read_text(encoding='utf8')
targets=[]
probe=context
for i,chunk in enumerate(text.split('theorem ')[1:],1):
    header='theorem '+chunk.strip()
    name=re.search(r'theorem\s+(\w+)',header).group(1)
    targets.append(dict(id='F'+str(i),name='BanditRL.OnlineLearning.'+name,header=header,
        statement_hash=statement_hash(header),phase='draft',compiled=False))
    args,goal=header.split(name,1)[1].split(' :\n',1)
    probe+='\n#check (∀ '+args.strip()+',\n'+goal+')\n'
assert len(targets)==5
write(CONTRACT / 'targets-v1.json',dict(version=1,targets=targets,source_sha256=PDF_SHA,
    context_sha256=sha(CONTRACT/'context-v1.lean.txt'),chapter_complete=False,goal_complete=False))
write(RUN / 'draft-typecheck-v1.lean',probe+'\nend BanditRL.OnlineLearning\n')
gate('draft-typecheck-v1','lake','env','lean',RUN/'draft-typecheck-v1.lean')
native('draft-help-search-v1','search-memory','--help')
native('draft-help-decls-v1','list-lean-decls','--help')
native('draft-search-mean-v1','search-memory','meanPredict')
native('draft-search-regret-v1','list-lean-decls','squaredBestRegret','--statement')
native('draft-search-limit-v1','list-lean-decls','LimitNoRegret','--statement')
gate('draft-local-absence-v1','rg','-n','meanPredict_bestLoss_nonneg|meanPredict_comparator_decomposition|meanPredict_fixedRegret_limit_iff','BanditRLProof',required=False)
native('draft-help-task-v1','new-task','--help')
native('draft-new-task-v1','new-task',TASK,'--kind','ftl-limit-hinge','--title','Actual FTL best regret and fixed-comparator ordinary-limit criterion','--target-lean',PUBLIC.relative_to(ROOT).as_posix())
write(CONTRACT / 'dependency-dag-v1.json',dict(nodes=[
    dict(id='F1',requires=['empiricalMean_minimizes','meanPredict'],ready=True),
    dict(id='F2',requires=['empiricalMean_decomposition'],ready=True),
    dict(id='F3',requires=['F1','squaredLoss_minimum_eq','meanPredict_bestRegret_bound','Real log/T vanishing'],ready=False),
    dict(id='F4',requires=['F2','F3','squaredBestRegret_eq_comparatorRegret','limit subtraction'],ready=False),
    dict(id='F5',requires=['F4','continuity of square','LimitNoRegret'],ready=False)],terminal='F4 exact same-process criterion; F5 conditional literal source-limit producer',single_lower_route=True))
write(CONTRACT / 'conversion-window-v1.md', 'Frozen v1 exact five headers and unchanged context/imports. Only theorem bodies/private proof helpers in new OnlineFTLLimitSemantics.lean after source-contract review. '
    'No edits to old definitions/proofs/source contracts. Canary exact headers need separate review before proof. Future stabilization may add root/Test imports, own contract/evidence, appended source cards/readers and new registry entries while retaining every old record and source obligation. '
    'GlobalSGB active_frontier/lifecycle memory immutable. Own task metadata append-only; own scoped attempt/frontier/lifecycle evidence. All tests/pins/source/source-meaning/header alterations require separately versioned repair review. No generated_site edits or merge/deploy.')
write(CONTRACT / 'semantic-signature-v1.json',dict(objects='real observation stream, same causal meanPredict initialized1/2, empiricalMean, signed fixed and interval-best regrets',
    quantifiers='F1/F2 forall real streams/u/naturalT; F3-5 forall one all-time unit stream; F4 forall realu,a; F5 assume empiricalMean converges then forall realu',
    metric='pathwise signed square-loss regret; ordinary finite-real atTop limit, distinct from eventual upper condition',
    information='existing exact strict-past source predictor, no future sequence optimization or target mean in algorithm',
    normalization='source roundt+1 isLeant; emptyT0 and totaldivision0 explicit; asymptoticatTop',probability='none',
    conclusion='F3 nonnegative best/T ->0; F4 fixed/T iff square distance ->-a; F5 sufficient empiricalMean convergence gives all-real fixed limits<=0',
    source_delta='five derived hinges, F5 extra convergence explicitly conditional; no unconditional literal-limit guarantee/Chapter1 closure'))
write(CONTRACT / 'canary-plan-v1.md', 'Freeze separate public-canary proposal before proving. One genuine binary periodic stream with both0and1 values, same causal meanPredict initial1/2, finiteT0/T1/T2, positive best-fixed regret and a strictly negative fixed-comparator normalized limit. '
    'Derive its empiricalMean convergence from actual binary counts; instantiate all five public endpoints, not merely quote a proposition or assume the needed regret bound. No supplied asymptotic regret oracle. Additional constant-stream boundary checks may supplement, not replace the binary case.')
for directory in ['tasks','proof-obligations','conversion-windows']:
    p=ROOT/directory/(TASK+'.md')
    write(RUN/('native-'+directory+'-template-v1.raw'),p.read_bytes())
    p.write_bytes(p.read_bytes()+ ('\n\n## Own draft five derived FTL limit obligations\n\n'+
        (CONTRACT/'source-intent-v1.md').read_text(encoding='utf8')+'\nExact frozen headers/DAG: docs/contracts/online-ftl-limit-v1. Contract review pending,0 production bodies compiled;5 derived obligations open.\n').encode('utf8'))
write(RUN/'10_director-v1.md','Bounded theorem-edge delta within Chapter1 source no-regret reconciliation. Same actualFTL lower bound + comparator identity -> best/T0 -> exact fixed ordinary-limit criterion. F5 explicit sufficient-condition source adapter. No chapter/wholeGoal closure, no next chapter writing.')
write(RUN/'11_architect-v1.md','One route. F1 induction onT: prefix-min lossPhi_(T+1) <= loss of old leader onT+1 =Phi_T +actualnextloss, using empiricalMean_minimizes and actualmeanPredict, with separateemptyT. F2 reuse exactdecomposition plusT0. F3 actualminimum identification +F1+4logupper squeeze. F4 divideF2 on positiveT and limit subtraction both directions. F5 continuitysquare andF4, thennegative-square bound. No new general arithmetic/asymptotic duplication. Pinnedmathlib limit API only; noLML/Optlib dependency change.')
write(RUN/'12_worker-v1.md','DRAFT exactpropositions elaborated via#check only. No new theorembody/public compiled proof. Dependency-readyF1 first after required independent source-contract audit; finiteleaf boundaries frozen. General-purpose lemma retrieval performed before proof.')
write(RUN/'memory_digest.md','DRAFT five derived actualFTL limit obligations open. Source/display ordinarylimit≠upperNoRegret; literalLimitNoRegret existing. Existing arbitrary-affine counterexample doesnotsettle bounded actualFTL. Search actuallocal mean/minimum/bounds, pinnedmathlibsqueeze/limit APIs; no proof terminal closed.')
write(RUN/'retrieval_index.md','Actual native search-memory meanPredict/list-lean-decls squaredBestRegret/LimitNoRegret statementlogs; existing APIs reused. rg absence exit1 is a query with nohits, not compilefailure/success. Exactmathlib theorem cards inspected (MLIB-ASYMPTOTICS). No unbuilt external repository fact accepted. Global retrieval indexes intentionally immutable; own index only until accepted integration.')
fixed()
print('DRAFT five exact headers/context typechecked; no production body.',flush=True)
