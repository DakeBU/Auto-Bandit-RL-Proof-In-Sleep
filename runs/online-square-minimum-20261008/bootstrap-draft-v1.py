from common_v1 import *
assert sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()
assert all(RUN.relative_to(ROOT).as_posix() in x for x in dirty),dirty
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/192']))
assert pr['head']['sha']==BASE and pr['state']=='open' and pr['draft'] and not pr['merged']
write(RUN/'stacked-base-PR192-v1.json',dict(PR=pr['html_url'],state='OPEN-DRAFT-unmerged',exact_head=BASE,canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc',no_main_update=True))
fixed_files=['BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningFTL.lean',
 'BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningRegret.lean',
 'BanditRLProof/OnlineLearningAsymptotic.lean','BanditRLProof/OnlineNoRegretSemantics.lean',
 'BanditRLProof/OnlineLearningHistory.lean','BanditRLProof/OnlineLearningIID.lean',
 'BanditRLProof/OnlineLearningInformation.lean','BanditRLProof/OnlineLearningStochastic.lean',
 'lean-toolchain','lakefile.lean','lake-manifest.json',
 'docs/contracts/online-book-v1/source-inventory.json','research-wiki/papers/sgb-theorem2-interface-frontier-trace.json']
mutable=['BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
 'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
for p in fixed_files+mutable:write(RUN/'snapshots'/(p.replace('/','--')+'.raw'),Path(p).read_bytes())
write(RUN/'draft-baseline-v1.json',dict(base=BASE,fixed_files={p:sha(p) for p in fixed_files},
    mutable_original_files={p:sha(p) for p in mutable},PDF_sha256=PDF_SHA,chapter_complete=False,goal_complete=False))
for page,origin in [(14,'online-regret-domains-20261007'),(15,'online-ftl-state-20261007'),(16,'online-ftl-state-20261007')]:
    for extension in ['txt','png']:
        src=Path('runs')/origin/f'source-pdf{page}-v1.{extension}'
        if src.exists():write(RUN/src.name,src.read_bytes())
write(RUN/'00_context.md','''Persistent whole-book Chapters1-16 Goal ACTIVE and unbudgeted; requested GPT-6 Astra/medium, no escalation/runtime attestation. Previous bounded C1-NOREGRET package delivered OPENdraft/unmergedPR192, exact2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3, actual DIRECT661 raw files/localremoteRESTequal/clean. Same shared Lean/Lake worktree E:/ABRL/worktrees/research-online-book, branchcodex/research-online-benchmarks; canonicalmain clean6847b678a73db68dee5101d6f05c2453c1405afc. Stores/runtime links/other checkouts retained; no main/merge/live update.

Current bounded dependency: printedp2/PDF14 actual squared best-fixed regret uses a minimum over[0,1]; printedp3/PDF15 empirical mean actually attains it. Produce the real sInf minimum from existing feasibility/minimization, including explicit empty-prefix library convention, then identify literal best regret with SAME shared comparatorRegret. Rebind actual causal meanPredict theorem1.3 and sharp initial/tail guarantee to this literal produced minimum. No generic minimizer assumed; no supplied future best comparator or regret certificate. Arbitrary supplied prediction identity is algebra/library generalization, not generic causal algorithm existence; actual mean predictor performance endpoints retain initial1/2 and strict past. Signed regret may be negative. Six derived producer/representation statements/adapters do not mean six printed source theorems.

Remaining IID expected-loss minimum and causal cumulative variance benchmark printedp1-2/PDF13-14 are REQUIRED next dependent work, not excluded or inferred from the empirical pathwise minimum. Expectation of hindsight minimum and minimum of expected fixed loss are different objects; no interchange. Five other main-relative module source audits remain required/unwaived,16C1sourceitems/proof totalnull,Chapter1open/Chapter2incomplete/3-16unenumerated/appendicesrequired/GoalACTIVE. Do not claim chapter completion from this package. One lower route, staged root director/architect/worker; distinct mandatory reusedblind/sourceReviewer only, prior staged history disclosed, no human/external review or single runtime-method-enforcement claim.
''')
write(RUN/'10_director.md','Dependency-ready first terminal is actual empirical mean feasibility/minimization at every finite prefix, T0 separately handled. Close sInf minimum before best-regret equality; then actual fixed-comparator order and two actual causal FTL performance endpoints. Only scoped scalar square-loss source hinge can advance; mandatory stochastic benchmark/information and five older main-relative modules remain open. No alternate chapter or proof-tree project.')
write(RUN/'20_architect.md','Single route: empiricalMean_mem + empiricalMean_minimizes (positiveT), T0 finite sum/defaultmean; IsLeast image witness + IsLeast.csInf_eq; literal minimum definition plus actual shared comparatorRegret; two FTL producer proofs reused exactly with same prefix and initial1/2. Search/compile APIs before source stabilization, freeze six raw headers and neutral context, distinct decoder/source review before theorem bodies. Intended own public module/root and canary/Test root; no old math edits, no dependency/toolchain changes. Mathlib csInf adapter generic already exists, do not duplicate it.')
write(RUN/'memory_digest.md','Draft only: six proposed square minimum/representation/causal performance targets. No body proof, no compiled target, no source acceptance or chapter/Goal closure yet. IID expected minimum/causal benchmark and old five module audits remain required.')
write(RUN/'retrieval_index.md','Draft sourcep2-5/PDF14-17. Existing empiricalMean_mem/minimizes, theorem_1_3, meanPredict_regret_refined, comparatorRegret and lemma_1_2; Mathlib IsLeast.csInf_eq/csInf_le/le_csInf. Actual native retrieval and compiled scratch checks pending; never treat declaration presence as source acceptance.')
native('new-task-v1','new-task',TASK,'--kind','lean','--title','Produce squared-loss hindsight minimum and actual FTL best regret','--target-lean','BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret')
native('draft-lifecycle-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,root_goal='Persistent Orabona Chapters1-16',scope='Actual squared interval minimum and same regret',exact_base_PR=192,exact_base_head=BASE,chapter_complete=False,goal_complete=False)))
fixed();print('Actual native draft created; source/contract/type audit next, no proof acceptance.')
