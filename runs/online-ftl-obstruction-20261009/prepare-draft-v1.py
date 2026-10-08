from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert not PUBLIC.exists() and not CANARY.exists() and not CONTRACT.exists()
prior=ROOT/'runs/online-ftl-limit-20261009'
ready=load(ROOT/'tmp/online-ftl-limit-final-ready-v1.json')
assert ready['actual_final_head']==BASE and ready['PR']==201 and ready['worktree_clean'] and not ready['merged']
paths=['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean',
    'BanditRLProof/OnlineFTLLimitSemantics.lean','Tests/OnlineFTLLimitSemanticsCanary.lean',
    'BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningFTL.lean',
    'BanditRLProof/OnlineLearningRegret.lean','BanditRLProof/OnlineLearningAsymptotic.lean',
    'BanditRLProof/OnlineNoRegretSemantics.lean','BanditRLProof/OnlineSquareMinimum.lean',
    'docs/contracts/online-ftl-limit-v1/chapter-one-source-ledger-accepted-v1.json',
    'runs/trials.jsonl','runs/lifecycle_memory.jsonl','proof-frontiers/active_frontier.json']
paths += [p.relative_to(ROOT).as_posix() for p in (ROOT/'research-wiki/retrieval-index').glob('*.json')]
baseline=[]
for i,rel in enumerate(paths):
    p=ROOT/rel
    if not p.exists():
        assert rel=='proof-frontiers/active_frontier.json';continue
    q=RUN/'baseline'/('input-'+str(i)+'-v1.raw');write(q,p.read_bytes())
    baseline.append(dict(path=rel,sha256=sha(p),snapshot=q.as_posix()))
write(RUN/'baseline-v1.json',dict(base=BASE,basePR=201,origin_main='6847b678a73db68dee5101d6f05c2453c1405afc',
    rows=baseline,shared_git='E:/ABRL/research/.git',shared_packages_preserved=True,chapter_complete=False,goal_complete=False))
write(RUN/'prior-delivery-v1.json',ready)
write(RUN/'00_context.md','Persistent Orabona Chapters1-16 Goal ACTIVE/unbudgeted; Astra/medium. Current required Chapter1 source reconciliation: actual unit-stream FTL ordinary-limit equivalence and concrete bounded binary oscillation obstruction. Stacked on OPENdraftunmerged PR201 exact'+BASE+'. No chapter/Goal/main/live completion. Reuse shared Lean project, canonical Git and pinned packages; no anonymous/private-paper/generated-site edits. Applicable hub/research AGENTS/README/lifecycle/paper requirements already read this logical turn; single lower route, mandatory distinct decoder/source reviewer. All prior failures/delivery evidence retained.')
for label,text in [('10_director-v1.md','Close the two REQUIRED actual-FTL ordinary-limit semantic gaps, not another arbitrary algorithm model. Freeze four derived terminals, keep source ordinary lim display separate from proposed correction. Prior F1-F5 actual producers are ready. Whole sixteen-source Chapter1 ledger stays open until reconciliation/chapter gates; no coverage percentage from unknown totals.'),
    ('11_architect-v1.md','D1 derives necessity from comparator0/1 squared-distance limits and sufficiency from the existing conditional same-process producer. D2 explicit well-founded binary dyadic stream. D3 exact prefix sums along4^(n+1)-1 and2*4^n-1, then two different empirical-mean limits. D4 same actual meanPredict: upper NoRegret and best/T0 coexist with no fixed-zero ordinary limit and no literal LimitNoRegret. No supplied mean/regret/independence oracle. Mathlib reused; one producer recursion.'),
    ('12_worker-v1.md','DRAFT only: inspect actual existing APIs and elaborate signatures/definition. First ready leaf D1 only after separate blind/source contract review. Freeze public and canary targets before theorem bodies. No target weakening, toolchain upgrade or new dependency.')]:write(RUN/label,text)
for page in [14,16,18]:
    for suffix in ['text-v1.txt','v1.png']:
        p=prior/('source-pdf'+str(page)+'-'+suffix)
        write(RUN/p.name,p.read_bytes())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',
    author='Francesco Orabona',version='arXiv:1912.13213v10',date='2026-06-21',url='https://arxiv.org/pdf/1912.13213v10',
    cached_pdf=PDF.resolve().as_posix(),sha256=PDF_SHA,anchors=[dict(printed=2,pdf=14,scope='Ordinary-limit no-regret display and signed fixed-comparator regret'),
    dict(printed=4,pdf=16,scope='Theorem1.3 actual strict-past FTL initial1/2'),dict(printed=6,pdf=18,scope='Sublinear best-regret consequence')],
    new_endpoints_are_derived=True,source_original_immutable=True,proposed_source_correction_separately_reviewed=True))
write(CONTRACT/'source-intent-v1.md','The printed ordinary-limit display is not the shared eventual upper-epsilon predicate. For the source same initial-half squared-loss FTL, ordinary limits for every fixed unit comparator exist precisely when the empirical mean converges. A single explicit binary stream has alternating dyadic blocks, empirical means with subsequential limits2/3 and1/3; actual fixed-zero average regret therefore cannot have an ordinary real limit even though actual upper NoRegret and best/T→0 hold. This derives a bounded SAME-algorithm obstruction, strengthening the older unbounded-affine arbitrary-algorithm example. It does not edit the pinned source or silently change its definition. No expected/high-probability/minimax or arbitrary protocol result.')
write(CONTRACT/'proposed-source-correction-v1.md','PROPOSED, separate from pinned source and prior Lean contracts: interpret the intended no-regret success condition as comparator-wise eventual upper-epsilon / limsup≤0 rather than unconditional existence of an ordinary limit. An alternative literal-lim statement for this squared FTL requires empirical-mean convergence. The concrete unit-stream obstruction and exact iff must be proved and separately source-reviewed before this proposal is accepted as reconciliation; no source text rewrite.')
context='''import BanditRLProof.OnlineFTLLimitSemantics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
namespace BanditRL.OnlineLearning

/-- Explicit binary dyadic-block observations, independent of the learner and horizon. -/
noncomputable def dyadicObservation : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 - dyadicObservation (n / 2)
termination_by n => n
decreasing_by omega

end BanditRL.OnlineLearning
'''
write(CONTRACT/'context-v1.lean.txt',context)
heads=[('D1','meanPredict_limitNoRegret_iff_mean_converges','''theorem meanPredict_limitNoRegret_iff_mean_converges (y : ℕ → ℝ)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) :
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2) (meanPredict y) ↔
      ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean y) atTop (nhds m)'''),
('D2','dyadicObservation_unit','''theorem dyadicObservation_unit :
    ∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1'''),
('D3','dyadic_empiricalMean_subsequences','''theorem dyadic_empiricalMean_subsequences :
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ) / 3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ) / 3))'''),
('D4','dyadic_meanPredict_obstruction','''theorem dyadic_meanPredict_obstruction :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)''')]
targets=[dict(id=i,name='BanditRL.OnlineLearning.'+n,header=h,statement_hash=statement_hash(h),phase='draft',compiled=False) for i,n,h in heads]
write(CONTRACT/'targets-v1.json',dict(version=1,targets=targets))
write(CONTRACT/'targets-v1.lean.txt','\n\n'.join(x['header'] for x in targets))
write(CONTRACT/'semantic-signature-v1.json',dict(space='ℕ-indexed single exogenous real observation stream, unit interval actions/comparators, squared loss',
    information='Same actual initial1/2 strict-past empirical-mean FTL, no horizon/future observation/limiting mean algorithm input',
    quantifiers='D1 one all-time unit y then iff literal every fixed unit comparator versus exists one real limit m inunit. D2-D4 one explicit all-time dyadicObservation, not horizon-varying sequences.',
    normalization='Signed comparator regret divided by natural horizon, real division total at0; subsequence indices≥1, positive cancellation only. Negative limits allowed.',
    probability='Deterministic pathwise. No stochastic expectations, filtration or loss/probability assumptions.',
    conclusion='Exact iff plus concrete bounded same-algorithm strict obstruction; upper-epsilon NoRegret and best/T0 explicitly coexist with failed ordinary-limit predicate.',
    evidence='Draft/probe not proofs; compilation/source/reader/fullgate/delivery separately required',chapter_complete=False,goal_complete=False))
write(CONTRACT/'dependency-dag-v1.json',dict(leaves=[dict(id='D1',ready=['meanPredict_fixedRegret_limit_iff','meanPredict_limitNoRegret_of_mean_converges','empiricalMean_mem']),
    dict(id='D2',ready=['dyadicObservation well-founded recursion']),dict(id='D3',requires=['D2','exact prefix-count induction','geometric subsequence limits']),
    dict(id='D4',requires=['D3','D2','meanPredict_fixedRegret_limit_iff','meanPredict_bestRegret_average_tendsto_zero','meanPredict_noRegret'])],single_lower_route=True))
write(CONTRACT/'conversion-window-v1.md','Public terminal headers and source remain frozen after stabilization. Allowed proof edit: new OnlineFTLOscillation body and local derived helpers only; no prior theorem assumptions, predicates, source or pins edit. Any target/model change requires new version + blind/source review. Public canary specification must be separately frozen/reviewed before its body. Integration only after BODY review; contributor gates must use committed candidate HEAD and explicitly cover newmodule, following retained M1 lesson. Original16/null preserved until chapter reconciliation; no Goal reset.')
write(CONTRACT/'proof-obligations-draft-v1.json',dict(derived_terminals=[dict(id=t['id'],state='draft',statement_hash=t['statement_hash']) for t in targets],
    helper_obligations=['actual binary recursion/unit membership','paired prefix sums','exact4^n-1 and2*4^n-1 counts','subsequence indices tend to infinity','two distinct squared-distance limits'],
    initial_ready_leaf='D1',source_claim_reconciliation_required=True,canary_required=True,full_gates_required=True,
    original_source_objects=16,unknown_required_proof_total=None,chapter_complete=False,goal_complete=False))
write(RUN/'reuse-search-v1.txt','Actual sources inspected: OnlineFTLLimitSemantics F1-F5, OnlineNoRegretSemantics literal/upper distinction, OnlineLearningMean empiricalMean/empiricalMean_mem, actual OnlineLearningAsymptotic meanPredict_noRegret. Prior compiled body/axioms/graph/registry evidence remains source-qualified. Mathlib actual search locates Analysis/SpecificLimits/Basic tendsto_pow_atTop_atTop_of_one_lt and Finset.sum_range_succ; no external dependency or source-number-only equivalence assumed. Exact #check signature probe next, no theorem body yet.')
write(CONTRACT/'reuse-decision-v1.json',dict(reuse='adapt_existing',canonical_existing=['meanPredict_fixedRegret_limit_iff','meanPredict_limitNoRegret_of_mean_converges','meanPredict_bestRegret_average_tendsto_zero','meanPredict_noRegret','empiricalMean_mem'],new_shared=['dyadicObservation','four derived terminals'],new_project=False,external_dependencies_added=False))
native('draft-new-task-v1','new-task',TASK,'--kind','proof','--title','Actual bounded FTL ordinary-limit reconciliation','--target-lean',PUBLIC.relative_to(ROOT).as_posix())
for folder in ['tasks','proof-obligations','conversion-windows']:
    p=ROOT/folder/(TASK+'.md');p.write_bytes(p.read_bytes()+('\n\n## Draft source contract\n\nFour derived targets in docs/contracts/online-ftl-obstruction-v1; D1 first dependency-ready leaf. Binary dyadic stream must be produced, no supplied limit/regret oracle. Source correction proposed separately; whole Goal ACTIVE, no chapter/source closure.\n').encode('utf8'))
fixed()
print('Four source-derived targets DRAFT; first ready D1; no public theorem body written.',flush=True)
