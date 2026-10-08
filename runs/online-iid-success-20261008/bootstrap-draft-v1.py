from common_v1 import *
assert sha(PDF) == PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip() == BASE
pr = json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/195']))
assert pr['head']['sha'] == BASE and pr['state']=='open' and pr['draft'] and not pr['merged']
write(RUN/'stacked-base-PR195-v1.json', pr)
gate('baseline-PR195-CI-v1','gh','pr','view','195','--json','number,state,isDraft,headRefOid,baseRefName,statusCheckRollup')
gate('baseline-main-contributor-failure-v1','gh','run','view','37755661984','--job','113239437754','--log-failed')
fixed_files = [p.as_posix() for p in Path('BanditRLProof').glob('Online*.lean')]
fixed_files += ['lean-toolchain','lakefile.lean','lake-manifest.json',
    'docs/contracts/online-book-v1/source-inventory.json','runs/active_frontier.json',
    'research-wiki/papers/sgb-theorem2-interface-frontier-trace.json',
    'docs/contracts/online-randomized-iid-v1/chapter-one-source-ledger-accepted-v3.json']
mutable = ['BanditRLProof.lean','Tests.lean','website/content/readings.json',
    'website/content/highlights.json','website/content/chapters.json','MANIFEST.md',
    'runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
for p in fixed_files + mutable:
    write(RUN/'snapshots'/(p.replace('/','--')+'.raw'),Path(p).read_bytes())
write(RUN/'draft-baseline-v1.json',dict(base=BASE,branch=BRANCH,
    fixed_files={p:sha(p) for p in fixed_files}, mutable_original_files={p:sha(p) for p in mutable},
    PDF_sha256=PDF_SHA,chapter_complete=False,goal_complete=False))
from pypdf import PdfReader
import pypdfium2 as pdfium
reader = PdfReader(PDF)
render = pdfium.PdfDocument(str(PDF))
for page in [13,14,16]:
    write(RUN/('source-pdf'+str(page)+'-text-v1.txt'),reader.pages[page-1].extract_text())
    target = RUN/('source-pdf'+str(page)+'-v1.png')
    assert not target.exists()
    render[page-1].render(scale=1.4).to_pil().save(target)
write(RUN/'source-read-v1.json',dict(PDF_sha256=PDF_SHA,PDF_pages=len(reader.pages),
    fresh_extracted_and_rendered_pdf_pages=[13,14,16],source_replaced=False))
write(RUN/'00_context.md','''Persistent Orabona Chapters1–16 total Goal ACTIVE/unbudgeted. Requested GPT-6 Astra/medium; no escalation or runtime attestation. Canonical main clean6847b678a73db68dee5101d6f05c2453c1405afc=origin/main; exact OPENdraft/unmergedPR195 head372c9a6c138c50d7a5e08e91351238f231565219 stacked base. New branchcodex/research-online-iid-success uses same shared Lean/Lake worktree E:/ABRL/worktrees/research-online-book. All other checkouts/sharedGit/runtime junctions retained.

Next required source scope printed1–2/PDF13–14: stochastic expected-fixed excess sublinear iff average expected loss minus variance tends to zero; actual strict-past meanPredict unknown-law algorithm success derived from source Theorem1.3 printed4/PDF16. Existing private-seed lower producer only characterizes bounded measurable policies; it does NOT make every policy successful. No arbitrary-kernel representation, completed-information or AE-factorization coverage closure. Five old main-relative source-module audits REQUIRED; live remote push CI failed those five contributor contracts; PR-base contributor passed and remote Lean build still running at captured baseline. No bypass or fabricated green.

Freeze four targets: generic centered-total little-o/average equivalence; actual bounded private-seed policy nonnegative excess and success/MSE-Cesaro equivalences; actual meanPredict expected-fixed4+4logT upper bound WITHOUT independence; actual jointIID meanPredict ordinary zero normalized limit AND little-o. T0 expressions defined but normalized identities only eventualT>0, never require genericA0=0/c=0. Same one infinite process/policy for every horizon. Mean only analysis benchmark, algorithm only strict history and initialhalf. Source minOUTSIDEexpectation, no expected hindsight minimum substitution. A.s.support sufficient; derive L2/integrability, never strengthen to allomega.

Single lower route staged ROOT director/architect/worker. Required distinct reused decoder/source reviewer; disclose actor history, no absolute-blind/human/external claims. Old source/proofs/readers immutable. Global SGBfrontier unchanged, own scoped lifecycle. C1/C2open; original16sourceobjects/proof-totalnull preserved;3–16unenumerated/appendicesrequired/Goalactive. No merge/deploy/retirement.
''')
write(RUN/'10_director.md','Four finite terminals must connect source C1EQ1.1-1.2 to actual stochastic algorithm success. Contract first; no proof bodies before independent semantic review. Single lower route. Full chapter remains open, every required source/audit/kernel coverage gap retained.')
write(RUN/'20_architect.md','R1 uses Mathlib little-o iff quotient tends to zero plus eventualT>0 normalization, not a bespoke asymptotic foundation. R2 uses actualPR195 seeded strict-past excess identity and actualPR194 expected-fixed minimum. R3 integrates source Theorem1.3 versus population mean using empiricalMean_minimizes and a.s.support-derived square integrability. R4 sandwiches nonnegative normalized expected-fixed excess below vanishing (4+4logT)/T, then uses R1. Actual fairIID sample-mean and persistent-private-seed non-success canaries. Ordinary zero limit distinct from existing adversarial eventual-upper-epsilon NoRegret.')
write(RUN/'memory_digest.md','Draft source, stacked base and actual CI records only; no stabilized/proved/accepted claim. Whole Goal active.')
write(RUN/'retrieval_index.md','Existing normalized_excess, expectedFixedMinimum_eq_variance, meanPredict_expectedFixed_excess, randomized_history_policy_expectedFixed_excess, theorem_1_3, empiricalMean_minimizes, meanPredict_measurable/mem. Mathlib MLIB-ASYMPTOTICS, MLIB-MEASURE-INTEGRAL, MLIB-REAL-LOG-SQRT. No LML/new library/toolchain change. Typed declaration search and contract audit pending.')
for command in ['new-task','lifecycle-event','blueprint-refresh','search-memory','list-lean-decls','reference-index','list-mathlib','list-papers','list-weapons']:
    native(command+'-help-v1',command,'--help')
native('new-task-v1','new-task',TASK,'--kind','lean','--title',
    'IID guessing stochastic success and actual sample-mean learner convergence',
    '--target-lean',PRE+'meanPredict_iid_success')
native('draft-lifecycle-v1','lifecycle-event','--session',TASK,'--event','draft',
    '--payload-json',json.dumps(dict(run_id=RUN.name,root_goal='Orabona Chapters1–16',
        exact_base_PR=195,exact_base_head=BASE,chapter_complete=False,goal_complete=False)))
native('blueprint-refresh-v1','blueprint-refresh',TASK)
for command in ['reference-index','list-mathlib','list-papers','list-weapons']:
    native(command+'-v1',command)
for i,q in enumerate(['normalized_excess','isLittleO','meanPredict','expectedFixedRegret']):
    native('memory-query'+str(i)+'-v1','search-memory',q)
    native('declarations-query'+str(i)+'-v1','list-lean-decls',q,'--statement')
fixed()
print('Native draft and pinned source baseline created; no proof bodies or acceptance.')
