from common_v1 import *

assert sha(PDF) == PDF_SHA
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == BASE
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
pr = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/194']))
assert pr['head']['sha'] == BASE and pr['state'] == 'open' and pr['draft'] and not pr['merged']
write(RUN / 'stacked-base-PR194-v1.json', dict(PR=pr['html_url'], exact_head=BASE,
    state='OPEN-DRAFT-unmerged', canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc',
    no_main_update=True, prior_delivery='PR194 clean exact local/remote/REST b08;926 owned files raw audit passed'))
fixed_files = ['BanditRLProof/' + n + '.lean' for n in ['OnlineLearningMean', 'OnlineLearningFTL',
    'OnlineLearningFoundations', 'OnlineLearningRegret', 'OnlineLearningAsymptotic', 'OnlineNoRegretSemantics',
    'OnlineLearningHistory', 'OnlineLearningIID', 'OnlineLearningInformation', 'OnlineLearningStochastic',
    'OnlineSquareMinimum', 'OnlineGuessingIIDBenchmark']]
fixed_files += ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    'docs/contracts/online-book-v1/source-inventory.json',
    'research-wiki/papers/sgb-theorem2-interface-frontier-trace.json', 'runs/active_frontier.json',
    'docs/contracts/online-iid-benchmark-v1/chapter-one-source-ledger-accepted-v4.json']
mutable = ['BanditRLProof.lean', 'Tests.lean', 'website/content/readings.json',
    'website/content/highlights.json', 'website/content/chapters.json',
    'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
for p in fixed_files + mutable:
    write(RUN / 'snapshots' / (p.replace('/', '--') + '.raw'), Path(p).read_bytes())
for p in ['MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']:
    write(RUN / 'snapshots' / ('git-base--' + p.replace('/', '--') + '.raw'),
        subprocess.check_output(['git', 'show', BASE + ':' + p]))
write(RUN / 'draft-baseline-v1.json', dict(base=BASE,
    fixed_files={p:sha(p) for p in fixed_files}, mutable_original_files={p:sha(p) for p in mutable},
    PDF_sha256=PDF_SHA, chapter_complete=False, goal_complete=False))
from pypdf import PdfReader
reader = PdfReader(PDF)
for page in [13, 14]:
    write(RUN / ('fresh-pinned-pdf' + str(page) + '-text-v1.txt'), reader.pages[page-1].extract_text())
    src = Path('runs/online-iid-benchmark-20261008') / ('source-pdf' + str(page) + '-v1.png')
    write(RUN / src.name, src.read_bytes())
write(RUN / 'source-read-v1.json', dict(PDF_sha256=PDF_SHA, PDF_page_count=len(reader.pages),
    fresh_extraction_pdf_pages=[13,14], PNGs='exact provenance copies from prior source cache; not fresh renders',
    source_replaced=False))
write(RUN / '00_context.md', '''Persistent Orabona Chapters1–16 total Goal ACTIVE/unbudgeted. Requested GPT-6 Astra/medium; no escalation or model-runtime attestation. Canonical main freshly fetched, clean6847b678a73db68dee5101d6f05c2453c1405afc; sharedGit E:/ABRL/research/.git, runtime junctions and every existing worktree retained. New branchcodex/research-online-randomized-iid from exact OPENdraft/unmergedPR194 b08f8312259ae10032b6318060e18911532d4610. Previous expected-fixed/deterministic IID package delivered; not main/live.

Next required source scope printed1–2/PDF13–14: cannot beat IID variance with private randomness and strict-past information. Seed must be independent of WHOLE target process, not only individually independent of each target. Current-target independence must be PRODUCED from this joint information structure and actual IID; supplying prediction-current independence is not a complete causal lower producer. General predictable information is a subspace of the seed+strict-past generated sigma field; no unmodeled side information about future targets. Seed codomain arbitrary measurable space, reusable entire private tape allowed; no randomization representation theorem for every kernel asserted.

Keep probability, measurable targets, a.s.unit support, same laws and joint IID. Policies jointly measurable in seed and finite past, feasible only on legal histories for every seed; abstract predictions only need a.s.feasibility. Derive all L2. Exact minimum is minimum of EXPECTED FIXED loss, outside expectation, reusing accepted PR194 actual minimum. T0 empty-prefix extension; finite normalized identities/asymptotic success remain separate mandatory work. Original16C1source items/proof-totalnull retained; C1/C2open,3–16unenumerated/appendicesrequired/GoalACTIVE. Five old main-relative source-module audits remain unwaived.

Single lower route with staged ROOT director/architect/worker. Mandatory distinct reused decoder/source reviewer; staged actor history disclosed, no absolute-blind, human/external, independent experiment, or single-runtime enforced workflow claim. Preserve all old contracts/body/readers and active globalSGBfrontier; own task frontier only. No merge/deploy/retirement.
''')
write(RUN / '10_director.md', 'Freeze seven producer/interface terminals and one generated-information definition. First finite leaf is the independent-seed triple regrouping lemma; then actual seeded strict-history independence, monotone information, predictable independence and two cumulative excess producers. Remaining asymptotic and old module source audits REQUIRED. No conclusion from declarations alone.')
write(RUN / '20_architect.md', 'One route: joint-law independence -> measurable product associativity -> (seed,past) independent current; compose whole-process seed independence with exact finite (past,current) extraction, and use actual target IID finite-history independence. Define information as comap of(seed,past), prove monotonicity via restriction; weaken left sigma field for predictable functions. Derive L2 from a.s.unit interval and apply PR194 literal expected-fixed minimum and cumulative square identity. Actual product-seed IID/XOR canaries must show joint dependence boundary; no pairwise shortcut.')
write(RUN / 'memory_digest.md', 'Draft only: private seed plus strict past/generic subordinate information IID variance lower producer. No stabilized contract, proof, source acceptance, chapter or Goal closure yet.')
write(RUN / 'retrieval_index.md', 'Actual pinned local candidates: indepFun_iff_map_prod_eq_prod_map_map, Measure.prodAssoc_prod, Measure.map_map, iIndepFun.indepFun_finset, IndepFun.comp, IndepFun_iff_Indep, indep_of_indep_of_le_left, Measurable.comap_le, expectedFixedMinimum_eq_variance, iid_cumulative_prediction_decomposition. Failed guessed Prod/Basic.lean path retained in session; actual Constructions.lean located via rg--files, no fabricated all-query success.')
for command in ['new-task', 'lifecycle-event', 'blueprint-refresh', 'list-lean-decls', 'reference-index']:
    native(command + '-help-v1', command, '--help')
native('new-task-v1', 'new-task', TASK, '--kind', 'lean',
    '--title', 'Private seed and predictable strict-past IID guessing variance benchmark',
    '--target-lean', PRE + 'randomized_history_policy_expectedFixed_excess')
native('draft-lifecycle-v1', 'lifecycle-event', '--session', TASK, '--event', 'draft',
    '--payload-json', json.dumps(dict(run_id=RUN.name, root_goal='Orabona Chapters1–16',
        exact_base_PR=194, exact_base_head=BASE, chapter_complete=False, goal_complete=False)))
native('blueprint-refresh-v1', 'blueprint-refresh', TASK)
fixed()
print('Native draft and source/baseline records produced; theorem bodies require reviewed stabilization.')
