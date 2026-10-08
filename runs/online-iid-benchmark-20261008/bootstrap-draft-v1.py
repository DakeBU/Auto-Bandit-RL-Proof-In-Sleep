from common_v1 import *

assert sha(PDF) == PDF_SHA
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == BASE
dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').splitlines()
assert all(RUN.relative_to(ROOT).as_posix() in row for row in dirty), dirty
pr = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/193']))
assert pr['head']['sha'] == BASE and pr['state'] == 'open' and pr['draft'] and not pr['merged']
write(RUN / 'stacked-base-PR193-v1.json', dict(PR=pr['html_url'], state='OPEN-DRAFT-unmerged', exact_head=BASE,
    canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc', no_main_update=True,
    actual_prior_DIRECT_audit='PR193 local/remote/REST exact, clean,516 task-owned raw files; four separate raw/Git global prefixes preserved'))
fixed_files = ['BanditRLProof/' + n + '.lean' for n in ['OnlineLearningMean', 'OnlineLearningFTL',
    'OnlineLearningFoundations', 'OnlineLearningRegret', 'OnlineLearningAsymptotic', 'OnlineNoRegretSemantics',
    'OnlineLearningHistory', 'OnlineLearningIID', 'OnlineLearningInformation', 'OnlineLearningStochastic', 'OnlineSquareMinimum']]
fixed_files += ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'docs/contracts/online-book-v1/source-inventory.json',
    'research-wiki/papers/sgb-theorem2-interface-frontier-trace.json', 'runs/active_frontier.json',
    'docs/contracts/online-square-minimum-v1/chapter-one-source-ledger-accepted-v2.json']
mutable = ['BanditRLProof.lean', 'Tests.lean', 'website/content/readings.json', 'website/content/highlights.json',
    'website/content/chapters.json', 'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
for p in fixed_files + mutable:
    write(RUN / 'snapshots' / (p.replace('/', '--') + '.raw'), Path(p).read_bytes())
write(RUN / 'draft-baseline-v1.json', dict(base=BASE, fixed_files={p:sha(p) for p in fixed_files},
    mutable_original_files={p:sha(p) for p in mutable}, PDF_sha256=PDF_SHA, chapter_complete=False, goal_complete=False))
sources = []
for page, origin in [(13, 'online-linearization-public-20261007'), (14, 'online-square-minimum-20261008')]:
    for extension in ['txt', 'png']:
        src = Path('runs') / origin / ('source-pdf' + str(page) + '-v1.' + extension)
        dst = RUN / src.name
        write(dst, src.read_bytes())
        sources.append(dict(source_cache=src.as_posix(), destination=dst.as_posix(), sha256=sha(dst),
            pdf_page=page, printed_page=page-12, provenance_preserving_copy_not_fresh_rerender=True,
            actual_ROOT_read_and_viewed=True))
from pypdf import PdfReader
reader = PdfReader(PDF)
for page in [13, 14]:
    write(RUN / ('fresh-pinned-pdf' + str(page) + '-text-v1.txt'), reader.pages[page-1].extract_text())
write(RUN / 'source-read-v1.json', dict(PDF_sha256=PDF_SHA, PDF_page_count=len(reader.pages),
    caches=sources, fresh_pinned_extraction_pages=[13,14], source_replaced=False))
write(RUN / '00_context.md', '''Persistent Orabona Chapters1–16 total Goal ACTIVE/unbudgeted. Requested GPT-6 Astra/medium, no escalation or runtime attestation. Canonicalmain still clean6847b678a73db68dee5101d6f05c2453c1405afc after explicit fetch of origin main; sharedGit E:/ABRL/research/.git and all worktrees/runtime junctions preserved. Current same shared Lean/Lake checkout E:/ABRL/worktrees/research-online-book, new branchcodex/research-online-iid from exact OPENdraft/unmergedPR193 bf9f896cdfebb2b836dacb01f3d4b209466c2100. Prior square-minimum package delivered; no main/live/merge/deploy/retirement.

Next dependency-ready source hinge printed1–2/PDF13–14: mean is feasible and attains minimum of EXPECTED FIXED cumulative square loss, valueT*variance; this is not expectation of hindsight minimum. Derive the cumulative expected excess and its nonnegativity for genuine measurable bounded strict-history policies using actual finite-history independence. Also instantiate the actual initial1/2 strict-past meanPredict and constant distribution-mean oracle. Inputs are measurable real random variables with almost-sure unit interval support, same laws and, only for causal regret endpoints, joint independence. Do not silently strengthen a.s. support to all sample points. Existing old pointwise IID/mean APIs are reuse candidates, not sufficient source audit evidence.

Generic independent-prediction identity is only an intermediate shared consumer with TWO genuine producers (strict history policy and meanPredict); it cannot close the source target alone. Generic benchmark definitions alone imply no integrability, causality, performance, or nonnegativity. Finite-history policies here are deterministic functions of past targets, with empty initial tuple; independent external randomization/general history-filtration extension requires a separately reviewed mandatory source-coverage audit, not a claim of all randomized algorithms. T0 is a disclosed empty-prefix extension, no unique minimum; normalized endpoint requiresT>0. Source1..T=Lean0..T−1. No high-probability/asymptotic-success/min-expectation exchange claim.

Original16C1items/proof-totalnull/C1open/C2incomplete/3–16unenumerated/necessaryappendicesrequired/GoalACTIVE. Five main-relative Foundations/History/IID/Information/Stochastic source-module audits remain unwaived; this package must separately audit exact reused BODYs and does not infer whole-module/chapter closure. One lower route, staged ROOT director/architect/worker, mandatory distinct reused decoder/source reviewer only; disclose staged history, no absolute-blind/human/external/runtime or single enforced-runtime-method claim.
''')
write(RUN / '10_director.md', 'Freeze finite eight-terminal package: expected fixed-prefix decomposition, actual feasible mean/IsLeast minimum, its real sInf value; one shared cumulative independent-prediction consumer; genuine strict-history and actual meanPredict cumulative excess/nonnegativity producers; constant mean optimum and positive-horizon normalization. First finite leaf is expected fixed-prefix decomposition; source stabilization and exact draft-type compilation precede bodies. Remaining randomized/source-wide coverage and source asymptotic equivalence remain required and cannot be excluded to claim full C1.')
write(RUN / '20_architect.md', 'Single route: use actual expected_square_decomposition after deriving MemLp2 from a.s. bounds, integral_finset_sum and same-law integrals/variances. Produce distribution mean feasibility via integral_nonneg_of_ae/integral_mono_ae, IsLeast membership/lower bounds, then IsLeast.csInf_eq. Generic cumulative loss identity uses actual independent_prediction_square and integrable finite sums. Genuine strict-past policy derives current-target independence from history_policy_independent; actual meanPredict uses meanPredict_independent/measurable plus a.s. support aggregated with ae_all_iff to produce MemLp2. Reuse normalized_excess only atT>0. No old math edits/new dependency/project/toolchain. Literal expected minimum and performance need separate source/type/body/reader evidence.')
write(RUN / 'memory_digest.md', 'Draft only; next true expected-fixed minimum and causal IID cumulative variance. Eight prospective terminals/two definitions; no theorem body or source acceptance. No exchange with hindsight minimum, no deterministic-policy-to-all-randomized claim, no chapter/Goal closure.')
write(RUN / 'retrieval_index.md', 'Candidates: expected_square_decomposition, independent_prediction_square, history_policy_independent, meanPredict_independent/measurable/mem, source_mean_optimal, iid_meanPredict_excess, normalized_excess; note last old IID/mean producers require pointwise support, whereas this new contract will retain a.s. support. Actual native/canonical retrieval and draft compilation pending.')
for command in ['new-task', 'lifecycle-event', 'blueprint-refresh', 'reference-index', 'list-lean-decls', 'search-memory']:
    native(command + '-help-v1', command, '--help')
native('new-task-v1', 'new-task', TASK, '--kind', 'lean', '--title', 'Produce expected fixed square-loss minimum and causal IID cumulative variance benchmark',
    '--target-lean', PRE + 'history_policy_expectedFixed_excess')
native('draft-lifecycle-v1', 'lifecycle-event', '--session', TASK, '--event', 'draft', '--payload-json', json.dumps(dict(
    run_id=RUN.name, root_goal='Persistent Orabona Chapters1–16', scope='Expected fixed-loss minimum and actual causal IID benchmark',
    exact_base_PR=193, exact_base_head=BASE, chapter_complete=False, goal_complete=False)))
native('actual-blueprint-refresh-v1', 'blueprint-refresh', TASK)
fixed()
print('Actual native draft/blueprint/source read recorded; contract/type/source review precede body proofs.')
