from common_v1 import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash

assert Path.cwd() == ROOT
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == BASE
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
assert not PUBLIC.exists() and not CANARY.exists()
assert sha(PDF) == PDF_SHA
prior = ROOT / 'runs/online-completed-causal-20261008'
ready = load(ROOT / 'tmp/online-completed-causal-final-ready-v2.json')
assert ready['actual_final_head'] == BASE and ready['worktree_clean'] and ready['official_attachment_committed']
assert ready['PR'] == 199 and ready['state'] == 'OPEN' and ready['draft'] and not ready['merged']
paths = ['BanditRLProof.lean', 'Tests.lean', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
         'runs/active_frontier.json', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl',
         'runs/lifecycle_memory.jsonl', 'MANIFEST.md',
         'website/content/readings.json', 'website/content/chapters.json', 'website/content/highlights.json',
         'website/content/functor_hypergraph.json', 'website/content/graph_memory_index.json',
         'BanditRLProof/OnlineGuessingCompletedCausal.lean', 'BanditRLProof/OnlineGuessingAECausal.lean',
         'BanditRLProof/OnlineGuessingRandomizedIID.lean', 'BanditRLProof/OnlineGuessingIIDBenchmark.lean',
         'BanditRLProof/OnlineLearningStochastic.lean',
         'docs/contracts/online-completed-causal-v1/chapter-one-source-ledger-accepted-v1.json',
         'docs/contracts/online-book-v1/coverage.json',
         'research-wiki/mathlib/theorem-cards.md']
rows = []
for rel in paths:
    p = ROOT / rel
    snapshot = RUN / 'baseline' / (rel.replace('/', '--') + '.raw')
    write(snapshot, p.read_bytes())
    rows.append(dict(path=rel, sha256=sha(p), snapshot=snapshot.relative_to(ROOT).as_posix()))
write(RUN / 'draft-baseline-v1.json', dict(rows=rows, base=BASE, basePR=199,
      canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc',
      shared_git='E:/ABRL/research/.git', lake_packages_junction='E:/ABRL/research/.lake/packages',
      current_source_branch=BRANCH, worktree=ROOT.as_posix(), protected_other_worktrees_preserved=True))
for filename in ['online-completed-causal-final-ready-v2.json', 'online-completed-causal-final-verify-v2.py',
                 'online-completed-causal-final-push-v1.log', 'online-completed-causal-final-push-v1-exit.json',
                 'online-completed-causal-final-PR199-v1.log', 'online-completed-causal-final-PR199-v1-exit.json',
                 'online-completed-causal-final-branch-v2.log', 'online-completed-causal-final-branch-v2-exit.json',
                 'online-completed-causal-final-PR199-v2.log', 'online-completed-causal-final-PR199-v2-exit.json',
                 'online-general-kernel-api-v1.lean', 'online-general-kernel-api-v1.log',
                 'online-general-kernel-api-v1-exit.json']:
    write(RUN / 'prior-delivery-and-retrieval' / filename, (ROOT / 'tmp' / filename).read_bytes())
for filename in ['source-pdf13-v1.png', 'source-pdf13-text-v1.txt', 'source-pdf15-v1.png', 'source-pdf15-text-v1.txt']:
    write(RUN / filename, (prior / filename).read_bytes())
write(RUN / '00_context.md',
      'Persistent unbudgeted Orabona v10 Chapters1-16 Goal ACTIVE. Requested GPT-6 Astra/medium; not runtime-attested. Canonical E:/ABRL/research main6847 clean and freshly fetched; shared Git/lake junctions and other worktrees preserved. Reused active book worktree on new branch codex/research-online-kernel-causal stacked on OPEN draft unmerged PR199 exact4db37e090143760d99b9aedd026a72fa0f1f09ac. Prior four ambient-null-augmentation derived proofs accepted/delivered; no source-object/chapter/Goal completion. Prior immediate GitHub head assertion failed after successful push, retained old capture and actual read-only repair captures now exact4db37; no force/repeated push or CI success claim.\n\n'
      'Current bounded delta: general measurable [0,1]-valued behavioral decision-kernel family on generated action and strict-observation histories, one law-independent sampler family and one infinite private uniform tape, actual causal recursion/consistency, actual joint and conditional kernel laws for every round, then same-process IID expected-fixed excess for every horizon. Not a claim that every arbitrary protocol/filtration has been reduced to this behavioral model. Original16 source objects/null unknown proof total and all other source/chapter/appendix gaps remain. No production body before reviewed frozen contract; single lower route. Distinct reused osd_blind/source_reviewer mandated by project semantic skill; no optional parallel proof agents, absolute blindness, external human review or runtime attestation. Root reread cached original texts and personally viewed PNG13/15; byte copies, not fresh rendering.\n')
write(CONTRACT / 'source-card-v1.json', dict(
    source_title='Online Learning: A Modern Introduction Using Convex Optimization', author='Francesco Orabona',
    url='https://arxiv.org/pdf/1912.13213v10', edition='arXiv:1912.13213v10', edition_date='2026-06-21',
    pdf_sha256=PDF_SHA, cache=PDF.resolve().as_posix(), anchors=[dict(printed_page=1,pdf_page=13),dict(printed_page=3,pdf_page=15)],
    reread_original_texts=True, personally_viewed_original_cached_pixels=True, fresh_render_performed=False,
    source_objects=['C1-GAME','C1-IID-LOWER','C1-EQ1.1-1.2'],
    formalization_delta='Five derived kernel-realization/probabilistic infrastructure endpoints; no five numbered source theorem attribution.'))
write(CONTRACT / 'source-intent-v1.md',
      'Source v10 printed1/PDF13: predict a unit number before revealing the next target; squared loss under a fixed unknown IID unit law cannot beat cumulative variance. Printed3/PDF15 states why a strategy can use the past while the future is unavailable. The source does not itself state a five-part stochastic-kernel representation theorem. This package makes a specified standard-Borel behavioral randomized policy model precise and connects its actual generated process to the source IID benchmark.\n\n'
      'Given ONE infinite family kappa_t of Markov kernels from (generated unit action history of lengtht, real observation history of lengtht) to I=[0,1], choose ONE jointly measurable sampler family f_t before any observation law or horizon. Draw one infinite tape U from product uniform volume; under rho x nu the tape is independent of the entire observation stream. The actual finite recursion starts from the empty action history and appends f_t((generated actions strictly beforet,Y_<t),U_t). No prediction kernel may be supplied with arbitrary future observations, a known mean or a horizon-specific strategy. Prove all earlier entries coincide with the SAME infinite generated process and prove nonanticipation under equality of tape coordinates<=t and observations<t.\n\n'
      'For EVERY probability observation-stream law nu (not necessarily IID/unit), derive the actual joint law of generated history and next action as history marginal compProd kappa_t, using fresh-draw independence produced from the infinite-product law and strict recursion. Then derive condDistrib equality AE on that actual history marginal. This is not assumed input; single-step mathlib sampling alone is insufficient. Bundled ProbabilityMeasure only expresses total mass1. Real observation history is deliberately unrestricted in realization. Unit outputs are typed, globally feasible.\n\n'
      'For the SAME family and process, under measurable coordinate IID/same-law targets AE in[0,1], prove every naturalT including0 expectedFixedRegret equals sum of expected squared prediction deviations from EY0 and is nonnegative. Population mean is analysis-only. Benchmark is minimum expected FIXED unit-comparator loss outside expectation. No pathwise/min-expectation exchange/rate/convergence/high-probability or adaptive-adversary guarantee follows from this product-law IID endpoint. Law-relative condDistrib equality does not make off-support histories unique. Classical sampler selection is not an executable distribution-free numerical sampler. Other private-state/general-filtration/completion constructions need separate precise contracts and remain required until audited. Original16/null/fullchapter/wholeGoal boundaries unchanged.\n')
text = (CONTRACT / 'targets-v1.lean.txt').read_text(encoding='utf8')
chunks = ['theorem ' + s.strip() for s in text.split('theorem ')[1:]]
targets = []
for i, header in enumerate(chunks, 1):
    name = re.search(r'theorem\s+(\w+)', header).group(1)
    targets.append(dict(id='K'+str(i), name='BanditRL.OnlineLearning.'+name,
          header=header, statement_hash=statement_hash(header), phase='draft', compiled=False))
assert len(targets) == 5
write(CONTRACT / 'targets-v1.json', dict(version=1, targets=targets,
      source_sha256=PDF_SHA, exact_context_sha256=sha(CONTRACT / 'context-v1.lean.txt'),
      new_body_count=0, source_theorem_count_claim=0, chapter_complete=False, goal_complete=False))
write(CONTRACT / 'dependency-dag-v1.json', dict(nodes=[
    dict(id='K1',requires=['Kernel.exists_measurable_map_eq_unitInterval'],ready=True),
    dict(id='K2',requires=['finite dependent recursion and finite-coordinate measurability'],ready=True),
    dict(id='K3',requires=['K2','iIndepFun_infinitePi','iIndepFun.indepFun_finset',
        'indepFun_prod','independent_private_seed_pair','Measure.compProd_apply'],ready=False),
    dict(id='K4',requires=['K3','condDistrib_ae_eq_of_measure_eq_compProd'],ready=False),
    dict(id='K5',requires=['K1','K2','K3','K4','randomized_history_policy_expectedFixed_excess'],ready=False)],
    lower_route='one finite causal recursion; derive fresh-draw joint law; instantiate same-policy IID producer',
    terminal='K5 law-independent selected family and same infinite process for all laws/rounds/horizons'))
write(CONTRACT / 'semantic-signature-v1.json', dict(
    source_sha256=PDF_SHA, source_objects=['C1-GAME','C1-IID-LOWER','C1-EQ1.1-1.2'],
    objects='unit action subtype I, real finite observation histories, one infinite uniform private tape',
    quantifiers='kappa infinite family -> exists f infinite family -> forall probability observation laws nu -> forall times/horizons',
    information='generated earlier actions; observations strictly beforet; random tape only coordinates<=t; no future-observation oracle',
    algorithm='actual finite recursion from empty history, projectively coherent same infinite prediction process',
    stochastic_modes='joint/conditional law: any probability nu; IID benchmark: joint coordinate independence, same law, AE unit observations',
    kernel_semantics='joint equality derived, then condDistrib AE on actual history marginal; not arbitrary off-support equality',
    feasibility='prediction typed I everywhere, target AE unit only for performance',
    normalization='natural time0 corresponds source first round; every T including0; expected-fixed minimum outsideE',
    mean='analysis only, not algorithm input', selection='classical jointly measurable sampler, not numerical algorithm extraction',
    scope='given behavioral kernels, not unproved universal reduction of arbitrary state/filtration/interactive adversaries',
    chapter_complete=False, goal_complete=False))
write(CONTRACT / 'reader-requirements-v1.json', dict(
    R1='Pinned v10 printed1/PDF13 and printed3/PDF15; five derived targets, no five printed-theorem claim; original16/null retained.',
    R2='One given infinite Markov-kernel family on generated action/strict-real-observation histories; one selected sampler before every law/horizon; global unit output subtype.',
    R3='Actual empty-start finite action recursion, prefix consistency with same infinite process and tape<=t/observations<t nonanticipation; no future loss sequence as algorithm input.',
    R4='Fresh uniform coordinate independence and product-law compatibility are proved from infinite product and actual strict history, not given stability/independence/desired kernel laws.',
    R5='Joint and conditional kernel law for every probability observation-stream law; conditional equality AE on actual history marginal and no off-support uniqueness.',
    R6='Same-process all-horizon IID expected-fixed identity/nonnegativity includingT0; coordinate independence/same-law/AE target unit assumptions; mean analysis-only, no rate/pathwise/minE interchange.',
    R7='Nondegenerate history-dependent kernel with actual earlier-action feedback/randomness/positive target variance; instantiate all five public endpoints, actual types/axioms/roots/Tests/fullharness/shadow/currentpixels; remaining arbitrary-protocol/source/chapter/appendix gaps and whole active Goal unchanged.'))
write(CONTRACT / 'canary-plan-v1.md',
      'Construct a genuinely stochastic, history-dependent unit decision kernel whose later distributions depend on previously generated actions and observed targets; retain positive-variance IID observations. Instantiate the selected-family producer, actual causal prefix/nonanticipation, joint law, conditional law and universal same-process expected-fixed terminal. Check naturalT0 and positive finite excess or variance. A constant deterministic policy or a bare single-step sampler quotation cannot discharge this canary. Exact nonzero quantities will be frozen with the actual canary proposal before proving it; no proof/candidate/compiled claim here.\n')
ledger = load(ROOT / 'docs/contracts/online-completed-causal-v1/chapter-one-source-ledger-accepted-v1.json')
assert len(ledger['original16_source_objects']) == 16 and ledger['required_proof_leaf_total'] is None
ledger['current_kernel_leaf_overlay'] = dict(task=TASK, phase='draft', derived_obligations=5, accepted=0,
    given_kernel_realization_required=True, general_protocol_reduction_unproved=True,
    chapter_complete=False, goal_complete=False)
write(CONTRACT / 'chapter-one-source-ledger-draft-v1.json', ledger)
write(RUN / '10_director-v1.md',
      'Bounded reusable-interface/integration delta within Chapter1: realize given behavioral decision kernels as one causal process, then connect actual process to existing IID expected-fixed producer. Do not start another chapter or replace globalSGB frontier. Sourceobjects/chapters/wholeGoal still open. Default single lower route; no quantitative experiment or model-strength change. K1 finite dependency-ready selection first; K2 causal recursion next; K3 law compatibility; K4 conditional adapter; K5 universal terminal.\n')
write(RUN / '11_architect-v1.md',
      'Reuse pinned mathlib kernel randomization once per natural time and classical countable choice for ONEfamily before nu. Fin.snoc dependent action recursion is actual implementation. Prove finite-input measurability by induction/lastCases, prefix coherence by induction, then nonanticipation by equality of finite inputs. Derive current uniform independence from finite disjoint coordinate blocks of infinitePi, transport to product nu, regroup observation stream/past tape/current draw with existing independent_private_seed_pair. Generated history is measurable in those past blocks. Map its joint law through jointly measurable sampler; prove product-map equals compProd by actual map_apply/prod_apply/compProd_apply. Use pinned condDistrib uniqueness only after actual joint equality. Lift IID/same-law/AE-unit observations through product snd, instantiate canonical randomized history producer using Fin-range/Fin equivalence and subtype-valued feasible policy. No added causal-independence premise. General product-map helper may be mathlib-candidate; route-specific wrappers remain thin.\n')
write(RUN / '12_worker-v1.md',
      'DRAFT only: algorithm context and five exact proposed headers written outside production. Prior API probe is actual Lean0 declaration/type retrieval only. No theorem body or mathematical terminal compiled. Source-blind decoding and anti-anchored contract review required before stabilization/proving. Frozen target cannot be weakened during proof repair.\n')
prototype = (CONTRACT / 'context-v1.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
for target in targets:
    rest = target['header'].split(target['name'].split('.')[-1],1)[1].strip().replace(' :\n', ',\n', 1)
    prototype += '\n#check (∀ ' + rest + ')\n'
prototype += '\nend BanditRL.OnlineLearning\n'
write(RUN / 'draft-typecheck-v1.lean', prototype)
gate('draft-typecheck-v1', 'lake', 'env', 'lean', RUN / 'draft-typecheck-v1.lean')
native('draft-new-task-v1', 'new-task', TASK, '--kind', 'causal-kernel-realization',
       '--title', 'One causal behavioral kernel process and exact IID expected-fixed excess',
       '--target-lean', PUBLIC.relative_to(ROOT).as_posix())
for directory in ['tasks','proof-obligations','conversion-windows']:
    p = ROOT / directory / (TASK + '.md')
    write(RUN / ('native-' + directory + '-template-v1.raw'), p.read_bytes())
    p.write_bytes(p.read_bytes() + ('\n\n## Draft5 derived kernel targets\n\n' +
        (CONTRACT / 'source-intent-v1.md').read_text(encoding='utf8') +
        '\nExact targets/context/DAG in ' + CONTRACT.relative_to(ROOT).as_posix() +
        '. K1 and K2 dependency-ready, K3/K4/K5 await actual predecessors. Syntax elaborated only; no terminal proof compiled. Separate semantic contract review required.\n').encode('utf8'))
native('draft-blueprint-v1', 'blueprint-refresh', TASK)
native('draft-lifecycle-v1', 'lifecycle-event', '--session', TASK, '--event', 'draft', '--payload-json',
       json.dumps(dict(run_id=RUN.name, contract_version=1, source_sha256=PDF_SHA,
       target_statement_hashes=[r['statement_hash'] for r in targets], obligations=5, compiled=0,
       chapter_complete=False, goal_complete=False)))
for name in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards',
             'proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    p = ROOT / 'research-wiki/retrieval-index' / (name + '.json')
    write(RUN / 'baseline' / ('retrieval-' + name + '.raw'), p.read_bytes())
native('draft-reference-index-v1', 'reference-index')
native('draft-search-kernel-v1', 'search-memory', 'kernel')
native('draft-search-sampler-v1', 'list-lean-decls', 'kernel_sampler', '--statement')
native('draft-search-actual-parent-v1', 'list-lean-decls', 'randomized_history_policy_expectedFixed_excess', '--statement')
write(RUN / 'memory_digest.md',
      'DRAFT unverified kernel package. Existing kernel single-step sampling/infinitePi and actual randomized_history_policy_expectedFixed_excess are named local retrieval candidates; read-only type probe Lean0 is not kernel proof progress. One coherent causal recursion, derived joint law and same-process terminal still REQUIRED. Previous completed-information4 accepted/delivered on PR1994db37, original16/null/remainingchapters preserved. Current source/statement review pending; no verified new lemma.\n')
write(RUN / 'retrieval_index.md',
      'Local pinned Mathlib Representation/CondDistrib/InfinitePi/MeasureCompProd/Fin.Tuple APIs inspected; exact declaration types in retained API probe and drafttype log. Canonical randomized-history producer is an exact candidate parent. Search-memory kernel/list-lean-decls sampler/parent actual logs separate from compile proofs. No Optlib/LML dependency/toolchain change or external unbuilt proof accepted. General fresh-history product-map lemma mathlib-candidate if absent; actual project recursion is route-local.\n')
print('Actual DRAFT five headers/context elaborated, native own task/blueprint/lifecycle recorded; no theorem body.', flush=True)
