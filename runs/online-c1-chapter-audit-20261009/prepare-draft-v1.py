from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.bandit import scan_lean_declarations
from tools.abrl_lifecycle import lean_declaration_header,statement_hash,_strip_lean_comments
import re

fixed()
historical=ROOT/'docs/contracts/online-ftl-obstruction-v1/chapter-one-source-ledger-accepted-v1.json'
old=load(historical)
assert len(old['original16_source_objects'])==16
catalogue=scan_lean_declarations(include_tests=False)
byname={x['full_name']:x for x in catalogue}
ns='BanditRL.OnlineLearning.'
mapping={
 'C1-GAME':['meanPredict_prefix','meanPredict_mem','ftlPredict_prefix','ftlPredict_mem','randomized_history_policy_independent','completed_predictable_private_seed_independent'],
 'C1-IID-MEAN':['expected_fixed_prefix_decomposition','expected_fixed_prefix_minimum','expectedFixedMinimum_eq_variance','constant_mean_expectedFixed_excess_zero'],
 'C1-IID-LOWER':['randomized_history_policy_expectedFixed_excess','ae_predictable_private_seed_expectedFixed_excess','completed_predictable_private_seed_expectedFixed_excess','causal_kernel_realization_and_expectedFixed_excess'],
 'C1-EQ1.1-1.2':['normalized_excess','history_policy_normalized_expectedFixed_excess','centered_total_sublinear_iff_average','randomized_history_policy_success_iff'],
 'C1-REGRET':['comparatorRegret_eq_sum','guessing_prefix_minimum','squaredLoss_minimum_eq','squaredBestRegret_eq_comparatorRegret','comparatorRegret_le_squaredBestRegret'],
 'C1-NOREGRET':['limitNoRegret_implies_noRegret','limitNoRegret_iff_noRegret_of_converges','meanPredict_limitNoRegret_iff_mean_converges','dyadic_meanPredict_obstruction'],
 'Remark1.1':['comparatorRegret_eq_sum'],
 'C1-MEAN-PREFIX':['empiricalMean_decomposition','empiricalMean_minimizes','empiricalMean_mem','empiricalMean_unique','guessing_prefix_minimum'],
 'C1-FTL':['ftlPredict_prefix','ftlPredict_mem','ftlPredict_half','ftlState_first','ftlState_eq_predict','ftlState_prefix','ftlState_mem','ftlState_half'],
 'Lemma1.2':['lemma_1_2'],
 'Theorem1.3':['theorem_1_3','meanPredict_bestRegret_bound'],
 'C1-STABILITY':['empiricalMean_update','meanPredict_stability','meanPredict_initial_stability'],
 'C1-REFINED-REGRET':['meanPredict_regret_refined','meanPredict_bestRegret_refined'],
 'C1-LOG-UNAVOIDABLE':['GuessingLower.randomized_log_lower'],
 'C1-HARMONIC':['UPSTREAM.harmonic_le_one_add_log'],
 'C1-SUCCESS':['meanPredict_noRegret','meanPredict_bestRegret_average_tendsto_zero','meanPredict_iid_success']}
assert set(mapping)=={x['source_id'] for x in old['original16_source_objects']}
allnames=sorted(set(n if n.startswith('UPSTREAM.') else ns+n for names in mapping.values() for n in names))
targets=[]
for i,name in enumerate(allnames,1):
    if name.startswith('UPSTREAM.'):
        name=name.split('.',1)[1];path=ROOT/'.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Bounds.lean';kind='theorem'
    else:
        record=byname[name];path=ROOT/record['file'];kind=record['kind']
    assert kind in ['theorem','lemma'],(name,kind)
    header=lean_declaration_header(path,name)
    targets.append(dict(id='A%03d'%i,name=name,path=path.resolve().as_posix(),
        header=header,statement_hash=statement_hash(header),file_sha256=sha(path),
        source_ids=[k for k,v in mapping.items() if (ns+name.rsplit('.',1)[-1] in [ns+x for x in v]) or
            name in [ns+x for x in v] or 'UPSTREAM.'+name in v],
        reuse='reuse_existing',production_body_or_header_edit_allowed=False,
        whole_public_value_check_required=True,prior_acceptance_not_current_chapter_acceptance=True))
write(CONTRACT/'targets-v1.json',dict(version=1,phase='draft',target_kind='existing-public-proof audit and chapter integration',
    required_source_object_count=16,selected_named_proof_values=len(targets),new_production_theorems=0,
    count_is_not_source_coverage=True,targets=targets))
write(CONTRACT/'targets-v1.lean.txt','\n\n'.join(x['header'] for x in targets))
context_names=[ns+x for x in ['comparatorRegret','NoRegret','LimitNoRegret','empiricalMean','meanPredict',
    'ftlPredict','ftlMeanStep','ftlState','squaredBestRegret','expectedFixedMinimum','expectedFixedRegret',
    'privateSeedPastInformation','KernelDecisionHistory','KernelDecisionSampler','kernelGeneratedActions',
    'kernelCausalPolicy','kernelGeneratedHistory','kernelGeneratedPrediction','dyadicObservation']]
context_names += [ns+'GuessingLower.'+x for x in ['binaryStream','binaryValues','causalPredict','pathRegret']]
context=[]
for name in context_names:
    r=byname[name];p=ROOT/r['file'];text=_strip_lean_comments(p.read_text(encoding='utf8'))
    short=name.rsplit('.',1)[1]
    match=re.search(r'(?m)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+'+re.escape(short)+r'\b',text)
    assert match,name
    after=text[match.start():]
    nextdecl=re.search(r'(?m)^\s*(?:(?:noncomputable|private)\s+)?(?:theorem|lemma|def|abbrev)\s+\w+',after[match.end()-match.start():])
    end=(match.end()-match.start()+nextdecl.start()) if nextdecl else len(after)
    block=after[:end].strip()
    block=re.sub(r'(?m)^end\s+.*$','',block).strip()
    context.append(dict(name=name,path=p.resolve().as_posix(),file_sha256=sha(p),
        exact_source_block=block,header=lean_declaration_header(p,name)))
write(CONTRACT/'definition-context-v1.json',dict(context_only=True,not_a_new_Lean_project=True,definitions=context))
write(CONTRACT/'context-v1.lean.txt',
    'Necessary exact definition context only. Not a production file and no proof or verdict is supplied.\n'
    'Ambient notation: open Filter MeasureTheory ProbabilityTheory Asymptotics BanditRL.OnlineLearning unitInterval; universes u v w z.\n\n'+
    '\n\n'.join('Actual scoped name '+x['name']+'\n'+x['exact_source_block'] for x in context))
notes={
 'C1-GAME':'Same unit squared-loss game. Strict-prefix deterministic/state causality is produced; IID current independence is produced from independent private randomness and strict past. Pathwise every-realization bound permits an adversary observing the deterministic current choice. It does not assert an arbitrary action-dependent stochastic environment is IID.',
 'C1-IID-MEAN':'Mean oracle is an analytical benchmark, never supplied to unknown-law meanPredict. Probability, measurability and AE unit support are explicit. The expected FIXED-comparator minimum lies OUTSIDE expectation; IsLeast is produced before real csInf. No min/expectation interchange.',
 'C1-IID-LOWER':'Every quantified measurable legal-cube private-seed policy, AE/completed predictable version, and produced unit-valued causal-kernel strategy has nonnegative expected fixed regret under joint IID and independent private randomness. Current independence is derived, not an input oracle. Audit whether these explicit mathematical strategy/information models discharge the source cannot-do-better claim; the arbitrary-protocol/filtration/private-state reduction caveat is preserved for reviewer adjudication, not silently removed.',
 'C1-EQ1.1-1.2':'Exact total-average identity only for T>0. Little-o centered total iff ordinary zero average holds on the same all-time process, using eventually positive horizons. General strategy success is characterized, not asserted for every strategy; T0 is separately an empty extension.',
 'C1-REGRET':'Comparator remains a fixed evaluation parameter, not learner input. Both signed comparator regret and true feasible interval minimum are represented. Footnote1 loss domain W/comparator V subsetW mapping was accepted in ONLINE-REGRET-DOMAINS-20261007, not a generic regret performance theorem; new chapter mapping must preserve its typed carrier and no loss evaluation outside declared domain.',
 'C1-NOREGRET':'Literal ordinary finite real nonpositive-limit predicate is kept separate from eventual upper-epsilon NoRegret. Equivalence requires actual comparator-wise convergence. The same bounded actual FTL dyadic counterexample refutes universal ordinary-limit inference from the printed logarithmic upper bound; exact iff characterizes when the literal predicate holds. The pinned source, true finite Theorem1.3, obstruction and separately reviewed correction PROPOSAL are four separate objects. Source definition represented is not a universal convergence proof. Reviewer must decide chapter reconciliation authority; no silent weakened target.',
 'Remark1.1':'The loss sequence is an explicit parameter of comparatorRegret; notation suppression changes no mathematics. A nondegenerate loss-swap test must expose this dependence, without altering the learner/comparator interface.',
 'C1-MEAN-PREFIX':'Positive-prefix unique empirical mean is produced and feasible, with actual minimization and least-element identification. T0 uses an explicit empty convention and never claims uniqueness. Unbounded real comparator minimization generalizes source interval without replacing feasible-minimum evidence.',
 'C1-FTL':'All feasible initial values have the source strict-past algorithm and true count/mean recursive state; the printed Theorem1.3 performance branch uses exactly initial1/2. Count/mean state update consumes only the next observation. No all-future-sequence arbitrary algorithm existence or best-history minimization oracle.',
 'Lemma1.2':'Source explicitly assumes feasible exact cumulative minimizers; arbitrary ambient carrier is a harmless geometry-free generalization. Current-prefix hindsight leaders are distinct from the causal FTL predictor. Zero-prefix extension is empty, and no arbitrary argmin existence is claimed.',
 'Theorem1.3':'For every finite positive T and actual unit observations, initial1/2 strictpast FTL has true interval-best regret at most4+4lnT. Empirical-mean minimizer is separately produced before literal minimum identification. The learner is fixed, never horizon- or comparator-selected.',
 'C1-STABILITY':'Exact mean update, actual zero-based one-step4/(t+1), and sharp initial1/4 are preserved. They come from the real predictor and current observation, not supplied stability premises.',
 'C1-REFINED-REGRET':'Actual SAME predictor true-minimum regret is at most1/4 + sum of4/(t+2) for t<T-1. This is the printed intermediate estimate and indices/initial term are not absorbed or changed.',
 'C1-LOG-UNAVOIDABLE':'Source qualitative logarithmic dependence is necessary. Existing producer quantifies every bounded measurable private-seed causal binary-history policy and positive horizon, produces one deterministic binary sequence with seed-expected regret at least ln(T+2)/6. The1/6 coefficient is derived, not printed/sharp; no full real-valued minimax constant or future-observing strategy impossibility.',
 'C1-HARMONIC':'Reuse exact pinned Mathlib harmonic bound. It is a required proof dependency, not a new ABRL theorem. Finite harmonic normalization and eventual positive T distinguish log0 convention from source natural domain.',
 'C1-SUCCESS':'Actual same FTL has upper-epsilon regret, ordinary zero normalized TRUE-best regret, and ordinary zero/little-o expected FIXED regret under joint IID/AEunit support. Ordinary fixed-comparator adversarial convergence is deliberately not inferred, and its bounded obstruction remains visible.'}
fresh=[]
for item in old['original16_source_objects']:
    sid=item['source_id'];selected=[]
    for n in mapping[sid]:selected.append(n.split('.',1)[1] if n.startswith('UPSTREAM.') else ns+n)
    fresh.append(dict(source_id=sid,printed_page=item['printed_page'],pdf_page=item['pdf_page'],
        kind=item['kind'],required_maintext=True,pinned_intent=item['target_intent'],
        exact_public_names=selected,current_semantic_contract=notes[sid],
        status='draft-chapter-reconciliation; full semantic/current compiled/chapter gates pending',
        acceptance_permission='No API presence, old accepted-local flag, theorem count or individual package delivery closes this source object.'))
write(CONTRACT/'chapter-one-source-map-draft-v1.json',dict(version=1,phase='draft',
    historical_ledger=historical.as_posix(),historical_ledger_sha256=sha(historical),
    original16_source_objects_preserved_verbatim=old['original16_source_objects'],current_mapping=fresh,
    independently_optional=[dict(id='History1.1',pages='printed6-7/PDF18-19'),
        dict(id='Problem1.1',status='planned/optional',pages='printed7/PDF19'),
        dict(id='Problem1.2',status='planned/optional',pages='printed7/PDF19')],
    no_maintext_result_excluded=True,unknown_proof_total_preserved=True,chapter_complete=False,goal_complete=False,
    historical_coverage7_flag_requires_separately_reviewed_reconciliation=True))
write(CONTRACT/'source-intent-v1.md','\n\n'.join(x['source_id']+' (printed'+str(x['printed_page'])+'/PDF'+str(x['pdf_page'])+')\n'+x['pinned_intent']+'\n'+x['current_semantic_contract'] for x in fresh))
write(CONTRACT/'initial-DAG-v1.json',dict(kind='source-semantic prerequisite overlay; compiler directVALUE extraction separate',
    edges=[['C1-GAME','C1-FTL'],['C1-MEAN-PREFIX','Theorem1.3'],['C1-FTL','C1-STABILITY'],
        ['Lemma1.2','C1-REFINED-REGRET'],['C1-STABILITY','C1-REFINED-REGRET'],
        ['C1-REFINED-REGRET','Theorem1.3'],['C1-HARMONIC','Theorem1.3'],['Theorem1.3','C1-SUCCESS'],
        ['C1-IID-MEAN','C1-EQ1.1-1.2'],['C1-IID-LOWER','C1-EQ1.1-1.2'],
        ['C1-EQ1.1-1.2','C1-SUCCESS'],['C1-NOREGRET','C1-SUCCESS']],
    bounded_ready_route='existing exact public proof/value audit -> complete sixteen-source reconciliation -> combined chapter canary/gates',
    no_competing_other_chapter_proof_work=True))
write(CONTRACT/'conversion-window-v1.md','Own current contract/RUN/task evidence only during draft. No production Lean or old statement/body/pin/global SGB/retrieval edit. Future proposed allowed scope after distinct review: one chapter-level external Tests canary and exact one Tests.lean import; source-qualified current coverage/reader mapping delta preserving all history, same registry/API; OWN contribution manifest and append-only OWN lifecycle entries. Any source/predicate/quantifier/target change requires new version/review. Zero new production mathematical wrappers are planned. Literal-vs-upper source correction remains separate and needs explicit chapter reconciliation verdict.')
write(CONTRACT/'proof-obligations-draft-v1.json',dict(phase='draft',
    source_objects_before=16,source_objects_after=16,source_object_acceptance=0,
    named_proof_values_to_revalidate=len(targets),new_production_math=0,
    required=['distinct full source inventory/signature review','exact public TYPE/VALUE search and axiom/fence audit',
        'current source-object/receipt/reader join','nondegenerate external wholechapter canary','root/Tests/full harness',
        'same registry and source-qualified Book map/site/current pixels','chapter reviewer decision/native shadow/scoped delivery'],
    chapter_complete=False,goal_complete=False))
write(RUN/'root-source-pixel-review-v1.json',dict(actor='/root',role='formalizer source reread',
    actually_viewed_current_original_pngs=True,rows=rows([RUN/('source-pdf'+str(n)+'-v1.png') for n in range(13,20)]),
    finding='Exact Eq1.1/1.2, fixed/true-minimum regret, literal lim display/footnote1, allinitial FTL vs halfinitial performance, Lemma1.2/Theorem1.3/printedsharp stability/harmonic/success, History+Exercises boundary personally checked.'))
write(RUN/'20_architect-draft-v1.md','Reuse exact currently public proofs. The sixteen source-object mapping is the terminal audit; selected declaration count is only evidence plumbing. Existing core/AE/completed/kernel/FTL scoped receipts are dependencies, never wholechapter certificates. Before test/reader edits require distinct reconstruction/review of all exact types, maintext enumeration, stochastic strategy-class boundary and ordinary-limit correction authority. After stabilization revalidate whole public proof VALUEs, public focused canaries and exact statement fences, then same combined shared project gates and source-qualified reader/registry. No new production wrapper, toolchain change, global frontier replacement or hidden source target weakening.')
neutral=[]
for t in targets:
    header=t['header'];short=t['name'].rsplit('.',1)[1]
    neutral.append(re.sub(r'^(theorem|lemma)\s+'+re.escape(short)+r'\b',r'\1 '+t['id'],header))
write(CONTRACT/'neutral-targets-v1.lean.txt','\n\n'.join(neutral))
write(RUN/'neutral-review-packet-v1.md',
    'Reconstruct EACH selected mathematical target A001 onward from neutral-targets-v1.lean.txt and necessary exact context-v1.lean.txt ONLY. No source identity/anchor/intention/verdict is supplied. Identify objects, quantifier order, assumptions, metric, constants/index/degenerate cases, information/probability and excluded regimes. Separate model definitions from universal performance/conditional characterizations, supplied independence from derived causal independence, fixed expected benchmark from expected hindsight minimum, upper asymptotics from ordinary limits. Definitions are context only, not new theorems. Give natural-language and LaTeX interpretations and ambiguity/required missing context. Do not read source-map/intent/fingerprint/reports or proof bodies/priors beyond supplied definition context. Disclose reused actor history and requested Astra/medium without runtime/absolute-blind/human/external attestation. Outputs ONLY blind-reconstruction-v1.md/blind-receipt-v1.json with alltwoinput RAW before/after/index hashes and target_count.')
write(RUN/'blind-inputs-v1.json',dict(rows=rows([CONTRACT/'neutral-targets-v1.lean.txt',CONTRACT/'context-v1.lean.txt']),
    target_count=len(targets),source_identity_or_prior_verdict_included=False))
fixed()
print('Full Chapter1 draft:',len(fresh),'source objects,',len(targets),'exact existing proof signatures;',len(context),'support definitions; no target accepted.',flush=True)
