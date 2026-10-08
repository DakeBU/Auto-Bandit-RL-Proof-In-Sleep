from common_v1 import *

fixed()
regular = ''' {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)'''
causal = regular + '''
    (hind : iIndepFun Y μ)
    (policy : (t : ℕ) → ((↑(Finset.range t) : Type) → ℝ) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t z, policy t z ∈ Set.Icc (0 : ℝ) 1)'''
history_prediction = '(fun t ω => policy t (fun i => Y i ω))'
headers = [
('expected_fixed_prefix_decomposition', 'theorem expected_fixed_prefix_decomposition' + regular + ''' (T : ℕ) (u : ℝ) :
    (∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) =
      (T : ℝ) * variance (Y 0) μ +
        (T : ℝ) * (u - ∫ ω, Y 0 ω ∂μ)^2''', [], 'Derived expected-fixed-prefix decomposition; no independence required.'),
('expected_fixed_prefix_minimum', 'theorem expected_fixed_prefix_minimum' + regular + ''' (T : ℕ) :
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
        Set.Icc (0 : ℝ) 1) ((T : ℝ) * variance (Y 0) μ)''', ['expected_fixed_prefix_decomposition'], 'Actual feasible distribution mean produces image membership and lower comparisons.'),
('expectedFixedMinimum_eq_variance', 'theorem expectedFixedMinimum_eq_variance' + regular + ''' (T : ℕ) :
    expectedFixedMinimum μ Y T = (T : ℝ) * variance (Y 0) μ''', ['expected_fixed_prefix_minimum'], 'Literal real infimum of expected fixed losses, now attained; not expectation of hindsight minimum.'),
('iid_cumulative_prediction_decomposition', 'theorem iid_cumulative_prediction_decomposition' + regular + '''
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, MemLp (prediction t) 2 μ)
    (hInd : ∀ t, IndepFun (prediction t) (Y t) μ) (T : ℕ) :
    (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
      (T : ℝ) * variance (Y 0) μ =
        ∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ''', ['independent_prediction_square'], 'Intermediate consumer only; two genuine causal producers follow.'),
('history_policy_expectedFixed_excess', 'theorem history_policy_expectedFixed_excess' + causal + ''' (T : ℕ) :
    expectedFixedRegret μ Y ''' + history_prediction + ''' T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y ''' + history_prediction + ''' T''',
    ['expectedFixedMinimum_eq_variance', 'iid_cumulative_prediction_decomposition', 'history_policy_independent'],
    'Actual deterministic measurable bounded strict-history policy; current-target independence derived, not supplied.'),
('meanPredict_expectedFixed_excess', 'theorem meanPredict_expectedFixed_excess' + regular + '''
    (hind : iIndepFun Y μ) (T : ℕ) :
    expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (meanPredict (fun i => Y i ω) t - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y (fun t ω => meanPredict (fun i => Y i ω) t) T''',
    ['expectedFixedMinimum_eq_variance', 'iid_cumulative_prediction_decomposition', 'meanPredict_independent', 'meanPredict_measurable', 'meanPredict_mem'],
    'Actual initial1/2 strict-past shared predictor; MemLp produced from a.s. support, no old pointwise strengthening.'),
('constant_mean_expectedFixed_excess_zero', 'theorem constant_mean_expectedFixed_excess_zero' + regular + ''' (T : ℕ) :
    (∫ ω, Y 0 ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      expectedFixedRegret μ Y (fun _ _ => ∫ ω, Y 0 ω ∂μ) T = 0''',
    ['expected_fixed_prefix_minimum', 'expectedFixedMinimum_eq_variance', 'expected_fixed_prefix_decomposition'],
    'Distribution-known fixed mean attains benchmark; not an executable learner discovering an unknown mean.'),
('history_policy_normalized_expectedFixed_excess', 'theorem history_policy_normalized_expectedFixed_excess' + causal + '''
    (T : ℕ) (hT : 0 < T) :
    (∫ ω, ∑ t ∈ Finset.range T, (policy t (fun i => Y i ω) - Y t ω)^2 ∂μ) /
        (T : ℝ) - variance (Y 0) μ =
      expectedFixedRegret μ Y ''' + history_prediction + ''' T / (T : ℝ)''',
    ['expectedFixedMinimum_eq_variance', 'normalized_excess'], 'Source finite-horizon normalization, T>0; asymptotic success equivalence remains separately required.')]
definitions = '''noncomputable def expectedFixedMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def expectedFixedRegret {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    expectedFixedMinimum μ Y T
'''
imports = 'import BanditRLProof.OnlineLearningHistory\nimport Mathlib.Order.ConditionallyCompleteLattice.Basic\n'
context = imports + '\nopen MeasureTheory ProbabilityTheory\n\nnamespace BanditRL.OnlineLearning\n\n' + definitions + '\nend BanditRL.OnlineLearning\n'
write(CONTRACT / 'public-context-v1.lean', context)
rows = [dict(id='I' + str(i).zfill(3), name=PRE + name, header=header,
    header_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(), dependencies=deps, source_class=classification)
    for i, (name, header, deps, classification) in enumerate(headers, 1)]
write(CONTRACT / 'targets-v1.json', dict(version=1, rows=rows, new_public_proofs=8, new_public_definitions=2,
    printed_numbered_theorem_count=0, chapter_complete=False, goal_complete=False))
write(CONTRACT / 'initial-DAG-v1.json', dict(nodes=rows, first_finite_leaf='I001',
    shared_consumer='I004', real_consumers=['I005 genuine strict-history policies', 'I006 actual meanPredict'],
    imported_producers=['history_policy_independent', 'meanPredict_independent', 'meanPredict_measurable', 'meanPredict_mem'],
    actual_API_compilation_pending=True, globalSGB_not_changed=True))
types = []
for i, (name, header, _, _) in enumerate(headers, 1):
    params, conclusion = header[len('theorem ' + name):].rsplit(' :\n', 1)
    types.append('def Q' + str(i).zfill(3) + ' : Prop := ∀' + params + ',\n' + conclusion + '\n')
checks = ['expected_square_decomposition', 'independent_prediction_square', 'history_policy_independent',
    'meanPredict_independent', 'meanPredict_measurable', 'meanPredict_mem', 'source_mean_optimal',
    'iid_meanPredict_excess', 'normalized_excess']
checks_text = '\n'.join('#check ' + PRE + x for x in checks)
checks_text += '\n#check MeasureTheory.integral_finset_sum\n#check MeasureTheory.integral_mono_ae\n#check MeasureTheory.integral_nonneg_of_ae\n#check ae_all_iff\n#check IsLeast.csInf_eq\n#check MemLp.integrable_sq\n'
write(RUN / 'draft-types-and-API-v1.lean', context + '\nopen BanditRL.OnlineLearning\nnamespace DraftExpected\n' +
    '\n'.join(types) + '\nend DraftExpected\n' + checks_text)
neutral_definitions = '''import Mathlib
open MeasureTheory ProbabilityTheory
namespace NeutralExpected
noncomputable def C2 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C3 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C2 y t
'''
neutral_definitions += definitions.replace('expectedFixedMinimum', 'C0').replace('expectedFixedRegret', 'C1')
neutral_types = '\n'.join(types).replace('expectedFixedMinimum', 'C0').replace('expectedFixedRegret', 'C1').replace('meanPredict', 'C3')
neutral = neutral_definitions + '\n' + neutral_types + '\nend NeutralExpected\n'
write(CONTRACT / 'neutral-context-v1.lean', neutral)
write(RUN / 'neutral-packet-v1.md',
    'Reconstruct only four complete definitions C0–C3 and eight closed propositions Q001–Q008 in natural language, LaTeX and seven semantic slots. '
    'No source identity, proof bodies, desired verdict or prior acceptance. Distinguish the order of infimum and integration, actual image/IsLeast membership, '
    'a.s. versus pointwise bounds, probability normalization/same-law versus independence, supplied independent-prediction consumer versus explicit finite strict-history and fixed first-output predictor, '
    'oracle distribution mean versus unknown-distribution learner, zero/positive horizons and normalization. Prior staged actor history disclosed, no absolute-blind/human/external/runtime attestation. '
    'Do not read any other files/source identities. Reconstruct rather than prove or accept.\n\n```lean\n' + neutral + '```\n')
write(RUN / 'neutral-inputs-v1.json', dict(rows=[dict(path=p.resolve().as_posix(), sha256=sha(p)) for p in
    [RUN / 'neutral-packet-v1.md', CONTRACT / 'neutral-context-v1.lean']], terminal_count=8, definition_count=4))
write(CONTRACT / 'contract-v1.md', '''# Version1 draft: expected fixed-loss minimum and causal IID cumulative benchmark

Pinned Orabona arXiv1912.13213v10/2026-06-21, PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed1/PDF13 IID mean/variance oracle, cannot-beat benchmark, nonnegative cumulative (1.1), positive-horizon average (1.2); printed2/PDF14 rewriting as minimum of EXPECTED FIXED cumulative loss. ROOT actually read original caches and viewed both full pages, rehashed pinned PDF and freshly extracted those original PDF pages. PNG caches are exact provenance copies, not fresh rerenders.

Eight exact prospective theorem headers plus two complete definitions in targets-v1/public-context-v1. General probability space, measurable real observations with almost-sure[0,1] support, all observations identically distributed toY0. Identical law suffices for fixed comparator decomposition/minimum, without independence. Derive all needed L2/integrability; source[0,1] law does not justify strengthening a.s. bounds to every sample point. Produce distribution mean feasibility and actual IsLeast of the generally infinite comparator-loss image with valueT*variance, before using csInf_eq. No supplied minimizer or totalized-inf escape. T0 empty-prefix extension has minimum0 and no uniqueness. Fixed comparator quantifier remains OUTSIDE integral, same stream and horizon throughout; this is NOT expectation of a hindsight minimum.

For causal performance add actual joint independence of target variables. I004 alone is an explicit intermediate consumer assuming current-target independence and L2 predictions; TWO downstream producers must derive them. I005 policies accept only the finite strict-past tuple, are measurable and bounded for all tuples, initial tuple empty; current-target independence is derived from actual history_policy_independent. I006 uses actual shared meanPredict (initial1/2, later strict-past empirical mean), actual meanPredict_independent/measurable/mem and derives L2 from a.s. observation bounds. No receiving entire future realization as algorithm input, no arbitrary P performance claim, no assumed one-step regret certificate. Arbitrary supplied P in standalone definitions/I004 is representation/consumer only and does not guarantee causal/integrable/nonnegative behavior.

Constant distribution mean is a benchmark knowing the distribution; no claim an unknown-distribution algorithm computes it. Its zero excess gives genuine attainability alongside the actual causal lower producer. Source rounds1..T=Lean0..T−1. Finite positive-horizon average identity uses the same expectedFixedRegret andT*variance; T>0 is essential. Asymptotic successfulness/sublinear-to-vanishing equivalence remains REQUIRED separately. The deterministic strict-history policy representation does not by itself cover arbitrary randomized strategies or abstract filtration policies; independent external randomization/source-wide coverage audit remains REQUIRED, not excluded. No high-probability/pathwise regret nonnegativity/min-expectation swap/rate claims.

Only bounded minimum plus deterministic strict-history and actual-mean IID cumulative benchmark may advance. Eight derived producers/representation/integration statements are not eight printed theorems; I004 cannot complete the target alone. Original16C1items/proof-totalnull preserved, full C1/C2 incomplete,3–16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. Five old main-relative module audits remain unwaived until separately reviewed relevant bodies and complete chapter gates. Distinct reused staged decoder/source reviewer required before proving; no human/external/runtime-model or complete single-runtime enforcement claim. Root/Tests/fullharness/actualkernel/canary/statement/DAG/reader/site/FINAL/native/PR evidence separately required. Exact OPENdraft/unmergedPR193 stack, no main/live/merge/deploy/retirement.
''')
requirements = [
('R1', 'Keep minimum of EXPECTED FIXED cumulative loss outside integration; never replace it by expectation of the hindsight minimum or pathwise square regret.'),
('R2', 'Preserve probability normalization, measurable observations, a.s. unit support and derived L2/integrability; no silent pointwise strengthening or totalized-integral performance claim.'),
('R3', 'Produce actual feasible distribution-mean image membership and all lower comparisons before real csInf; generally infinite image, T0 empty extension without uniqueness.'),
('R4', 'Same-law fixed benchmark needs no independence; causal performance requires joint target independence and actual current-target independence derived from strict history or meanPredict.'),
('R5', 'I004 is only a supplied-independent-prediction intermediate with two real causal consumers; standalone definitions/arbitrary traces cannot certify algorithm existence or nonnegative expected excess.'),
('R6', 'Actual meanPredict starts at1/2 then exact strict past; fixed distribution-mean optimum knows the law and is not an unknown-law learning implementation.'),
('R7', 'Deterministic finite-history policy scope is explicit; randomized/general filtration coverage remains mandatory audit work. Do not label all strategies or full source/chapter complete from this package.'),
('R8', 'Keep source1..T/Lean0..T−1, T0 extension, positiveT average denominators, actual nondegenerate IID canaries and same-prefix processes; no asymptotic-success or high-probability claim.'),
('R9', 'Reuse shared Lean graph/registry and exact old declarations; source, draft/type, actual body, kernel/canary/combined/harness/site/FINAL/native/PR gates separate. Original16C1items/proof-totalnull, five old module audits, C1/C2/program open,3–16/appendices required; OPENunmergedPR193 stack is not main/live.')]
write(CONTRACT / 'reader-requirements-v1.json', [dict(id=i, requirement=text) for i, text in requirements])
write(CONTRACT / 'source-card-v1.json', dict(source_url='https://arxiv.org/pdf/1912.13213v10', PDF_sha256=PDF_SHA,
    anchors=[dict(printed_page=p, pdf_page=p+12) for p in [1,2]],
    intent='Produce the literal minimum of expected fixed cumulative square loss, actual deterministic strict-history/meanPredict cumulative IID nonnegative excess and attained mean benchmark.',
    delta=['Explicit probability/measurability/a.s. support from source unit-interval distribution', 'Same-law suffices for the fixed minimum',
        'T0 empty-prefix extension without uniqueness', 'Deterministic finite-history scope; randomized/abstract-filtration source-wide extension REQUIRED',
        'Finite normalization only; asymptotic successfulness REQUIRED separately', 'Eight derived declarations, not eight printed source theorems'],
    source_package_accepted=False, chapter_complete=False, goal_complete=False))
source_rows = [dict(path=(RUN / ('source-pdf' + str(page) + '-v1.' + ext)).as_posix(), sha256=sha(RUN / ('source-pdf' + str(page) + '-v1.' + ext)))
    for page in [13,14] for ext in ['txt','png']]
write(CONTRACT / 'source-fingerprint-v1.json', dict(version=1, PDF_sha256=PDF_SHA, source_rows=source_rows,
    targets_sha256=sha(CONTRACT / 'targets-v1.json'), public_context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    source_card_sha256=sha(CONTRACT / 'source-card-v1.json')))
ledger = load('docs/contracts/online-square-minimum-v1/chapter-one-source-ledger-accepted-v2.json')
assert len(ledger['maintext_items']) == 16 and ledger['chapter_mandatory_proof_total'] is None
ledger['version'] = 3
ledger['prior_effective_ledger'] = dict(path='docs/contracts/online-square-minimum-v1/chapter-one-source-ledger-accepted-v2.json',
    sha256=sha('docs/contracts/online-square-minimum-v1/chapter-one-source-ledger-accepted-v2.json'))
ledger['source_package_accepted'] = False
ledger['current_package_only'] = 'Current eight-target expected-fixed-minimum/deterministic causal IID benchmark DRAFT; prior square-minimum acceptance preserved, no current proof/source acceptance.'
ledger['current_planned_new_proofs'] = 8
ledger['current_planned_new_definitions'] = 2
ledger['remaining_randomized_or_abstract_filtration_causal_benchmark'] = 'REQUIRED source-wide coverage audit; deterministic finite-history package alone does not close full cannot-beat assertion.'
ledger['remaining_source_asymptotic_success_equivalence'] = 'REQUIRED separately, finiteT normalization alone cannot close source sublinear/vanishing equivalence.'
for item in ledger['maintext_items']:
    if item['source_id'] == 'C1-REGRET':
        item['square_minimum_subobligation'] = 'Accepted and delivered OPEN/unmergedPR193 exactbf9f896cdfebb2b836dacb01f3d4b209466c2100; literal pathwise minimum only, historical evidence preserved.'
    if item['source_id'] in ['C1-IID-MEAN', 'C1-IID-LOWER', 'C1-EQ1.1-1.2']:
        item['current_IID_subobligation'] = 'Current eight-target contract DRAFT, actual causal producers/a.s. support required; no acceptance. Randomized/source asymptotic/full chapter coverage still required.'
ledger['chapter_complete'] = ledger['goal_complete'] = False
write(CONTRACT / 'chapter-one-source-ledger-draft-v1.json', ledger)
write(RUN / 'proof-obligations-draft-v1.json', dict(version=1, rows=[dict(id=r['id'], declaration=r['name'], status='draft',
    dependencies=r['dependencies'], frozen_header_sha256=r['header_sha256']) for r in rows],
    remaining_required=['randomized/source-wide causal coverage audit', 'source asymptotic successfulness equivalence',
        'five main-relative module audits', 'full C1/C2', '3–16/necessaryappendices'], chapter_complete=False, goal_complete=False))
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + ('\n\n## Draft exact IID benchmark contract v1\n\n' +
        (CONTRACT / 'contract-v1.md').read_text(encoding='utf8') + '\nFrozen eight prospective headers: ' +
        sha(CONTRACT / 'targets-v1.json') + '; source/draft-type/body acceptance pending.\n').encode('utf8'))
write(RUN / 'native-reference-index-v1.py',
    "from common_v1 import *\nsys.path.insert(0,str(ROOT/'tools'))\nimport bandit\nbandit.RETRIEVAL_INDEX_DIR=RUN/'native-reference-index'\nraise SystemExit(bandit.main(['reference-index']))\n")
gate('actual-reference-index-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-reference-index-v1.py')
for label, command in [('mathlib-cards','list-mathlib'), ('paper-cards','list-papers'), ('weapon-cards','list-weapons')]:
    native(label + '-v1', command)
for query in ['expected_square_decomposition', 'history_policy_independent', 'expectedFixedMinimum', 'independent_prediction_square']:
    native('memory-' + query + '-v1', 'search-memory', query)
    native('declarations-' + query + '-v1', 'list-lean-decls', query, '--statement')
gate('actual-draft-types-and-API-v1', 'lake', 'env', 'lean', RUN / 'draft-types-and-API-v1.lean')
gate('actual-neutral-types-v1', 'lake', 'env', 'lean', CONTRACT / 'neutral-context-v1.lean')
fixed()
print('Draft eight Prop types/four definitions compiled; distinct blind reconstruction/source stabilization pending.')
