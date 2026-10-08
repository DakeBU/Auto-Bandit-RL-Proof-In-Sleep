from common_v1 import *

fixed()
imports = 'import BanditRLProof.OnlineGuessingIIDBenchmark\n'
definition = '''/-- Information available before round t: one private tape and strict-past targets. -/
def privateSeedPastInformation {Ω : Type u} {Σ : Type v} [MeasurableSpace Σ]
    (S : Ω → Σ) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance
'''
context = imports + '\nopen MeasureTheory ProbabilityTheory\nuniverse u v w z\n\nnamespace BanditRL.OnlineLearning\n\n' + definition + '\nend BanditRL.OnlineLearning\n'
basic = ''' {Ω : Type u} {Σ : Type v} [MeasurableSpace Ω] [MeasurableSpace Σ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Σ) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)'''
regular = ''' {Ω : Type u} {Σ : Type v} [MeasurableSpace Ω] [MeasurableSpace Σ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Σ) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)'''
policy = '''
    (policy : (t : ℕ) → (Σ × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))'''
pred = '(fun t ω => policy t (S ω, fun i => Y i ω))'
rows = [
('independent_private_seed_pair', '''theorem independent_private_seed_pair
    {Ω : Type u} {Σ : Type v} {Χ : Type w} {Ζ : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Σ] [MeasurableSpace Χ] [MeasurableSpace Ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Σ) (X : Ω → Χ) (Y : Ω → Ζ)
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hseed : IndepFun S (fun ω => (X ω, Y ω)) μ) (hXY : IndepFun X Y μ) :
    IndepFun (fun ω => (S ω, X ω)) Y μ''', [], 'Joint-seed regrouping lemma; pairwise independence does not suffice.'),
('private_seed_past_independent', 'theorem private_seed_past_independent' + basic + ''' (t : ℕ) :
    IndepFun (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) (Y t) μ''',
 ['independent_private_seed_pair', 'history_policy_independent'], 'Derive joint seed+strict-past current independence from natural whole-process seed independence and target IID.'),
('privateSeedPastInformation_monotone', '''theorem privateSeedPastInformation_monotone
    {Ω : Type u} {Σ : Type v} [MeasurableSpace Σ]
    (S : Ω → Σ) (Y : ℕ → Ω → ℝ) :
    Monotone (privateSeedPastInformation S Y)''', [], 'Actual generated pre-reveal information grows with the history; no stochastic hypotheses needed.'),
('predictable_private_seed_independent', 'theorem predictable_private_seed_independent' + basic + '''
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ) (hP : Measurable[F] P) :
    IndepFun P (Y t) μ''', ['private_seed_past_independent'], 'Any measurable prediction in subordinate information inherits independence; current independence is not supplied.'),
('randomized_history_policy_independent', 'theorem randomized_history_policy_independent' + basic + policy + ''' (t : ℕ) :
    IndepFun (fun ω => policy t (S ω, fun i => Y i ω)) (Y t) μ''',
 ['private_seed_past_independent'], 'Actual jointly measurable policy of seed and finite strict past; empty initial history may use seed.'),
('predictable_private_seed_expectedFixed_excess', 'theorem predictable_private_seed_expectedFixed_excess' + regular + '''
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ) (hP : ∀ t, Measurable[F t] (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T''',
 ['predictable_private_seed_independent', 'expectedFixedMinimum_eq_variance', 'iid_cumulative_prediction_decomposition'],
 'General predictable-information actual causal lower producer; derive ambient measurability and L2 from information/support.'),
('randomized_history_policy_expectedFixed_excess', 'theorem randomized_history_policy_expectedFixed_excess' + regular + policy + '''
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y ''' + pred + ''' T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (policy t (S ω, fun i => Y i ω) - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y ''' + pred + ''' T''',
 ['predictable_private_seed_expectedFixed_excess'], 'Concrete seed+finite-history producer instantiates the general information endpoint; feasible only on legal histories.')]
targets = [dict(id='R' + str(i).zfill(3), name=PRE + name, header=header,
    header_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(), dependencies=deps, source_class=kind)
    for i, (name, header, deps, kind) in enumerate(rows, 1)]
write(CONTRACT / 'public-context-v1.lean', context)
write(CONTRACT / 'targets-v1.json', dict(version=1, rows=targets, new_public_proofs=7,
    new_public_definitions=1, printed_numbered_theorem_count=0, chapter_complete=False, goal_complete=False))
write(CONTRACT / 'initial-DAG-v1.json', dict(nodes=targets, first_finite_leaf='R001',
    source_terminals=['R006', 'R007'], kernel_helpers=['R001', 'R002', 'R003', 'R004', 'R005'],
    active_globalSGB_frontier_changed=False, actual_API_compilation_pending=True))
types = []
for i, (name, header, _, _) in enumerate(rows, 1):
    params, conclusion = header[len('theorem ' + name):].rsplit(' :\n', 1)
    types.append('def Q' + str(i).zfill(3) + ' : Prop := ∀' + params + ',\n' + conclusion + '\n')
checks = ['ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map',
    'MeasureTheory.Measure.prodAssoc_prod', 'MeasureTheory.Measure.map_map',
    'MeasureTheory.Measure.map_measurableEquiv_injective', 'Measurable.comap_le',
    'Measurable.of_comap_le', 'MeasurableSpace.comap_mono', 'MeasurableSpace.comap_comp',
    'ProbabilityTheory.indep_of_indep_of_le_left', 'ProbabilityTheory.IndepFun_iff_Indep',
    'ProbabilityTheory.iIndepFun.indepFun_finset', PRE + 'history_policy_independent',
    PRE + 'expectedFixedMinimum_eq_variance', PRE + 'iid_cumulative_prediction_decomposition']
write(RUN / 'draft-types-and-API-v1.lean', context + '\nopen BanditRL.OnlineLearning\nnamespace DraftSeed\n' +
    '\n'.join(types) + '\nend DraftSeed\n' + '\n'.join('#check ' + n for n in checks))
prior_context = Path('docs/contracts/online-iid-benchmark-v1/public-context-v2.lean').read_text(encoding='utf8')
prior_defs = prior_context.split('namespace BanditRL.OnlineLearning\n',1)[1].split('end BanditRL.OnlineLearning',1)[0]
neutral = 'import Mathlib\nopen MeasureTheory ProbabilityTheory\nuniverse u v w z\nnamespace NeutralSeed\n'
neutral += prior_defs.replace('expectedFixedMinimum', 'C0').replace('expectedFixedRegret', 'C1')
neutral += definition.replace('privateSeedPastInformation', 'C2')
neutral += '\n' + '\n'.join(types).replace('privateSeedPastInformation', 'C2').replace('expectedFixedRegret', 'C1')
neutral += '\nend NeutralSeed\n'
write(CONTRACT / 'neutral-context-v1.lean', neutral)
write(RUN / 'neutral-packet-v1.md', 'Reconstruct only C0–C2 complete definitions and seven closed propositions Q001–Q007, including all quantifiers and seven semantic slots. Read only this packet and neutral-context-v1.lean. No source identity, theorem name, body or prior verdict. Distinguish whole-vector joint independence from pairwise independence, comap information versus ambient measurability, strict past and empty history, all-seed/legal-history bounds versus almost-sure bounds, probability and integrations, fixed-comparator order, consumer versus produced causality. State exactly which side information classes and limits are covered; no kernel representation or independence assumption strengthening. Prior staged actor history disclosed; no absolute-blind/human/external/runtime attestation. Reconstruct, do not prove or accept.\n\n```lean\n' + neutral + '```\n')
write(RUN / 'neutral-inputs-v1.json', dict(rows=[dict(path=p.resolve().as_posix(), sha256=sha(p)) for p in
    [RUN / 'neutral-packet-v1.md', CONTRACT / 'neutral-context-v1.lean']], terminal_count=7, complete_definitions=3))
requirements = [
('R1', 'Seed is independent of the WHOLE process, and target family jointly IID; pairwise seed-target independence cannot replace this. Current independence must be derived.'),
('R2', 'Generated information is comap of seed+STRICT PAST; monotonicity is proved. General pre-reveal subfields are subordinate to this information; no arbitrary future-correlated side information or general kernel representation claim.'),
('R3', 'Concrete jointly measurable seed+history policy instantiates general predictable endpoint. At t0 history is empty but seed is allowed; prediction cannot see current/future targets.'),
('R4', 'Retain probability, measurable targets, same laws, a.s.unit support; derive ambient measurability and L2. Legal cube-only policy feasibility for every seed, no global off-cube strengthening.'),
('R5', 'Literal minimum is minimum of expected FIXED losses outside expectation. Same-prefix expected excess identity and nonnegativity, no hindsight minimum or pathwise nonnegativity.'),
('R6', 'Actual nondegenerate independent private seed/IID targets and XOR-style boundary canaries; T0 empty extension, source1..T=Lean0..T−1. Finite result only; source asymptotic successfulness remains REQUIRED.'),
('R7', 'Seven derived producer/interface proofs and one definition, not seven printed results or new rates. Shared root/Tests/fullharness/kernel/canary/fences/site/native/semantic review gates separate; original16/null/C1C2open/3–16unenumerated/appendices/oldfiveaudits/GoalACTIVE; OPENdraftPR194 exact b08 stack is not main/live.')]
write(CONTRACT / 'reader-requirements-v1.json', [dict(id=i, requirement=t) for i,t in requirements])
write(CONTRACT / 'contract-v1.md', '''# Draft v1: independent private tape and predictable strict-past IID guessing

Frozen source Orabona arXiv1912.13213v10/2026-06-21, PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed1–2/PDF13–14: predict before reveal; IID variance cannot be beaten in expectation; rewrite with minimum of EXPECTED FIXED loss. Fresh source text and exact cached page pixels read/viewed by ROOT. Current source item scope extends prior deterministic-history core to arbitrary measurable private tape independent of WHOLE target process and any prediction measurable in subordinate seed+strict-past information.

Seven exact prospective headers/one complete generated-information definition. R001 general joint-law regrouping helper; R002 produces seed+past/current independence from natural whole-process seed independence and joint IID; R003 proves actual generated information monotone. R004 proves current independence for measurable predictions in any subordinate sigma field; no given one-step regret or given prediction-current independence. R005 concrete jointly measurable seed+past policy independence. R006 cumulative literal expected-fixed excess identity and nonnegativity with a.s.feasible predictable predictions; derive ambient measurability and L2. R007 instantiates that information endpoint with actual policy(seed, finite strict past), joint measurability and feasibility only on legal history cube for every seed. The abstract F family need not itself be monotone; each F_t is pre-reveal subordinate. The enclosing generated information is monotone. No side-information leak, no sigma-field completion/AE-predictability or representation theorem for every randomized kernel is claimed.

Seed may encode an entire private random tape in any measurable space; it is independent of the whole target vector, not merely each coordinate. Target variables are jointly independent and identically distributed, measurable and a.s.[0,1]. Law-known mean benchmark from PR194 remains an oracle, not an unknown-law algorithm. Exact benchmark minE remains outside expectation; no E[min], pathwise nonnegative regret or high-probability/asymptotic result. t0 empty prefix is a disclosed extension; first prediction may depend on the tape. Source rounds1..T map0..T−1. Need actual independent seed+infinite IID nondegenerate canary and a joint-dependence/pairwise pitfall witness.

Single lower route. Mathematical progress is causal independence frontier then exact cumulative terminals R006/R007, not number of interfaces. Existing shared Lean/Lake/mathlib/root registry; old bodies/contracts and global activeSGBfrontier unchanged. Distinct reused staged decoder/source reviewer required before proving; no independent human/external or complete runtime enforcement/model setting attestation. Required root/Tests/fullharness, public canary, axiom audit, statement identities/fences, source/reader review, site and native own frontier gates before acceptance; reviewable PR delivery separate. Original16C1source items/proof-totalnull retained, full C1/C2 remain open; source asymptotic-success equivalence and five old main-relative source-module audits unwaived,3–16unenumerated/necessaryappendicesrequired/GoalACTIVE. Exact OPENdraft/unmergedPR194 b08 stack; no main/live/merge/deploy/retirement.
''')
write(CONTRACT / 'source-card-v1.json', dict(source_url='https://arxiv.org/pdf/1912.13213v10', PDF_sha256=PDF_SHA,
    anchors=[dict(printed_page=p,pdf_page=p+12) for p in [1,2]],
    intent='Actual independent private-tape and predictable strict-past IID cumulative variance lower producer.',
    delta=['Explicit measurable private-seed formulation of causal randomized strategy; source informal, not numbered.',
        'Subordinate pre-reveal information; no arbitrary side information, completed fields, AE-measurable factorization or kernel representation.',
        'a.s.support and L2 derived; legal history only for all seed values.',
        'T0 extension; finite result only, asymptotic mandatory separately.'],
    source_package_accepted=False, chapter_complete=False, goal_complete=False))
source_rows = [dict(path=(RUN / ('fresh-pinned-pdf'+str(p)+'-text-v1.txt')).as_posix(),
    sha256=sha(RUN / ('fresh-pinned-pdf'+str(p)+'-text-v1.txt'))) for p in [13,14]]
source_rows += [dict(path=(RUN / ('source-pdf'+str(p)+'-v1.png')).as_posix(),
    sha256=sha(RUN / ('source-pdf'+str(p)+'-v1.png'))) for p in [13,14]]
write(CONTRACT / 'source-fingerprint-v1.json', dict(version=1, PDF_sha256=PDF_SHA, source_rows=source_rows,
    target_hashes={r['id']:r['header_sha256'] for r in targets}, definition_sha256=hashlib.sha256(definition.encode()).hexdigest()))
write(CONTRACT / 'conversion-window-v1.md', 'Source causal private randomness -> measurable private tape independent whole IID stream -> generated strict-past comap and subordinate information -> derived current independence -> actual L2 and cumulative expected-fixed benchmark. Never replace joint independence by pairwise; no arbitrary full-future algorithm, performance certificate, min/expectation exchange, off-cube feasibility or asymptotic promotion. Source printed1–2/PDF13–14 only; seven derived proof interfaces, not seven source theorems.')
write(CONTRACT / 'proof-obligations-draft-v1.json', dict(version=1, status='draft', obligations=[
    dict(id=r['id'], name=r['name'], dependencies=r['dependencies'], header_sha256=r['header_sha256'],
         status='unproved', required=True) for r in targets],
    required_followup=['source asymptotic-success equivalence', 'five old module source audits', 'C1/C2 full gates', 'Chapters3–16/appendix enumeration and closure'], chapter_complete=False, goal_complete=False))
ledger = load('docs/contracts/online-iid-benchmark-v1/chapter-one-source-ledger-accepted-v4.json')
assert len(ledger['maintext_items']) == 16 and ledger['chapter_mandatory_proof_total'] is None
ledger['prior_effective_ledger'] = dict(path='docs/contracts/online-iid-benchmark-v1/chapter-one-source-ledger-accepted-v4.json',
    sha256=sha('docs/contracts/online-iid-benchmark-v1/chapter-one-source-ledger-accepted-v4.json'))
ledger['current_randomized_IID_package'] = dict(status='draft', exact_base_PR=194, exact_base_head=BASE,
    terminal_ids=[r['id'] for r in targets], chapter_complete=False, source_package_accepted=False)
write(CONTRACT / 'chapter-one-source-ledger-draft-v1.json', ledger)
gate('draft-types-and-API-v1', 'lake', 'env', 'lean', RUN / 'draft-types-and-API-v1.lean')
gate('neutral-types-v1', 'lake', 'env', 'lean', CONTRACT / 'neutral-context-v1.lean')
fixed()
print('Exact seven draft propositions and three neutral definitions typechecked; bodies remain unproved.')
