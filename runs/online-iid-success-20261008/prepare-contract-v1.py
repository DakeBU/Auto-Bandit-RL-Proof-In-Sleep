from common_v1 import *
fixed()
stochastic = '''{Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)'''
seeded = stochastic.replace('{Ω : Type u}', '{Ω : Type u} {Seed : Type v}').replace(
    '[MeasurableSpace Ω]', '[MeasurableSpace Ω] [MeasurableSpace Seed]') + '''
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t))
    (hpb : ∀ t s z, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) →
      policy t (s, z) ∈ Set.Icc (0 : ℝ) 1)'''
loss = '(∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ)'
mean = '(fun t ω => meanPredict (fun i => Y i ω) t)'
zero = 'atTop (nhds (0 : ℝ))'
conclusions = [
    '''(fun T => total T - (T : ℝ) * c) =o[atTop] (fun T : ℕ => (T : ℝ)) ↔
      Tendsto (fun T => total T / (T : ℝ) - c) atTop (nhds (0 : ℝ))''',
    f'''let prediction := fun t ω => policy t (S ω, fun i => Y i ω)
    (∀ T, 0 ≤ expectedFixedRegret μ Y prediction T) ∧
      ((fun T => expectedFixedRegret μ Y prediction T) =o[atTop]
          (fun T : ℕ => (T : ℝ)) ↔
        Tendsto (fun T => {loss} / (T : ℝ) - variance (Y 0) μ) {zero}) ∧
      (Tendsto (fun T => {loss} / (T : ℝ) - variance (Y 0) μ) {zero} ↔
        Tendsto (fun T => (∑ t ∈ Finset.range T,
          ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) / (T : ℝ)) {zero})''',
    f'''expectedFixedRegret μ Y {mean} T ≤ 4 + 4 * Real.log T''',
    f'''Tendsto (fun T => expectedFixedRegret μ Y {mean} T / (T : ℝ)) {zero} ∧
      (fun T => expectedFixedRegret μ Y {mean} T) =o[atTop]
        (fun T : ℕ => (T : ℝ))'''
]
names = ['centered_total_sublinear_iff_average', 'randomized_history_policy_success_iff',
    'meanPredict_expectedFixed_upper', 'meanPredict_iid_success']
binders = ['(total : ℕ → ℝ) (c : ℝ)', seeded,
    stochastic + ' (T : ℕ) (hT : 0 < T)', stochastic + ' (hind : iIndepFun Y μ)']
targets = [dict(id='S00'+str(i+1),name=PRE+n,binders=b,conclusion=c,
    header='theorem '+n+' '+b+' :\n    '+c,source_anchor=(
      'printed1/PDF13 equations1.1-1.2 success equivalence' if i<2 else
      'derived stochastic application of printed4/PDF16 Theorem1.3; not a separately numbered source result'))
    for i,(n,b,c) in enumerate(zip(names,binders,conclusions))]
write(CONTRACT/'targets-v1.json',dict(version=1,status='draft',targets=targets,
    no_proof_bodies=True,chapter_complete=False,goal_complete=False))
imports = '''import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Filter Asymptotics
universe u v
namespace BanditRL.OnlineLearning
'''
props = '\n\n'.join('def '+t['id']+' : Prop := ∀ '+t['binders']+',\n    '+t['conclusion'] for t in targets)
write(CONTRACT/'public-context-v1.lean',imports+'\n'+props+'\n\nend BanditRL.OnlineLearning\n')
old = Path('docs/contracts/online-randomized-iid-v1/neutral-context-v2.lean').read_text(encoding='utf8')
neutral = old[:old.index('/-- Information available')].replace('open MeasureTheory ProbabilityTheory',
    'open MeasureTheory ProbabilityTheory Filter Asymptotics').replace('namespace NeutralSeed','namespace NeutralLimit')
neutral += '''noncomputable def C2 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then (1 : ℝ) / 2 else (∑ i ∈ Finset.range t, y i) / (t : ℝ)

'''
for t in targets:
    text = 'def Q'+t['id'][1:]+' : Prop := ∀ '+t['binders']+',\n    '+t['conclusion']
    neutral += text.replace('expectedFixedRegret','C1').replace('meanPredict','C2')+'\n\n'
neutral += 'end NeutralLimit\n'
write(CONTRACT/'neutral-context-v1.lean',neutral)
apis = ['Asymptotics.isLittleO_iff_tendsto\'', 'Asymptotics.IsLittleO.tendsto_div_nhds_zero',
    'Filter.tendsto_congr\'', 'Filter.Tendsto.congr\'', 'squeeze_zero\'',
    'MeasureTheory.integrable_finset_sum', 'MeasureTheory.integral_mono_ae',
    'MeasureTheory.integral_sub', 'BanditRL.OnlineLearning.normalized_excess',
    'BanditRL.OnlineLearning.expected_fixed_prefix_decomposition',
    'BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance',
    'BanditRL.OnlineLearning.meanPredict_expectedFixed_excess',
    'BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess',
    'BanditRL.OnlineLearning.theorem_1_3', 'BanditRL.OnlineLearning.empiricalMean_minimizes',
    'BanditRL.OnlineLearning.meanPredict_measurable', 'BanditRL.OnlineLearning.meanPredict_mem',
    'Real.tendsto_pow_log_div_mul_add_atTop','Filter.tendsto_natCast_atTop_atTop']
write(RUN/'typed-api-search-v1.lean',imports+'\nend BanditRL.OnlineLearning\n'+
    '\n'.join('#check '+a for a in apis)+'\n'+
    '\n'.join('#print axioms '+a for a in apis if a not in ['squeeze_zero\'']))
write(CONTRACT/'contract-v1.md','''Draft S001–S004, Orabona v10 SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17.

S001: signed real centered total o(T) iff its average centered loss tends to zero. Generic adapter is a generalization of the source arithmetic; no stochastic/IID/convergence assumptions, noA0/c restrictions. Eventual positive horizons avoid zero denominator; atT0 two expressions may differ.
S002: same single infinite measurable jointIID/same-law/a.s.[0,1] target stream, private seed measurable and independent of WHOLE stream, policy jointly measurable and feasible for everyseed on legal strictpast histories. MinEXPECTEDFIXEDloss outside expectation. Produce nonnegative finite excess using existing actual causalPR195, and equivalences among excess=o(T), lossaverage-variance→0 and MSE-Cesaro→0. These equivalences do NOT assert any arbitrary policy converges. Bounded explicit seed model only, source fullclass coverage unresolved; private tape may have arbitrary measurable codomain and emptyhistory canuse seed.
S003: actual firsthalf/strictpastmeanPredict under measurable same-law/a.s.unit targets andT≥1 has expectedfixedregret≤4+4logT. No independence assumption. Source Theorem1.3 usedpathwise thenintegrated versus fixedpopulationmean, not expected hindsight minimum. This is a derived application, not a new numberedsource theorem. Deriveintegrability; doNOTrequirepointwiseallomega support. Algorithm neverknowsμ/mean/horizon.
S004: addjointIID toS003; source causal nonnegative lower+actual upper produce ordinary normalized zero limit AND signedexcesslittle-o. No assumedconvergence, no highprobability/almostsure/minimax/newrate/general-kernel result. Existing adversarialupper-epsilonNoRegret alone is insufficient, and remains distinct.

All exact Lean binders/conclusions reside targets-v1.json. Four source-facing declarations/two actual theorem edges, original16C1objects/null retained, C1/C2open;3–16unenumerated. Five oldmain-relativemodulecontribution audits, generalrandomization coverage and wholechapter gate REQUIRED. No source exclusion for difficulty. No proof bodies until independentdecoder/sourcecontract review; every targetrepairversioned. Staged automated actors reused, requestedAstra/medium notruntimeattested, nothuman/external/absolute-blind.
''')
write(CONTRACT/'initial-DAG-v1.json',dict(nodes=['S001','S002','S003','S004'],
    planned_edges=[['normalized_excess','S001'],['isLittleO_iff_tendsto\'','S001'],
        ['randomized_history_policy_expectedFixed_excess','S002'],['S001','S002'],
        ['theorem_1_3','S003'],['empiricalMean_minimizes','S003'],
        ['expected_fixed_prefix_decomposition','S003'],['meanPredict_expectedFixed_excess','S004'],
        ['S003','S004'],['isLittleO_iff_tendsto\'','S004']],
    ready_leaves=['S001','S003'],edge_status='planned, not compiler dependency claims'))
write(CONTRACT/'conversion-window-v1.md','Only four frozen headers in targets-v1.json may become production proof bodies in OnlineGuessingIIDSuccess.lean. Imports/scopednames fixed; proof tactics/helpers only with recorded architecture. Canary may instantiate actual publicvalues, no axioms/sorry/native shortcuts. Publicroot/Tests/reader/globalregistry updates only after BODYstage and explicit bounded integration permissions. All prior production/readers/targets/pins/globalSGB immutable. Targetchanges require newversion/roundtrip, never proof-only silent weakening.')
write(CONTRACT/'proof-obligations-draft-v1.json',dict(task_id=TASK,stage='draft',
    targets=[dict(id=t['id'],name=t['name'],status='unproved',terminal=t['conclusion']) for t in targets],
    required=['contract-roundtrip','focused-build','four-public-instantiations','nondegenerate-public-canary',
        'fixed-header-hash','body-semantic-review','axiom-audit','combined-root','combined-Tests',
        'full-harness','own-shadow-globalSGB-unchanged','contributor-PR-base','reader/site/registry/visual',
        'candidate-review','native-acceptance','scoped-commit-push-draftPR'],
    whole_goal_required_unclosed=['five-old-module-audits','full-randomization-information-source-coverage',
        'whole-C1gate','C2remaining','C3-C16enumeration-andproofs','required-appendices'],
    chapter_complete=False,goal_complete=False))
write(CONTRACT/'source-fingerprint-v1.json',dict(PDF=str(PDF),sha256=PDF_SHA,
    version='arXiv1912.13213v10 2026-06-21',printed_pages=[1,2,4],pdf_pages=[13,14,16],
    equations=['1.1','1.2'],reused_source_result='Theorem1.3',
    actual_source_text_sha256={str(p):sha(RUN/('source-pdf'+str(p)+'-text-v1.txt')) for p in [13,14,16]},
    ROOT_actual_pixel_viewed=[13,14,16],source_modified=False))
write(CONTRACT/'source-statement-fingerprint-v1.json',dict(source=sha(CONTRACT/'source-fingerprint-v1.json'),
    whole_target_file=sha(CONTRACT/'targets-v1.json'),
    headers={t['id']:hashlib.sha256(t['header'].encode('utf8')).hexdigest() for t in targets},
    public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    neutral_context_sha256=sha(CONTRACT/'neutral-context-v1.lean'),status='draft'))
write(RUN/'blind-packet-v1.md','''Reconstruct ONLY neutral-context-v1.lean Q001–Q004 and whole C0,C1,C2definitions. Do not inspect source/publiccontext/priorverdicts/proofs. Provide all seven semantic slots and natural-language/LaTeX; explicitly distinguish conjunctions/equivalence from produced convergence and all horizon zero semantics. Reused actor has previous project history: disclose rather than claim absolute blindness. Requested GPT-6 Astra/medium, no escalation/runtime attestation. Only create blind-reconstruction-v1.md and blind-receipt-v1.json in this RUN, hashinputs pre/post. No source verdict or proof acceptance.
''')
inputs = [CONTRACT/'neutral-context-v1.lean',RUN/'blind-packet-v1.md']
write(RUN/'blind-inputs-v1.json',dict(inputs={p.as_posix():sha(p) for p in inputs},
    permissions=['blind-reconstruction-v1.md','blind-receipt-v1.json'],history_disclosed=True))
gate('typed-api-search-v1','lake','env','lean',RUN/'typed-api-search-v1.lean')
gate('draft-public-target-types-v1','lake','env','lean',CONTRACT/'public-context-v1.lean')
gate('draft-neutral-target-types-v1','lake','env','lean',CONTRACT/'neutral-context-v1.lean')
fixed()
print('Four draft target propositions and exact API declarations typechecked; not proved or stabilized.')
