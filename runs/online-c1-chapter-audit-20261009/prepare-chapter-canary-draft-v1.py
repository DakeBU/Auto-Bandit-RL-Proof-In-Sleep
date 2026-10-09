from common_v1 import *
import re
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header,_strip_lean_comments
defs='''def rising (t : ℕ) : ℝ := if t = 0 then 0 else 1
def falling (t : ℕ) : ℝ := if t = 0 then 1 else 0
'''
imports=['BanditRLProof.OnlineFTLInitializationRegret','Tests.OnlineLearningChapterOneCanary','Tests.OnlineLearningRegretDomainsCanary','Tests.OnlineSquareMinimumCanary','Tests.OnlineGuessingIIDSuccessCanary','Tests.OnlineGuessingKernelCausalCanary','Tests.OnlineFTLOscillationCanary','Tests.OnlineGuessingLogLowerCanary']
setup=''.join('import '+m+'\n' for m in imports)+'\nnoncomputable section\nopen Filter Asymptotics MeasureTheory ProbabilityTheory BanditRL.OnlineLearning\nopen scoped ENNReal\nopen Tests.OnlineGuessingIIDBenchmark\nnamespace Tests.OnlineLearningChapterAudit\n\n'+defs+'\n'
specs=[
('initial_zero_first_regret','squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 ∧\n      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 > (1 : ℝ) / 4'),
('two_round_initial_correction','squaredBestRegret falling (ftlPredict 0 falling) 2 =\n      squaredBestRegret falling (meanPredict falling) 2 + (3 : ℝ) / 4'),
('positive_regret_negative_correction','squaredBestRegret rising (ftlPredict 0 rising) 2 = (1 : ℝ) / 2 ∧\n      squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧\n      ((0 - rising 0)^2 - ((1 : ℝ) / 2 - rising 0)^2) = -(1 : ℝ) / 4'),
('general_initial_finite_values','squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 ∧\n      squaredBestRegret falling (ftlPredict 0 falling) 2 ≤ (3 : ℝ) ∧\n      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 ≤ 1'),
('same_past_current_reveal','ftlState 0 rising 1 = ftlState 0 (fun _ => 0) 1 ∧\n      rising 1 ≠ (0 : ℝ) ∧ ftlState 0 rising 2 ≠ ftlState 0 (fun _ => 0) 2'),
('initialized_state_values','ftlState ((3 : ℝ) / 4) rising 0 = (0, (3 : ℝ) / 4) ∧\n      ftlState ((3 : ℝ) / 4) rising 1 = (1, 0) ∧\n      ftlState ((3 : ℝ) / 4) rising 2 = (2, (1 : ℝ) / 2)'),
('all_initial_dyadic_upper','∀ initial ∈ Set.Icc (0 : ℝ) 1,\n      NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)\n        (ftlPredict initial dyadicObservation)'),
('nonhalf_dyadic_best_average','Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation\n      (ftlPredict ((3 : ℝ) / 4) dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ))'),
('outside_real_initial_identity','squaredBestRegret (fun _ => (3 : ℝ)) (ftlPredict 2 (fun _ => 3)) 1 =\n      squaredBestRegret (fun _ => (3 : ℝ)) (meanPredict (fun _ => 3)) 1 - (21 : ℝ) / 4'),
('empty_horizon_not_first_correction','squaredBestRegret falling (ftlPredict 0 falling) 0 = 0 ∧\n      squaredBestRegret falling (meanPredict falling) 0 = 0 ∧\n      ((0 - falling 0)^2 - ((1 : ℝ) / 2 - falling 0)^2) = (3 : ℝ) / 4'),
('best_and_fixed_comparator_distinct','comparatorRegret (fun t x => (x - falling t)^2) (ftlPredict 0 falling) 0 2 = 1 ∧\n      squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2'),
('positive_iid_variance_excess','variance (observation 0) iidLaw = (1 : ℝ) / 4 ∧\n      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 ∧\n      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 / (2 : ℝ) = (1 : ℝ) / 8'),
('population_mean_fixed_minimum','IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw)\n      \'\' Set.Icc (0 : ℝ) 1) ((1 : ℝ) / 2) ∧\n      expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) 2 = 0'),
('expectation_and_hindsight_distinct','(∫ ω, hindsightMinimum ω 2 ∂iidLaw) = (1 : ℝ) / 4 ∧\n      expectedFixedMinimum iidLaw observation 2 = (1 : ℝ) / 2'),
('iid_success_total_and_average','Tendsto (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T /\n      (T : ℝ)) atTop (nhds (0 : ℝ)) ∧\n      (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T) =o[atTop]\n        (fun T : ℕ => (T : ℝ))'),
('loss_sequence_visible_outside_comparators','(RegretDomainsProbe.output 0).val ∈ RegretDomainsProbe.outputW ∧\n      (RegretDomainsProbe.output 0).val ∉ RegretDomainsProbe.sourceV ∧\n      comparatorRegret RegretDomainsProbe.domainLoss RegretDomainsProbe.output\n        RegretDomainsProbe.referenceOne 2 = -2 ∧\n      comparatorRegret (fun t x => 2 * RegretDomainsProbe.domainLoss t x)\n        RegretDomainsProbe.output RegretDomainsProbe.referenceOne 2 = -4'),
('produced_minimum_and_empty_nonunique','empiricalMean rising 2 = (1 : ℝ) / 2 ∧\n      sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - rising t)^2) \'\' Set.Icc (0 : ℝ) 1) = (1 : ℝ) / 2 ∧\n      ∀ u ∈ Set.Icc (0 : ℝ) 1, (∑ t ∈ Finset.range 0, (u - rising t)^2) = 0'),
('positive_prefix_unique','∀ u : ℝ,\n      (∑ t ∈ Finset.range 2, (u - rising t)^2) ≤\n        (∑ t ∈ Finset.range 2, (empiricalMean rising 2 - rising t)^2) → u = (1 : ℝ) / 2'),
('concrete_be_the_leader','(∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) = -2 ∧\n      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2)) = 0 ∧\n      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) ≤\n        ∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2)'),
('half_refined_and_logarithmic','squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧\n      squaredBestRegret rising (meanPredict rising) 2 ≤ (9 : ℝ) / 4 ∧\n      squaredBestRegret rising (meanPredict rising) 2 ≤ 4 + 4 * Real.log 2'),
('same_stream_later_stability','(meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 = (3 : ℝ) / 4 ∧\n      (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 ≤ 4 / ((1 : ℝ) + 1)'),
('actual_kernel_same_run_excess','(∀ T : ℕ, expectedFixedRegret Tests.OnlineGuessingKernelCausal.gameLaw\n      Tests.OnlineGuessingKernelCausal.target\n      (fun t ω => (Tests.OnlineGuessingKernelCausal.prediction t ω : ℝ)) T = (T : ℝ) / 4) ∧\n      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 0 1) {1} = (1 / 4 : ℝ≥0∞) ∧\n      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 1 1) {1} = (3 / 4 : ℝ≥0∞)'),
('correlation_changes_excess','expectedFixedRegret iidLaw (fun _ => observation 0)\n      (fun t ω => meanPredict (fun _ => observation 0 ω) t) 2 = -(1 : ℝ) / 4 ∧\n      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4'),
('same_actual_ftl_limit_obstruction','NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) ∧\n      Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧\n      (¬ ∃ a : ℝ, Tendsto (fun T : ℕ => comparatorRegret (fun t x => (x - dyadicObservation t)^2)\n        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧\n      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation)'),
('qualitative_log_fixed_binary_witness','∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤\n      ∫ b, BanditRL.OnlineLearning.GuessingLower.pathRegret (GuessingLogLowerProbe.seededPolicy b) v.toList\n        ∂GuessingLogLowerProbe.coinMeasure'),
('harmonic_two_bound','(harmonic 2 : ℝ) = (3 : ℝ) / 2 ∧ (harmonic 2 : ℝ) ≤ 1 + Real.log 2'),
('centered_total_average_boundary','(fun T : ℕ => (5 + 3 * (T : ℝ)) - (T : ℝ) * 3) =o[atTop]\n      (fun T : ℕ => (T : ℝ)) ∧\n      ((5 + 3 * (0 : ℝ)) / (0 : ℝ) - 3) = -(3 : ℝ)')
]
targets=[]
for n,(name,conclusion) in enumerate(specs,1):
    header='theorem '+name+' :\n    '+conclusion
    targets.append(dict(id='C%03d'%n,name='Tests.OnlineLearningChapterAudit.'+name,header=header,conclusion=conclusion,statement_hash=statement_hash(header),owning_public_path='Tests/OnlineLearningChapterAuditCanary.lean',phase='draft; no body/public Test yet'))
write(CONTRACT/'chapter-canary-targets-draft-v1.json',dict(targets=targets,imports=imports,setup=setup,exact_target_count=len(targets),production_scope_unchanged=True,source_count=17,proof_total=None,chapter_complete=False,goal_complete=False))
probe=RUN/'chapter-canary-draft-types-v1.lean'
write(probe,setup+'\n'.join('#check ('+t['conclusion']+' : Prop)' for t in targets)+'\nend Tests.OnlineLearningChapterAudit\n')
gate('chapter-canary-draft-types-v1','lake','env','lean',probe)
neutral=setup+'\n'.join('theorem '+t['id']+' :\n    '+t['conclusion']+'\n' for t in targets)+'\nend Tests.OnlineLearningChapterAudit\n'
write(CONTRACT/'chapter-canary-neutral-targets-v1.lean.txt',neutral)
# Exact source-free mathematical definitions only. No theorem bodies, source/card/review/verdict.
context=(CONTRACT/'general-initialization-neutral-context-v2.lean.txt').read_text('utf8')+'\n'
sources=[
('Tests/OnlineLearningChapterOneCanary.lean',None),
('Tests/OnlineLearningRegretDomainsCanary.lean',None),
('Tests/OnlineGuessingIIDBenchmarkCanary.lean',None),
('Tests/OnlineGuessingKernelCausalCanary.lean',None),
('Tests/OnlineGuessingLogLowerCanary.lean',None),
('BanditRLProof/OnlineGuessingKernelCausal.lean',None),
('BanditRLProof/OnlineLearningFTLState.lean',None),
('BanditRLProof/OnlineFTLOscillation.lean',None),
('BanditRLProof/OnlineNoRegretSemantics.lean',None),
('BanditRLProof/OnlineGuessingIIDBenchmark.lean',None),
('BanditRLProof/OnlineGuessingLogLower.lean',None)]
declpattern=re.compile(r'(?m)^(?:(?:noncomputable|private)\s+)*(?:def|abbrev|theorem|lemma|instance|namespace|end)\b')
for rel,_ in sources:
    text=_strip_lean_comments((ROOT/rel).read_text('utf8'))
    matches=list(declpattern.finditer(text));namespace=[];blocks=[]
    for i,m in enumerate(matches):
        part=text[m.start():matches[i+1].start() if i+1<len(matches) else len(text)].strip()
        first=part.splitlines()[0]
        if first.startswith('namespace '):namespace.append(first.split()[1]);continue
        if first.startswith('end'):
            if namespace:namespace.pop()
            continue
        if re.match(r'(?:(?:noncomputable|private)\s+)*(?:def|abbrev)\b',first):
            ns='.'.join(namespace)
            blocks.append(('namespace '+ns+'\n' if ns else '')+part+'\n'+('end '+ns+'\n' if ns else ''))
    context+='\n\n'+'\n\n'.join(blocks)
# Explicit support typedefs and the public existential type needed by selectedSampler.
context+='\n\n'+next(t['header'] for t in load(CONTRACT/'targets-v1.json')['targets'] if t['name'].endswith('.causal_kernel_realization_and_expectedFixed_excess'))+'\n'
write(CONTRACT/'chapter-canary-neutral-context-v1.lean.txt',context)
packet=RUN/'chapter-canary-neutral-packet-v1.md'
write(packet,'Decode only the27 supplied neutral proposed theorem headers and exact definition context. No source identity, proof bodies, compile result or intent verdict is supplied. Reconstruct each in prose and LaTeX with seven semantic slots, full quantifiers/initial/current-vs-past/metric/expectation/minimum/T0/constants/support/model boundaries. Types are proposals, not proofs. Existing mathematical identifier names may remain in exact definitions; reused staged decoder history is disclosed, no absolute blindness/runtime/human/external review claim. Output ONLY chapter-canary-blind-reconstruction-v1.md and chapter-canary-blind-receipt-v1.json in this RUN, bind two indexed file/index/packet RAW beforeafter, actual27 header count, missingcontext/ambiguities/complete slots. Do not read source/intent/review/body/logs or edit inputs. Requested GPT-6 Astra medium.')
write(RUN/'chapter-canary-neutral-inputs-v1.json',dict(rows=rows([CONTRACT/'chapter-canary-neutral-targets-v1.lean.txt',CONTRACT/'chapter-canary-neutral-context-v1.lean.txt']),exact_targets=27,source_identity_provided=False,proofs_provided=False,source_review_provided=False))
fixed()
print('27 exact chapter canary types compiled as Props; no canary body created. Neutral reconstruction pending.',flush=True)
