from common_proving_v1 import *
proving_fixed()
context='''import BanditRLProof.OnlineFTLOscillation

open Filter BanditRL.OnlineLearning
namespace Tests.OnlineFTLOscillation

end Tests.OnlineFTLOscillation
'''
headers=[
'''theorem dyadic_unit_and_prefix :
    (∀ t, dyadicObservation t ∈ Set.Icc (0 : ℝ) 1) ∧
    dyadicObservation 0 = 0 ∧ dyadicObservation 1 = 1 ∧
    dyadicObservation 2 = 1 ∧ dyadicObservation 3 = 0''',
'''theorem actual_causal_predictions :
    meanPredict dyadicObservation 0 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 1 = 0 ∧
    meanPredict dyadicObservation 2 = (1 : ℝ)/2 ∧
    meanPredict dyadicObservation 3 = (2 : ℝ)/3''',
'''theorem actual_signed_regrets :
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 0 = 0 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 1 = (1 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 2 = (3 : ℝ)/4 ∧
    squaredBestRegret dyadicObservation (meanPredict dyadicObservation) 3 = (5 : ℝ)/6 ∧
    comparatorRegret (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) 0 3 / (3 : ℝ) = -(1 : ℝ)/6''',
'''theorem all_comparator_iff_instantiated :
    LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ↔
    ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m)''',
'''theorem no_feasible_mean_limit :
    ¬ ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (empiricalMean dyadicObservation) atTop (nhds m)''',
'''theorem two_actual_mean_subsequences :
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (4^(n + 1) - 1))
      atTop (nhds ((2 : ℝ)/3)) ∧
    Tendsto (fun n : ℕ => empiricalMean dyadicObservation (2 * 4^n - 1))
      atTop (nhds ((1 : ℝ)/3))''',
'''theorem obstruction_instantiated :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation) ∧
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
    (¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)''',
'''theorem upper_noRegret_on_actual_stream :
    NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)''',
'''theorem actual_best_average_zero :
    Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ))''',
'''theorem fixed_zero_has_no_ordinary_limit :
    ¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)''',
'''theorem literal_limit_noRegret_fails :
    ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
      (meanPredict dyadicObservation)''']
targets=[]
for i,h in enumerate(headers,1):
    name=h.split()[1]
    targets.append(dict(id='C'+str(i),name='Tests.OnlineFTLOscillation.'+name,header=h,statement_hash=statement_hash(h)))
write(CONTRACT/'canary-context-v1.lean.txt',context)
write(CONTRACT/'canary-targets-v1.lean.txt','\n\n'.join(headers))
write(CONTRACT/'canary-targets-v1.json',dict(version=1,targets=targets,context_sha256=sha(CONTRACT/'canary-context-v1.lean.txt'),
    body_compiled=False,chapter_complete=False,goal_complete=False))
write(CONTRACT/'canary-plan-v1.md','11 public canaries on ONE explicit fixed binary dyadic stream. C1 produces support/first four observations; C2 checks actual strict-past predictions with initial half. C3 checks actual feasible-best R0/1/2/3 and negative signed fixed-zero R3/3. C4 instantiates D1 iff; C5 combines it with D4 to rule out a feasible mean limit. C6 instantiates both D3 limits. C7 instantiates the WHOLE D4 four-part endpoint; C8-C11 inspect each separate metric. No supplied convergence, support, regret or nonexistence oracle. These are tests of four derived results, not eleven source results or chapter completion.')
probe=context.rsplit('end Tests.OnlineFTLOscillation',1)[0]
for t in targets:probe+='\n#check ('+t['header'].split(' :\n',1)[1]+')\n'
write(RUN/'canary-draft-typecheck-v1.lean',probe+'\nend Tests.OnlineFTLOscillation\n')
gate('canary-draft-typecheck-v1','lake','env','lean',RUN/'canary-draft-typecheck-v1.lean')
neutral=(RUN/'neutral-context-and-statements-v1.lean.txt').read_text(encoding='utf8').split('\ntheorem meanPredict_limitNoRegret_iff_mean_converges',1)[0]
neutral+='\nend BanditRL.OnlineLearning\n\nopen Filter BanditRL.OnlineLearning\nnamespace Tests.OnlineFTLOscillation\n\n'
write(RUN/'neutral-canary-statements-v1.lean.txt',neutral+'\n\n'.join(headers)+'\n\nend Tests.OnlineFTLOscillation\n')
write(RUN/'canary-blind-packet-v1.md','Read ONLY neutral-canary-statements-v1.lean.txt and this packet. Reconstruct all11 test statements in natural mathematics/LaTeX, all seven semantic slots, exact indices/constants/signs/ordinary-vs-upper meaning; distinguish canary target elaboration from actual theorem-body verification. No source lookup, prior verdict or proof read. Reused distinct actor history disclosed, requested Astra/medium not runtime attested. Output ONLY canary-blind-reconstruction-v1.md and canary-blind-receipt-v1.json in ownRUN. Hash both exact RAWinputs before/after, report_sha256, inputs_unchanged/input_checks; no body/source/chapter acceptance.')
write(RUN/'canary-blind-inputs-v1.json',dict(rows=rows([RUN/'neutral-canary-statements-v1.lean.txt',RUN/'canary-blind-packet-v1.md'])))
write(RUN/'canary-source-review-packet-v1.md','Separate source-facing canary CONTRACT review BEFORE test proof. Inspect eleven exact headers/complete context/neutral reconstruction and pinned source original p2/p4/p6: same initial-half strict-past FTL and signed regret. Test one explicit all-time dyadic binary stream, not a horizon-picked future oracle. Check exact observations0,1,1,0; predictionshalf,0,half,two-thirds; bestR0=0,R1=quarter,R2=threequarters,R3=five-sixths, fixed-zero R3/3=negative one-sixth. Four production terminals are derived reconciliation, not printed source theorems. C4 exact iff instantiated, C5 feasible mean nonconvergence from actual iff/obstruction, C6 two distinct actual means, C7 same-process four-part obstruction, C8-C11 split metrics. No supplied limit/bound/support oracle. Types elaborated only; bodies to follow after review. Source ordinary lim remains separate from upper NoRegret and correction PROPOSAL. No chapter/Goal closure. Output ONLY canary-contract-review-v1.md and canary-contract-receipt-v1.json in ownRUN: verdict, fixed_input_count, all raw_input_checks(path/before_sha256/after_sha256/unchanged), inputs_unchanged, report_sha256, required_blocking_repairs, per-target seven-slot audits and nondegeneracy assessment. Approve only exact11 headers/context canary proof scope if favorable. No source/header/body/root/site/git edits; reused distinct staged actor/requested Astra medium/runtime_attestedfalse.')
print('11 exact proposed canary types elaborated; no canary theorem body.',flush=True)
