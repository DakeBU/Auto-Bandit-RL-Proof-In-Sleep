from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
fixed()
proposals=[('ftlPredict_bestRegret_initial_correction','''(initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)''','''squaredBestRegret y (ftlPredict initial y) T =
      squaredBestRegret y (meanPredict y) T +
        ((initial - y 0)^2 - ((1 : ℝ) / 2 - y 0)^2)'''),
 ('ftlPredict_bestRegret_log_bound','''(initial : ℝ) (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)''','''squaredBestRegret y (ftlPredict initial y) T ≤
      5 + 4 * Real.log (T : ℝ)'''),
 ('ftlPredict_upperNoRegret','''(initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1)''','''NoRegret (Set.Icc (0 : ℝ) 1)
      (fun t x => (x - y t)^2) (ftlPredict initial y)'''),
 ('ftlPredict_bestRegret_average_tendsto_zero','''(initial : ℝ) (y : ℕ → ℝ)
    (hi : initial ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1)''','''Tendsto (fun T : ℕ =>
      squaredBestRegret y (ftlPredict initial y) T / (T : ℝ))
        atTop (nhds (0 : ℝ))''')]
records=[]
for i,(name,args,result) in enumerate(proposals,1):
    header='theorem '+name+' '+args+' :\n    '+result
    records.append(dict(id='G%03d'%i,name='BanditRL.OnlineLearning.'+name,header=header,statement_hash=statement_hash(header),binders=args,conclusion=result,
        phase='draft proposed general-init repair; source v1 final decision pending',owning_public_path='BanditRLProof/OnlineFTLInitializationRegret.lean',production_body_exists=False))
write(CONTRACT/'general-initialization-targets-draft-v2.json',dict(version=2,phase='draft proposal ONLY',new_targets=records,
    original_fifty_targets_unchanged=True,actual_source_final_review_pending=True,source_subobligation='C1-FTL any-initial winning guarantee',new_target_count_is_not_source_result_count=True,chapter_complete=False,goal_complete=False))
write(CONTRACT/'general-initialization-targets-draft-v2.lean.txt','\n\n'.join(x['header'] for x in records))
write(CONTRACT/'general-initialization-intent-draft-v2.md','''DRAFT proposed repair, not frozen/stabilized or proved. The current source reviewer identified printed3/PDF15 any-unit-initial FTL family then its promise to win. Existing8 state/causality targets do not themselves give performance, while exact printed Theorem1.3 initialhalf remains unchanged. Four proposed derived targets use the SAME existing causal ftlPredict/ftlState, with initial chosen before the run and not depending on future/horizon/comparator. G1 proves actual two-trace loss difference consists exactly of the changed first-round loss (T>0); no feasibility/probability/one-step regret oracle. Both traces have identical later strict-past means. G2 gives a derived all-initial logarithmic true-minimum bound5+4lnT for positive horizon/initialunit/bounded scored prefix: reuse actual half4+4lnT and bound changed first loss difference<=1.5 is NOT a printed or sharp coefficient; the printed half4 and initial1/4 remain unchanged. G3 produces only comparator-wise upper-epsilon NoRegret on each one all-time bounded stream from actual finite guarantee; no asserted ordinary fixed-comparator limit. G4 proves ordinary zero normalized TRUE-best regret using G1's fixed finite first-round correction divided by divergingT and the existing same-half true-best average-zero producer. No claim that arbitrary fixed-comparator ordinary limits exist. EmptyT extension is independently0; the G1 identity deliberately excludesT0. Existingtheorem/RNG/law/interfaces/toolchain unchanged. Proposed source model/terminal/editing scope still needs distinct blind and source review, then proving/bodies/canaries/combined/publication gates. Newfour derived declarations would close one source subobligation, not four printed results or wholechapter/book. Proving no body is allowed until stabilization.''')
write(RUN/'general-initialization-draft-typecheck-v2.lean','import BanditRLProof\n\nopen Filter BanditRL.OnlineLearning\n\n'+'\n\n'.join('#check (∀ '+x['binders']+',\n    '+x['conclusion']+')' for x in records))
gate('general-initialization-draft-typecheck-v2','lake','env','lean',RUN/'general-initialization-draft-typecheck-v2.lean')
write(RUN/'general-initialization-draft-type-readiness-v2.json',dict(actual_type_expression_checks=4,actual_exit_zero=True,
    no_theorem_bodies_or_values_created=True,only_compiled_type_expressions_not_proved_theorems=True,
    exact_source_contract_not_stabilized=True,original_fifty_public_statements_and_all_baseline_unchanged=True))
fixed();print('Four general-init draft type expressions checked, no production bodies created; source final review pending.',flush=True)
