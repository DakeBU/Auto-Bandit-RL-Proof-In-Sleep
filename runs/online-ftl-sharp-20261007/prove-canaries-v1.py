from common_v1 import *
fixed(proving=True);assert load(RUN/'refined-focused-compiled-v1.json')['public_name']==PRE+'meanPredict_regret_refined'
plan=load(CONTRACT/'planned-canary-headers-v1.json')
bodies={
'endpoint_values':''' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · exact meanPredict_initial_stability _ (by norm_num)
  · exact meanPredict_initial_stability _ (by norm_num)
''',
'interior_value':''' := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
''',
'outside_interval':''' := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
''',
'one_round_refined':''' := by
  constructor
  · norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  · exact meanPredict_regret_refined _ 1 (by omega) (by intro t ht; norm_num)
''',
'two_round_refined':''' := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [meanPredict, empiricalMean, probeTargets, Finset.sum_range_succ]
  · exact meanPredict_regret_refined _ 2 (by omega) (by
      intro t ht
      simp only [probeTargets]
      split_ifs <;> norm_num)
  · norm_num [Finset.sum_range_succ]
''',
'future_independence':''' := by
  constructor
  · apply meanPredict_prefix
    intro i hi
    have : i = 0 := by omega
    subst i
    norm_num [probeTargets]
  · norm_num [probeTargets]
'''}
text='''import BanditRLProof.OnlineLearningFTL
import Mathlib.Tactic

open BanditRL.OnlineLearning
namespace FTLSharpProbe

/-- Validation sequence: first target zero, subsequent targets one. -/
def probeTargets (t : ℕ) : ℝ := if t = 0 then 0 else 1

'''
text+='\n'.join(plan[n]+bodies[n] for n in plan)+'\nend FTLSharpProbe\n'
write(CANARY,text)
write(RUN/'30_lower-canaries-v1.md','Six frozen named validation bodies. Endpoints actually call initial theorem; one/two horizons actually call refined; prefix perturbation calls original causality theorem. Compute both actual values and source RHS separately. Outside2 only invalid-domain witness, not theorem instantiation. No new source/public result. Original test/root unchanged before BODY; combined Tests import later.')
gate('focused-canaries-v1','lake','build','Tests.OnlineLearningFTLSharpCanary')
write(RUN/'canaries-focused-compiled-v1.json',dict(named_test_proofs=6,test_definitions=1,chapter_complete=False,goal_complete=False))
