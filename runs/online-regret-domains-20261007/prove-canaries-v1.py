from common_v1 import *
fixed();s=load(RUN/'stabilized-contract-v1.json');assert s['status'] in ['accepted','accepted-with-explicit-delta']
defs=load(CONTRACT/'planned-test-definitions-v1.json');tests=load(CONTRACT/'planned-canary-headers-v1.json')
prefix='''import BanditRLProof.OnlineLearningRegret
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Filter BanditRL.OnlineLearning
namespace RegretDomainsProbe

'''
text=prefix+'\n\n'.join(defs.values())+'\n\n'
first='''  exact comparatorRegret_eq_sum loss prediction (embed V W hVW u) T'''
text+=tests['domain_gap_sum']+' := by\n'+first+'\n'
write(RUN/'leaves/typed-gap-first-body-v1.lean',text+'\nend RegretDomainsProbe\n')
write(CANARY,text+'\nend RegretDomainsProbe\n')
gate('typed-gap-first-body-v1','lake','env','lean',CANARY)
write(RUN/'first-ready-leaf-compiled-v1.json',dict(declaration=TEST+'domain_gap_sum',actual_proof='Public comparatorRegret_eq_sum instantiated with X=SubtypeW and comparator inclusion fromV',header_sha256=hashlib.sha256(tests['domain_gap_sum'].encode()).hexdigest(),frozen_header_unchanged=True,source_module_sha256=sha(PUBLIC),actual_type_context='typed loss only onW; predictorW; comparatorV; no arbitrary loss extension',first_attempt_compiled=True,gate='typed-gap-first-body-v1',package_accepted=False,chapter_complete=False,goal_complete=False))
native('first-ready-leaf-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--lean',CANARY,'--verifier-evidence',RUN/'first-ready-leaf-compiled-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'comparatorRegret_eq_sum','--notes','Actual typed W loss/V comparator embedding leaf compiled; 0newproductionmath; current domain source-mapping test, not genericperformance/chapterclosure.')
bodies={
'restriction_commutes':'  rfl',
'proper_inclusion':'''  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change 0 ≤ x ∧ x ≤ 2
    change 0 ≤ x ∧ x ≤ 1 at hx
    exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩
  · norm_num [outputW]
  · norm_num [sourceV]''',
'loss_prefix':'''  unfold comparatorRegret
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    exact h t (Finset.mem_range.mp ht) (prediction t)
  · apply Finset.sum_congr rfl
    intro t ht
    exact h t (Finset.mem_range.mp ht) u''',
'zero_horizon':'  simp [comparatorRegret]',
'outside_prediction_and_negative_regret':'''  norm_num [output, outputW, sourceV, comparatorRegret, domainLoss,
    referenceOne, Finset.sum_range_succ]''',
'same_prediction_two_comparators':'''  norm_num [referenceZero, referenceOne, sourceV, comparatorRegret, domainLoss,
    output, Finset.sum_range_succ]''',
'negative_game_noRegret':'''  apply noRegret_of_vanishing_bound liftedComparators domainLoss output (fun _ _ => 0)
  · intro u hu
    exact Filter.Eventually.of_forall (fun T => by
      change comparatorRegret domainLoss output u T / (T : ℝ) ≤ 0
      apply div_nonpos_of_nonpos_of_nonneg ?_ (Nat.cast_nonneg T)
      rw [comparatorRegret_eq_sum]
      apply Finset.sum_nonpos
      intro t ht
      change 0 ≤ u.val ∧ u.val ≤ 1 at hu
      change -(2 : ℝ) - (-u.val) ≤ 0
      linarith [hu.2])
  · intro u hu
    exact tendsto_const_nhds'''
}
for n,h in tests.items():
 if n!='domain_gap_sum':text+='\n'+h+' := by\n'+bodies[n]+'\n'
write(RUN/'leaves/canary-bodies-attempt-v1.txt',bodies)
CANARY.write_bytes((text+'\nend RegretDomainsProbe\n').encode())
gate('all-canary-bodies-v1','lake','build','Tests.OnlineLearningRegretDomainsCanary')
assert re.findall(r'(?m)^theorem (\w+)\b',CANARY.read_text(encoding='utf-8'))==list(tests)
fixed();write(RUN/'canary-bodies-compiled-v1.json',dict(actual_named_validation_proofs=8,actual_fixture_definitions=8,new_production_math=0,canary_sha256=sha(CANARY),frozen_headers_unchanged=True,first_attempt_all_bodies_compiled=True,source_mapping_terminal='Typed shared API instance, concrete proper domains and producer-derived negative-regret NoRegret',BODY_review='pending',combined_reader_native_PR='pending',chapter_complete=False,goal_complete=False))
print('Actual8 canary proof bodies compiled; source/production math unchanged; BODY and full acceptance pending.')
