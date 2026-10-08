from common_proving_v1 import *
s=proving_fixed()
assert load(RUN/'leaf-L2-attempt-v2.json')['mathematical_body_compiled']
old=PUBLIC.read_bytes();end=b'\nend BanditRL.OnlineLearning\n'
assert old.endswith(end) and sha(PUBLIC)==load(RUN/'leaf-L2-attempt-v2.json')['current_source_sha256']
native('lifecycle-proving-L3-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(run_id=RUN.name,selected_leaf='L3',statement_hash=s['targets'][2]['statement_hash'],
        dependency_L2_actual_focused_exit=0,terminal_type_edits=False,accepted_package=False)))
body=''' := by
  have hinfo (t : ℕ) : privateSeedPastInformation S Y t ≤ ‹MeasurableSpace Ω› :=
    (hS.prodMk (measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) => hY i))).comap_le
  have hL (t : ℕ) : MemLp (prediction t) 2 μ :=
    memLp_of_bounded (hpb t)
      (AEStronglyMeasurable.mono ((hF t).trans (hinfo t)) (hP t)) 2
  have hInd (t : ℕ) : IndepFun (prediction t) (Y t) μ :=
    ae_predictable_private_seed_independent μ Y hY hind S hS hseed t (F t) (hF t)
      (prediction t) (hP t)
  have he : expectedFixedRegret μ Y prediction T =
      ∑ t ∈ Finset.range T, ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
    unfold expectedFixedRegret
    rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
    exact iid_cumulative_prediction_decomposition μ Y hY hlaw hb prediction hL hInd T
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))
'''
new=old[:-len(end)]+b'\n'+(s['targets'][2]['header']+body).encode('utf8')+end
PUBLIC.write_bytes(new)
assert new.startswith(old[:-len(end)])
proving_fixed()
write(RUN/'leaf-L3-attempt-v1.lean.raw',new)
result=gate('leaf-L3-focused-v1','lake','build','BanditRLProof.OnlineGuessingAECausal',required=False)
write(RUN/'leaf-L3-attempt-v1.json',dict(id='L3',actual_exit=result,current_source_sha256=sha(PUBLIC),
    snapshot_sha256=sha(RUN/'leaf-L3-attempt-v1.lean.raw'),previous_L1_L2_proof_bytes_preserved=True,
    frozen_statement_hash=s['targets'][2]['statement_hash'],header_unchanged=True,
    mathematical_body_compiled=result==0,semantic_BODY_review_pending=True,package_accepted=False,
    exact_same_original_prediction=True,derived_independence_not_assumed=True))
native('leaf-L3-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if result==0 else 'failed','--notes','L3 exact original-P expected fixed minimum outside expectation; actual derived independence and L2 integrability; finite all-natural T. Full gates pending.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',s['targets'][2]['statement_hash'],
    '--progress-class','compiled-leaf' if result==0 else 'diagnostic','--obligations-before','3','--obligations-after','3')
proving_fixed()
print('L3 actual focused exit',result,'; acceptance remains pending')
