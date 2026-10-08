from common_proving_v1 import *

s = proving_fixed()
assert load(RUN/'leaf-K3-attempt-v2.json')['mathematical_body_compiled']
t = s['targets'][3]
before = PUBLIC.read_bytes()
source = before.decode('utf8')
assert '\ntheorem '+t['name'].split('.')[-1] not in source
body = ''' := by
  have hp : Measurable (kernelGeneratedPrediction f t) := by
    have hr : Measurable (fun ω : (ℕ → I) × (ℕ → ℝ) =>
        (ω.1, fun i : Fin t => ω.2 i)) := by
      fun_prop
    exact (kernel_sampler_causal_process f hf).1 t |>.comp hr
  exact condDistrib_ae_eq_of_measure_eq_compProd (kernelGeneratedHistory f t)
    hp.aemeasurable (kernel_sampler_joint_law κ f hf hκ ν t)
'''
native('lifecycle-proving-K4-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,leaf='K4',attempt=1,statement_hash=t['statement_hash'],
       dependencies=['K1','K2','K3'],terminal='conditional law AE under actual generated history marginal')))
footer = '\nend BanditRL.OnlineLearning\n'
assert source.endswith(footer)
PUBLIC.write_bytes((source[:-len(footer)]+'\n'+t['header']+body+footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(before[:-len(footer.encode())])
proving_fixed()
write(RUN/'leaf-K4-attempt-v1.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K4-focused-v1','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K4-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K4-attempt-v1.json',dict(id='K4',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K4-attempt-v1.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      previous_K1_K2_K3_bytes_preserved=True,body_source_review_pending=True,
      package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K4-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'Conditional law follows from actual K3 joint law and AE uniqueness of condDistrib; equality only under actual generated-history marginal. Frozen context and all preceding bodies retained; final same-process performance terminal and package gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K4 focused exit',result,'actual compiled',compiled,flush=True)
