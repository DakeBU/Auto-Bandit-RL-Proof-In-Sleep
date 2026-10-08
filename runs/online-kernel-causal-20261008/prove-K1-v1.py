from common_proving_v1 import *

s = proving_fixed()
assert not PUBLIC.exists()
t = s['targets'][0]
context = (CONTRACT/'context-v2.lean.txt').read_text(encoding='utf8').rsplit('end BanditRL.OnlineLearning',1)[0]
body = ''' := by
  have h : ∀ t, ∃ f : KernelDecisionHistory t → I → I,
      Measurable (Function.uncurry f) ∧ ∀ a, (volume : Measure I).map (f a) = κ t a :=
    fun t => Kernel.exists_measurable_map_eq_unitInterval (κ t)
  choose f hf hmap using h
  exact ⟨f, hf, hmap⟩
'''
PUBLIC.write_bytes((context+'\n'+t['header']+body+'\nend BanditRL.OnlineLearning\n').encode('utf8'))
proving_fixed()
write(RUN/'leaf-K1-attempt-v1.lean.raw',PUBLIC.read_bytes())
result = gate('leaf-K1-focused-v1','lake','build','BanditRLProof.OnlineGuessingKernelCausal',required=False)
log = (RUN/'leaf-K1-focused-v1.log').read_text(encoding='utf8')
artifact = ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingKernelCausal.olean'
compiled = result == 0 and 'Built BanditRLProof.OnlineGuessingKernelCausal' in log and \
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size > 0
if result == 0:
    assert compiled
write(RUN/'leaf-K1-attempt-v1.json',dict(id='K1',actual_exit=result,
      source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaf-K1-attempt-v1.lean.raw'),
      frozen_statement_hash=t['statement_hash'],header_unchanged=True,frozen_actual_algorithm_unchanged=True,
      mathematical_body_compiled=compiled,artifact_sha256=sha(artifact) if compiled else None,
      body_source_review_pending=True,package_accepted=False,chapter_complete=False,goal_complete=False))
native('leaf-K1-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
       '--status','compiled' if compiled else 'failed','--notes',
       'One infinite jointly measurable representing sampler family selected before every law/horizon. Focused body only; causal/law/performance terminal and all package gates pending.',
       '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
       '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','5','--obligations-after','5')
proving_fixed()
print('K1 actual focused exit',result,'mathematical body compiled',compiled,'K2-K5 still pending.',flush=True)
