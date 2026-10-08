from common_proving_v1 import *

s=proving_fixed()
leaf=sys.argv[1];assert leaf in ['L2','L3','L4']
assert load(RUN/'leaf-L1-attempt-v2.json')['mathematical_body_compiled']
i=int(leaf[1:])-1;t=s['targets'][i]
before=PUBLIC.read_bytes();text=before.decode('utf8')
assert 'theorem '+t['name'].split('.')[-1] not in text
expected_previous=i
assert sum('\ntheorem '+x['name'].split('.')[-1] in text for x in s['targets'])==expected_previous
if i>1:assert load(RUN/('leaf-L'+str(i)+'-attempt-v1.json'))['mathematical_body_compiled']
write(RUN/('proving-'+leaf+'-v1.json'),dict(leaf=leaf,terminal=t['name'],
    core_dependency_actual_attempt='leaf-L1-attempt-v2.json',core_source_hash=sha(RUN/'leaf-L1-attempt-v2.lean.raw'),
    dependency_ready=True,frozen_statement_hash=t['statement_hash'],same_original_process=True,
    permitted_file=PUBLIC.relative_to(ROOT).as_posix(),no_terminal_type_edits=True))
native('lifecycle-proving-'+leaf+'-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(run_id=RUN.name,selected_leaf=leaf,statement_hash=t['statement_hash'],
        actual_core_attempt=2,single_lower_route=True,no_terminal_type_edits=True)))
if leaf=='L2':
    body=''' := by
  rename_i mΩ mSeed
  letI : MeasurableSpace Ω := mΩ
  have hAE (t : ℕ) : AEStronglyMeasurable[F t] (prediction t) μ := by
    obtain ⟨version, hv, he⟩ :=
      completed_measurable_real_exists_version μ (F t) (prediction t) (hP t)
    exact hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_exists_bounded_history_policy μ Y S F hF prediction hAE hpb
'''
elif leaf=='L3':
    body=''' := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨version, hv, he⟩ := completed_measurable_real_exists_version μ F P hP
  have hAE : AEStronglyMeasurable[F] P μ := hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_private_seed_independent μ Y hY hind S hS hseed t F hF P hAE
'''
else:
    body=''' := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  have hAE (t : ℕ) : AEStronglyMeasurable[F t] (prediction t) μ := by
    obtain ⟨version, hv, he⟩ :=
      completed_measurable_real_exists_version μ (F t) (prediction t) (hP t)
    exact hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_private_seed_expectedFixed_excess μ Y hY hlaw hb hind S hS hseed
    F hF prediction hAE hpb T
'''
footer='\nend BanditRL.OnlineLearning\n';assert text.endswith(footer)
PUBLIC.write_bytes((text[:-len(footer)]+'\n'+t['header']+body+footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(before[:-len(footer.encode())])
proving_fixed()
write(RUN/('leaf-'+leaf+'-attempt-v1.lean.raw'),PUBLIC.read_bytes())
result=gate('leaf-'+leaf+'-focused-v1','lake','build','BanditRLProof.OnlineGuessingCompletedCausal',required=False)
log=(RUN/('leaf-'+leaf+'-focused-v1.log')).read_text(encoding='utf8')
artifact=ROOT/'.lake/build/lib/lean/BanditRLProof/OnlineGuessingCompletedCausal.olean'
compiled=(result==0 and 'Built BanditRLProof.OnlineGuessingCompletedCausal' in log and
    'Build completed successfully' in log and artifact.is_file() and artifact.stat().st_size>0)
if result==0:assert compiled
write(RUN/('leaf-'+leaf+'-attempt-v1.json'),dict(id=leaf,actual_exit=result,
    current_source_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/('leaf-'+leaf+'-attempt-v1.lean.raw')),
    frozen_statement_hash=t['statement_hash'],header_unchanged=True,mathematical_body_compiled=compiled,
    previous_bodies_bytes_preserved=True,artifact_sha256=sha(artifact) if compiled else None,
    semantic_BODY_review_pending=True,package_accepted=False))
native('leaf-'+leaf+'-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt',
    '--status','compiled' if compiled else 'failed','--notes',leaf+' actual core-produced relative AE version and immutable original-process causal endpoint; no supplied independence/stability bound. Focused compile only; all package gates pending.',
    '--lean',PUBLIC.relative_to(ROOT).as_posix(),'--run-id',RUN.name,'--statement-hash',t['statement_hash'],
    '--progress-class','compiled-leaf' if compiled else 'diagnostic','--obligations-before','4','--obligations-after','4')
proving_fixed()
print(leaf,'actual focused exit',result,'actual compiled witness',compiled,'four accepted obligations pending.',flush=True)
