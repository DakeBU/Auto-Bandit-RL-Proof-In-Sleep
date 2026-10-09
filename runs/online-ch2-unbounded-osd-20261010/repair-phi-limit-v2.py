from leaf_driver import *
guard()
name = 'phi_limit'
row = targets[name]
assert sha(PUBLIC) == sha(RUN/(name+'-attempt-v1.lean'))
assert load(RUN/(name+'-focused-build-v1.json'))['actual_exit'] == 1
ps = [RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
write(RUN/'phi_limit-repair-exact-before-v2.json',dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
event('phi_limit-repair-v2','repair',dict(task=TASK,leaf=row['name'],failure='derivative simplification needs function subtraction evaluation; nhdsLT_le_nhdsNE needs explicit endpoint',change='Evaluate Pi.sub_apply/id_eq in derivative and specialize one-sided filter inclusion to1',statement_changed=False,definitions_changed=False,prior_attempt=rows([RUN/(name+'-attempt-v1.lean'),RUN/(name+'-focused-build-v1.json')])))
before = PUBLIC.read_bytes()
text = before.decode('utf8')
old = 'simpa only [zero_sub, sub_self, Real.rpow_zero, mul_one, mul_neg_one] using'
new = 'simpa only [Pi.sub_apply, id_eq, zero_sub, sub_self, Real.rpow_zero, mul_one, mul_neg_one] using'
assert text.count(old) == 1
text = text.replace(old,new)
old = 'hd.tendsto_slope.mono_left nhdsLT_le_nhdsNE'
new = 'hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)'
assert text.count(old) == 1
text = text.replace(old,new)
PUBLIC.write_bytes(text.encode('utf8'))
guard()
assert PUBLIC.read_bytes().startswith(base64.b64decode(load(RUN/(name+'-exact-before-v1.json'))['public_raw_base64']))
write(RUN/(name+'-attempt-v2.lean'),PUBLIC.read_bytes())
code,out = capture(name+'-focused-build-v2','lake','build','BanditRLProof.OnlineUnboundedOSD',required=False)
write(RUN/(name+'-focused-inspected-v2.json'),dict(actual_exit=code,actual_stdout=out,build_completed_marker='Build completed successfully' in out,source=rows([PUBLIC]),body_only_repair=True,statement_and_definitions_unchanged=True,source_algorithm_lower_bound_open=True))
assert code == 0 and 'Build completed successfully' in out
capture(name+'-native-fence-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/(name+'-native-extracted-v2.json'))
actual=load(CONTRACT/(name+'-native-extracted-v2.json'));frozen=load(CONTRACT/('frozen-'+name+'-v1.json'))
assert actual['statement_hash']==frozen['statement_hash']
write(RUN/(name+'-fence-compared-v2.json'),dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True,body_only_repair=True))
guard()
write(RUN/'phi-limit-local-milestone-v2.json',dict(leaf=row['name'],status='focused compiled/frozen only',source_supplementary_assertion='left limit1-log2>=0.3',not_endpoint_continuity=True,phi_range_open=True,source_algorithm_lower_bound_open=True,package_BODY_accepted=False,whole_Goal='ACTIVE'))
