from proof_driver import *
fixed()
TEST=ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean'
assert load(RUN/'fixed-canary-focused-inspected-v1.json')['actual_exit']==1
old=TEST.read_bytes()
write(RUN/'fixed-canary-repair-exact-before-v2.json',dict(path=TEST.relative_to(ROOT).as_posix(),sha256=sha(TEST),before_raw_base64=base64.b64encode(old).decode('ascii')))
s=old.decode('utf8')
before='''    by_cases ht0 : t = 0
    · simpa [loss, ht0] using hs0
    · simpa [loss, ht0] using hs1'''
after='''    intro z hz
    by_cases ht0 : t = 0
    · simpa only [loss, if_pos ht0] using hs0 z hz
    · simpa only [loss, if_neg ht0] using hs1 z hz'''
assert s.count(before)==1
s=s.replace(before,after)
before='''  have hB : divergence ψ 0 (1 / 2) = 11 / 64 := by simpa [x] using hD10'''
after='''  have hA' : divergence ψ (-(1 / 2)) (1 / 2) = 5 / 8 := by
    simpa only [neg_div] using hA
'''+before
assert s.count(before)==1
s=s.replace(before,after)
before='norm_num [sum_range_succ, loss, f0, f1, V, x, hA, hB, hC]'
assert s.count(before)==1
s=s.replace(before,'norm_num [sum_range_succ, loss, f0, f1, V, x, hA, hA\', hB, hC]')
TEST.write_bytes(s.encode('utf8'))
write(RUN/'fixed-canary-attempt-source-v2.lean',TEST.read_bytes())
native_snapshot('fixed-canary-repair-native-before-v2')
event('fixed-canary-repair-event-v2','repair',dict(task=TASK,leaf='fixed_source_run',failure='v1 broad simp unfolded parent forall domain asymmetrically; rational negative expression not normalized before divergence rewrite',repair='Pointwise support application with simp only; explicit neg_div-normalized divergence identity.',statement_changed=False,production_changed=False))
code,out=capture('fixed-canary-focused-build-v2','lake','build','Tests.OnlinePrescientBregmanSourceCanary',required=False)
compiled=code==0 and 'Built Tests.OnlinePrescientBregmanSourceCanary' in out and 'Build completed successfully' in out
actual=lifecycle.lean_declaration_header(TEST,'BanditRL.OnlinePrescientBregmanSourceCanary.fixed_source_run')
assert lifecycle.statement_hash(actual)==load(CONTRACT/'frozen-fixed_source_run-v1.json')['statement_hash']
write(RUN/'fixed-canary-focused-inspected-v2.json',dict(actual_exit=code,actual_stdout=out,compiled_module_markers=compiled,source=rows([TEST]),header_frozen=True,package_accepted=False))
assert compiled
