from common import *
fixed()
before=sha(PUBLIC)
capture('production-compiled-VALUE-export-v1','lake','env','lean','--run',RUN/'ExportSummationValuesV1.lean',RUN/'production-compiled-VALUE-v1.json')
d=load(RUN/'production-compiled-VALUE-v1.json')
assert d['has_value'] and len(d['VALUE_constants'])>0
assert sha(PUBLIC)==before
write(RUN/'production-dependency-inspected-v1.json',dict(compiled_export=rows([RUN/'production-compiled-VALUE-v1.json']),module_sha256=before,public_proof_terminals=1,actual_VALUE_presence_checked=['ContinuousOn.intervalIntegrable_of_Icc','intervalIntegral.integral_mono_on','intervalIntegral.integral_const','intervalIntegral.sum_integral_adjacent_intervals'],chapter_complete=False,whole_Goal='active'))
fixed()
