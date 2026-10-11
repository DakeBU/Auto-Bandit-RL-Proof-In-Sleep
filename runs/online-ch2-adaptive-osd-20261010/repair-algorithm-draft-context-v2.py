from common import *
first = load(RUN/'algorithm-draft-type-probe-v1.json')
assert first['actual_exit'] == 1
v1 = CONTRACT/'algorithm-definition-context-draft-v1.lean.txt'
raw = v1.read_bytes()
marker = b'abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)\n'
assert raw.count(marker) == 1
context = raw.replace(marker, marker+b'local instance : DecidableEq E := Classical.decEq E\n')
write(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt', context)
write(RUN/'algorithm-draft-context-repair-v2.json', dict(
    actual_failed_exit=1, failure_receipt_sha256=sha(RUN/'algorithm-draft-type-probe-v1.json'),
    failure='Header if selected=0 lacks synthesized DecidableEq in generic ambient E',
    repair='Explicit local classical DecidableEq in noncomputable scoped context; no theorem premise or output type change',
    definition_context_v1_sha256=sha(v1), definition_context_v2_sha256=sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'),
    predicate_assumptions_changed=False, production_algorithm_created=False,
    boundary='Scratch definition/proposition type elaboration only, not proof attempt or production acceptance'))
probe = context.decode('utf8')+'\n'
for name in ['state_succ', 'regret_bound']:
    header = (CONTRACT/('algorithm-'+name+'-header-draft-v1.lean.txt')).read_text(encoding='utf8')
    statement = header[len('theorem '+name):].rstrip()[:-len(':= by')]
    probe += '#check (∀ '+statement.replace(' :\n', ',\n', 1).lstrip()+')\n\n'
write(RUN/'AlgorithmDraftTypeProbeV2.lean', probe+'end BanditRL.OnlineAdaptiveOSD\n')
code, out = capture('algorithm-draft-type-probe-v2', 'lake', 'env', 'lean', RUN/'AlgorithmDraftTypeProbeV2.lean', required=False)
print(out)
sys.exit(code)
