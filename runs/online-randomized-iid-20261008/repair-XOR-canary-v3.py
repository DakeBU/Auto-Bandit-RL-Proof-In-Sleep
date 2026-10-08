from common_reviewed_v2 import *

headers_fixed(7)
assert load(RUN/'canary-XOR-focused-build-v2-exit.json')['exit_code'] == 1
write(RUN/'snapshots'/'canary-XOR-failed-v2.raw', CANARY.read_bytes())
text = CANARY.read_text(encoding='utf8')
cast = '← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0)'
old = '  norm_num [fourLaw]\n'
assert text.count(old) == 1
text = text.replace(old, old+'  rw ['+cast+']\n  norm_cast\n  norm_num\n', 1)
old = '      Set.indicator_apply, xorX, xorY, xorTape, h0s, h1s, h0t, h1t]\n'
assert text.count(old) == 3
text = text.replace(old, old.rstrip('\n')+' <;>\n      (rw ['+cast+']; norm_cast; norm_num)\n')
old = '    Set.indicator_apply, xorX, xorY, xorTape] at he\n'
assert text.count(old) == 1
text = text.replace(old, old+'  rw ['+cast+'] at he\n  norm_cast at he\n  norm_num at he\n',1)
CANARY.write_bytes(text.encode('utf8'))
write(RUN/'leaves'/'canary-with-XOR-v3.lean', CANARY.read_bytes())
write(RUN/'canary-XOR-failure-repair-v3.json', dict(
    failed_build='canary-XOR-focused-build-v2-exit.json',
    failed_source='snapshots/canary-XOR-failed-v2.raw',
    public_statement_changed=False, canary_statement_changed=False,
    repair='Only five arithmetic proof bodies: explicitly transfer finite ENNReal quarter arithmetic to NNReal. All independence and counterexample statements unchanged.',
    isolated_arithmetic_gate='ENN-quarter-arithmetic-v7-exit.json',
    retained_failed_isolated_attempts=[3,4,5,6]))
gate('canary-XOR-focused-build-v3','lake','build','Tests.OnlineGuessingRandomizedIIDCanary')
headers_fixed(7)
write(RUN/'snapshots'/'canary-XOR-compiled-v3.raw',CANARY.read_bytes())
print('Actual private-seed/infinite-IID and pairwise-but-not-joint XOR canaries compiled.')
