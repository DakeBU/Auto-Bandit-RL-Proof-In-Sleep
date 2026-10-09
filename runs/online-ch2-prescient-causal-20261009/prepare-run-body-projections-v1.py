from common import *
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
text = TEST.read_text(encoding='utf8')
assert 'theorem two_distinct_current_losses' not in text
assert 'theorem boundary_outside_center_run' not in text
changes = []
for name, old, base, indices in [
    ('canary-two-round-body-v1.txt',
     '  obtain \u27e8hf0, hs0, _, _, _, hstrict, hm0, hnondiff, hD10, hD01, _, _\u27e9 :=\n    BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic\n',
     'BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic',
     [('hf0', 1), ('hs0', 2), ('hstrict', 6), ('hm0', 7), ('hnondiff', 8), ('hD10', 9), ('hD01', 10)]),
    ('canary-outside-run-body-v1.txt',
     '  obtain \u27e8hf, hs, htop, hout, _, _, hstrict, hm, hmove, _, _\u27e9 :=\n    BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center\n',
     'BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center',
     [('hf', 1), ('hs', 2), ('htop', 3), ('hout', 4), ('hstrict', 7), ('hm', 8), ('hmove', 9)])]:
    p = RUN / name
    before = p.read_bytes()
    s = before.decode('utf8')
    assert s.count(old) == 1
    write(RUN / (name + '.pre-projection.raw'), before)
    new = ''.join('  have ' + var + ' := ' + base + '.2' * (i - 1) + '.1\n' for var, i in indices)
    s = s.replace(old, new)
    if name == 'canary-outside-run-body-v1.txt':
        s = s.replace('    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> dsimp [\u03c8, id] <;> ring\n',
                      '    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1\n    dsimp [\u03c8, id]\n    ring\n')
    p.write_bytes(s.encode('utf8'))
    changes.append(dict(path=p.as_posix(), before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=sha(p)))
write(RUN / 'prospective-run-body-projection-preparation-v1.json', dict(changes=changes,
    exact_original_RAW_preserved=True, before_Test_run_body_materialization=True,
    reason='Avoid the known prior-package And.casesOn obstruction to isolating numeric tails. Use exact old theorem component projections as local have proofs, with identical mathematical facts. No new failure or source/statement change.',
    production_fixed_sha256=sha(PUBLIC), test_boundary_bodies_unchanged=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
