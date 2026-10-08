from common_v1 import *

bindings=load(RUN/'FINAL-v1-prose-repair-mutable-bindings-v2.json')
assert len(bindings)==2
for r in bindings:
    p=Path(r['live_path']); original=Path(r['snapshot']).read_bytes()
    assert sha(r['snapshot'])==r['sha256'] and sha(p)==r['current_sha256']
    assert p.read_bytes().startswith(original)
    suffix=p.read_bytes()[len(original):]
    assert hashlib.sha256(suffix).hexdigest()==r['suffix_sha256']
    assert [json.loads(x) for x in suffix.decode('utf8').splitlines() if x.strip()]==r['exact_owned_entries']
write(RUN/'FINAL-repair-guard-failure-v2.json',dict(
    executed_helper='repair-FINAL-prose-v2.py', actual_outer_exit=1,
    failed_assertion='common_body_v1.body_fixed: integrated changed lifecycle_sessions.jsonl is not a reader/root path',
    actual_completed_native_exits=[0,0], exact_completed_mutable_bindings=bindings,
    raw_outer_stderr_saved=False,
    limitation='Outer error was returned by exec_command; no separate raw stderr file was captured. This record is a diagnostic, not a raw log.',
    repair='Version a guard accepting only the two SHA-bound original journal snapshots and their exact recorded own rejection/repair suffixes. No native command rerun, no source change.',
    obligations_pending=3, goal_complete=False))
s=(RUN/'common_body_v1.py').read_text(encoding='utf8')
needle="        assert integrated and p.resolve() in allowed,p\n"
assert s.count(needle)==1
replacement="""        mutable={x['live_path']:x for x in load(RUN/'FINAL-v1-prose-repair-mutable-bindings-v2.json')}
        if p.as_posix() in mutable:
            x=mutable[p.as_posix()]
            original=Path(x['snapshot']).read_bytes()
            assert sha(x['snapshot'])==row['sha256']
            assert sha(p)==x['current_sha256'] and p.read_bytes().startswith(original)
            suffix=p.read_bytes()[len(original):]
            assert hashlib.sha256(suffix).hexdigest()==x['suffix_sha256']
            entries=[json.loads(v) for v in suffix.decode('utf8').splitlines() if v.strip()]
            assert entries==x['exact_owned_entries']
            assert all(v.get('task',v.get('session_id'))==TASK for v in entries)
            continue
        assert integrated and p.resolve() in allowed,p
"""
write(RUN/'common_body_FINAL_repair_v2.py',s.replace(needle,replacement))
s=(RUN/'common_reader_v4.py').read_text(encoding='utf8')
assert s.startswith('from common_body_v1 import *')
write(RUN/'common_reader_FINAL_repair_v2.py',s.replace('from common_body_v1 import *','from common_body_FINAL_repair_v2 import *',1))
from common_reader_FINAL_repair_v2 import fixed_integrated
assert fixed_integrated()
print('Actual exact rejection/repair journal guard passes; no repeated native commands.',flush=True)
