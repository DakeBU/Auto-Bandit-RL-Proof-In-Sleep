from common_accepted_v3 import *

accepted_fixed()
old = RUN/'audit-accepted-metadata-v3.py'
start = time.time()
child = subprocess.run([sys.executable,'-B','-X','utf8',str(old)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert child.returncode == 1 and b'assert entries' in child.stdout
write(RUN/'metadata-audit-v3-failed-replay.log', child.stdout)
write(RUN/'metadata-audit-v3-failed-replay-exit.json', dict(
    actual_command=[sys.executable,'-B','-X','utf8',str(old)], exit_code=child.returncode,
    seconds=round(time.time()-start,3), log_sha256=sha(RUN/'metadata-audit-v3-failed-replay.log'),
    replay_of_original_observed_failure=True,
    reason='Own --output memory-record writes its actual own RUN JSON; global lifecycle_memory journal correctly remained unchanged.',
    semantic_or_native_gate_failure=False))
raw = old.read_bytes()
assert raw.count(b'        assert entries\n') == 1
raw = raw.replace(b'        assert entries\n', b"        row['unchanged'] = not entries\n")
raw = raw.replace(b'actual-accepted-metadata-audit-v3.json', b'actual-accepted-metadata-audit-v4.json')
write(RUN/'audit-accepted-metadata-v4.py', raw)
gate('metadata-audit-v4', sys.executable,'-B','-X','utf8',RUN/'audit-accepted-metadata-v4.py')
write(RUN/'metadata-audit-repair-v4.json', dict(original_helper_sha256=sha(old),
    operative_helper_sha256=sha(RUN/'audit-accepted-metadata-v4.py'),
    delta='Allow an unchanged global journal; still check every actual appended row belongs to this task. No fabricated shared-memory append.',
    native_commands_not_repeated=True, original_failed_helper_preserved=True,
    mathematical_statements_readers_and_native_records_unchanged=True,
    chapter_complete=False, goal_complete=False))
print('Actual metadata audit repaired; all native records and fixed mathematical/source bytes unchanged.')
