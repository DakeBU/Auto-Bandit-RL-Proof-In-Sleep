from common_accepted_v3 import *
import ast

accepted_fixed()
old = RUN/'close-draft-delivery-v3.py'
child = subprocess.run([sys.executable,'-B','-X','utf8',str(old)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert child.returncode == 1 and b"SyntaxError: unmatched ')'" in child.stdout
write(RUN/'close-delivery-v3-syntax-failed-replay.log',child.stdout)
write(RUN/'close-delivery-v3-syntax-failed-replay-exit.json',dict(exit_code=1,
    actual_command=[sys.executable,'-B','-X','utf8',str(old)],
    raw_log_sha256=sha(RUN/'close-delivery-v3-syntax-failed-replay.log'),
    replay_of_original_observed_failure=True,no_Lean_or_publication_change=True))
raw = old.read_bytes()
before = b'do not infer an unexecuted future head\')))'
after = b'do not infer an unexecuted future head\'))'
assert raw.count(before) == 1
fixed_raw = raw.replace(before,after)
ast.parse(fixed_raw.decode('utf8'))
write(RUN/'close-draft-delivery-v4.py',fixed_raw)
write(RUN/'delivery-syntax-repair-v4.json',dict(original_helper_sha256=sha(old),
    operative_helper_sha256=sha(RUN/'close-draft-delivery-v4.py'),
    repair='One unmatched parenthesis; actual Python AST parse passed.',
    original_failed_helper_retained=True,mathematical_reader_or_frozen_statement_change=False,
    chapter_complete=False,goal_complete=False))
print('Delivery-only syntax repaired, original raw failure retained.')
