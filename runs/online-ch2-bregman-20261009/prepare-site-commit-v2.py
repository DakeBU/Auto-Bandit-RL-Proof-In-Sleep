from publication_guard_v1 import *
fixed()
old=(RUN/'commit-and-build-site-v1.py').read_text(encoding='utf8')
old=old.replace("load(RUN/'candidate-diff-audit-v1.json')['full_whitespace_gate_passed']","load(RUN/'candidate-diff-audit-v2.json')['scoped_whitespace_gate_passed']")
write(RUN/'commit-and-build-site-v2.py',old)
fixed()
