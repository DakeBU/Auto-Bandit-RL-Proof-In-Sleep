"""Preserve actual failed audit and fresh diagnostics without inventing its cause."""
from common_v1 import *
import ast
fixed(True)
assert load(RUN/'complete-delivery-gates-v1-01-exit.json')['exit_code']==1
assert load(RUN/'committed-raw-audit-v1-01-exit.json')['exit_code']==1
key=(RUN.relative_to(ROOT)/'accepted-frontier-refresh-v1-exit.json').as_posix()
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()
command=['git','ls-tree','-r','-z','--full-tree',head,'--',RUN.relative_to(ROOT).as_posix()]
raw=subprocess.check_output(command);objects={e.split(bytes([9]),1)[1].decode('utf-8'):e.split(bytes([9]),1)[0].split()[2].decode('ascii') for e in raw.split(bytes([0])) if e}
assert key in objects
blob=subprocess.check_output(['git','cat-file','blob',objects[key]]);assert hashlib.sha256(blob).hexdigest()==sha(key)
separators=[]
for p in [RUN/'audit-committed-raw-v1.py',Path('runs/online-osd-public-20261007/audit-committed-raw-v1.py')]:
 b=[list(n.value) for n in ast.walk(ast.parse(p.read_text(encoding='utf-8'))) if isinstance(n,ast.Constant) and isinstance(n.value,bytes)]
 assert b==[[0],[9],[9]];separators.append(dict(path=p.as_posix(),sha256=sha(p),actual_byte_separators=b))
write(RUN/'delivery-audit-diagnostic-tree-v1.bin',raw)
write(RUN/'delivery-audit-diagnostic-v1.json',dict(status='original mismatch not reproduced by fresh explicit-head/full-tree diagnostic',audited_head=head,command=command,tree_sha256=sha(RUN/'delivery-audit-diagnostic-tree-v1.bin'),tree_files=len(objects),missing_reported_path=key,path_present_in_actual_tree=True,git_blob=objects[key],git_blob_raw_sha256=hashlib.sha256(blob).hexdigest(),current_file_sha256=sha(key),separator_checks=separators,git_prefix=subprocess.check_output(['git','rev-parse','--show-prefix'],encoding='utf-8').strip(),initial_failed_auditor_did_not_capture_tree_or_head_in_output=True,initial_mechanism='unresolved; do not claim a proven NUL/quoting/cache cause',proof_reader_and_frozen_sources_unchanged=True,publication_not_attempted=True,chapter_complete=False,goal_complete=False))
write(RUN/'delivery-audit-repair-v1.md','Preserved actual complete-delivery-gates-v1-01/committed-raw-audit-v1-01 exit1. Failure reported a committed native exit file missing from the ls-tree dictionary. Fresh exact-head full-tree diagnostic proves that same path is present and its Git blob matches raw file bytes; both original parsers actually use correct NUL/TAB separators. The initial auditor did not capture its tree/head, so its mechanism is unresolved, not falsely labeled an escaping/cache repair. Version2 captures explicit full-tree command/head and raw tree after validating EVERY current nonignored RUN file against actual Git blobs. No exclusion/weakening, source/reader/Lean edit or old evidence replacement. New logs/diagnostic and repair tools must be committed BEFORE the new audit. Separate metadata review required before publication; original failed files remain immutable. Scientific accepted scope unchanged; delivery pending, whole Goal ACTIVE.')
print('Fresh explicit Git tree contains the reported path and raw blob matches; initial mechanism unresolved, strict captured audit2 required.')
