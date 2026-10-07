from common_v1 import *
fixed(proving=True,integrated=True)
old=Path('runs/online-foundations-public-20261007/audit-committed-raw-v1.py').read_text(encoding='utf-8')
write(RUN/'audit-committed-raw-v1.py',old.replace('codex/research-online-foundations-migration',BRANCH).replace('fixed(True)','fixed(proving=True,integrated=True)'))
write(RUN/'publication-tools-before-FINAL-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['record-acceptance-v1.py','prepare-publication-v1.py','create-pr-v1.py','complete-publication-v1.py','prepare-delivery-v1.py','audit-committed-raw-v1.py']],scope='Bounded authorized pipeline prepared; actual FINAL binds before execution. No native acceptance/push/API yet.',new_public_math=2,new_named_validation_proofs=6,goal_complete=False))
