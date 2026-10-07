from common_v1 import *
fixed(True)
old=Path('runs/online-unit-scaling-public-20261007/audit-committed-raw-v1.py').read_text(encoding='utf-8')
write(RUN/'audit-committed-raw-v1.py',old.replace('codex/research-online-unit-scaling-migration',BRANCH))
write(RUN/'publication-tools-before-FINAL-v1.json',dict(rows=[dict(path=(RUN/n).as_posix(),sha256=sha(RUN/n)) for n in ['record-acceptance-v1.py','prepare-publication-v1.py','create-pr-v1.py','complete-publication-v1.py','prepare-delivery-v1.py','audit-committed-raw-v1.py']],scope='Prepared bounded authorized pipeline; all tools will be bound in actual FINAL before use. No acceptance/push/API yet.',new_public_math=0,new_named_validation_proofs=7,goal_complete=False))
