from common_v1 import *
fixed(True);old=Path('runs/online-optimal-step-public-20261007')
for name in ['audit-committed-raw-v1.py','complete-publication-v1.py']:
 s=(old/name).read_text(encoding='utf-8').replace('online-optimal-step','online-unit-scaling').replace('optimal-step','unit-scaling').replace('fixed-coefficient unit-scaling','uniform coordinate unit-scaling')
 write(RUN/name,s)
s=(old/'create-pr-v1.py').read_text(encoding='utf-8').replace('codex/research-online-optimal-step-migration','__HEAD__').replace('codex/research-online-linearization-migration','codex/research-online-optimal-step-migration').replace('__HEAD__',BRANCH).replace('PR184','PR185').replace('/pulls/184','/pulls/185').replace('codex%2Fresearch-online-optimal-step-migration','codex%2Fresearch-online-unit-scaling-migration')
write(RUN/'create-pr-v1.py',s)
write(RUN/'publication-tools-before-FINAL-v1.json',dict(status='prepared-not-executed',own_tools=['complete-publication-v1.py','create-pr-v1.py','audit-committed-raw-v1.py','prepare-publication-v1.py','prepare-delivery-v1.py'],user_authorized='Scopedcommit/push/reviewable draft PR; no merge/deploy.',fresh_parent_PR=185,exact_parent=BASE,base_branch='codex/research-online-optimal-step-migration',new_math=0,FINAL_and_native_acceptance_required=True,chapter_complete=False,goal_complete=False))
print('Bounded draft publication tools prepared before FINAL; no publication action yet.')
