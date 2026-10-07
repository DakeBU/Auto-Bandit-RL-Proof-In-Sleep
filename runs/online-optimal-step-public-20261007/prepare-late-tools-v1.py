from common_v1 import *
fixed(True);old=Path('runs/online-linearization-public-20261007')
script=(old/'complete-publication-v1.py').read_text(encoding='utf-8').replace('common_v2','common_v1').replace('check-scoped-diff-v2.py','check-scoped-diff-v1.py').replace('online-linearization-public','online-optimal-step-public').replace('causal linearization','fixed-coefficient optimal-step').replace('linearization contributor','optimal-step contributor').replace('raw linearization','raw optimal-step')
write(RUN/'complete-publication-v1.py',script)
write(RUN/'late-infrastructure-scope-v1.json',dict(status='prepared-not-executed',final_fixed_inputs=340,final_fixed_inputs_unmodified=True,late_helpers=['record-acceptance-v1.py','prepare-publication-v1.py','prepare-late-tools-v1.py','complete-publication-v1.py','prepare-delivery-v1.py'],reason='Acceptance/publication infrastructure outside frozen340 FINAL inputs; no source/Lean/reader change. Final DIRECT Git blob audit covers every late own raw file.',source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Late bounded infrastructure prepared; original340 FINAL rows unchanged.')
