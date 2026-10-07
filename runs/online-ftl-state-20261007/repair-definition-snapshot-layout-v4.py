from common_v1 import *
fixed(proving=True)
frozen=(RUN/'leaves/state-definitions-frozen-v1.txt').read_bytes()
assert PUBLIC.read_bytes()==frozen+b'\nend BanditRL.OnlineLearning\n'
write(RUN/'definition-layout-failure-repair-v4.json',dict(actual_failed_command='python -B -X utf8 runs/online-ftl-state-20261007/repair-state-definition-identity-v3.py',actual_failed_exit=1,actual_failed_check='Snapshot text was written through rstrip/newline helper, so it lacks the one extra blank line before namespaceend',following_command_failed='continue-state-v3.py did not yet exist; shell had continued after first failure',following_exit=2,repair='Check exact raw snapshot plus explicit additional newline and namespaceend; versioned helper retains all bytes',actual_public_sha256=sha(PUBLIC),snapshot_sha256=sha(RUN/'leaves/state-definitions-frozen-v1.txt'),mathematical_target_or_body_change=False))
text=(RUN/'repair-state-definition-identity-v3.py').read_text(encoding='utf-8')
old="+'end BanditRL.OnlineLearning\\n'";new="+'\\nend BanditRL.OnlineLearning\\n'"
assert text.count(old)==1
text=text.replace(old,new)
text=text.replace("prefix=(RUN/'leaves/state-definitions-frozen-v1.txt').read_text(encoding='utf-8')","prefix=(RUN/'leaves/state-definitions-frozen-v1.txt').read_text(encoding='utf-8')+'\\n'")
write(RUN/'repair-state-definition-identity-v4.py',text)
fixed(proving=True)
