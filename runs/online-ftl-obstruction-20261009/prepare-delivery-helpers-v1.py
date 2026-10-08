from common_body_v2 import *
integrated_fixed()
source=(ROOT/'runs/online-ftl-limit-20261009/commit_owned_v1.py').read_text(encoding='utf8')
source=source.replace('from common_accepted_v2 import *','from common_accepted_v1 import *')
write(RUN/'commit_owned_v1.py',source)
print('Owned commit guard prepared; no commit or publication executed.',flush=True)
