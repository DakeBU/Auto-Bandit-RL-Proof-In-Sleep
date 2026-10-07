"""Identical positive bounded scope audit, with unique immutable output version."""
from common_v2 import *
p=RUN/'audit-scope-v1.py';text=p.read_text(encoding='utf-8')
text=text.replace("RUN/'source-scope-audit-v1.json'","RUN/'source-scope-audit-v2.json'")
exec(compile(text,str(p)+'-version2-output','exec'))
