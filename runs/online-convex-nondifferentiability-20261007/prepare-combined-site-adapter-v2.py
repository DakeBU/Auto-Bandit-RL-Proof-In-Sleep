"""Bind later site acceptance to the real repaired combined gate, not failed v1."""
from common_v4 import *
old=RUN/'source-site-gates-v1.py';new=RUN/'source-site-gates-v2.py'
t=old.read_text(encoding='utf-8');assert "passed('project-gates-v1-01')" in t
t=t.replace("passed('project-gates-v1-01')","passed('project-gates-v2-01');passed('full-harness-v2-01')")
write(new,t);compile(t,str(new),'exec')
write(RUN/'combined-site-adapter-pre-use-v2.json',dict(original_unused=old.as_posix(),effective=new.as_posix(),effective_sha256=sha(new),reason='Original full harness v1 failed its existing tracked-source fence; site must require separately recorded real v2 combined/full harness success',executed_site_failure=False,source_math_headers_unchanged=True))
print('Prepared immutable v2 site adapter requiring true repaired combined gates.')
