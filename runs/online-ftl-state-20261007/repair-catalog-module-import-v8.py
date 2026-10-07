from common_v1 import *
write(RUN/'catalog-implementation-invocation-failure-v7.json',dict(command=['python','-B','-X','utf8','runs/online-ftl-state-20261007/implement-catalog-repair-v7.py'],exit_code=1,observed_stderr="ModuleNotFoundError: No module named 'website'",evidence_origin='Actual exec_command output; no separate subprocess log existed.',cause='Direct script sys.path starts at run directory; repository package root absent.',mutation_before_failure='none',repair='Versioned helper inserts ROOT in sys.path; source/math untouched.'))
source=(RUN/'implement-catalog-repair-v7.py').read_text(encoding='utf-8')
source=source.replace('from website.scripts import build_site as site','sys.path.insert(0,str(ROOT))\nfrom website.scripts import build_site as site')
write(RUN/'implement-catalog-repair-v8.py',source)
