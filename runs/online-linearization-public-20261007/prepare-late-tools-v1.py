"""Prepare narrowly enumerated raw-DOM exception; original v1 tool unchanged."""
from common_v2 import *
fixed(True)
source=(RUN/'check-scoped-diff-v1.py').read_text(encoding='utf-8')
needle="elif any(p.endswith('/formula-render-v'+str(i)+'-dom.html') for i in [1,2,3]):reason='exact browser DOM bytes'"
assert source.count(needle)==1
write(RUN/'check-scoped-diff-v2.py',source.replace(needle,needle+"\n  elif p.endswith('/capture-diagnostics-v2-dom.html'):reason='exact retained diagnostic browser DOM bytes'"))
write(RUN/'late-infrastructure-scope-v1.json',dict(status='prepared-not-executed',final_fixed_inputs=472,final_fixed_inputs_unmodified=True,late_helpers=['record-acceptance-v1.py','prepare-publication-v1.py','complete-publication-v1.py','prepare-late-tools-v1.py','check-scoped-diff-v2.py','prepare-delivery-v1.py'],reason='Bounded acceptance/publication tools after frozen FINAL package; no source/Lean/reader change. All late raw files will be checked against final committed Git blobs.',raw_whitespace_exception='ONLY additional actual capture-diagnostics-v2-dom.html immutable browser bytes; production JSON/scripts/docs still checked; original v1 tool retained.',source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Late bounded infrastructure scope recorded; original472 FINAL rows unchanged.')
