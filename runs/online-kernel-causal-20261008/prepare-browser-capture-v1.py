from common_body_v1 import *

fixed_integrated()
old = ROOT/'runs/online-completed-causal-20261008'
cjs = (old/'capture-reader-v5.cjs').read_text(encoding='utf8')
cjs = cjs.replace("nodes.length!==4","nodes.length!==5").replace('Missing four new public nodes','Missing five new public nodes')
cjs = cjs.replace('completed-causal-source-card','kernel-causal-source-card').replace('actual-four-new-proof-notes','actual-five-new-proof-notes')
cjs = cjs.replace('-v5','-v1')
write(RUN/'capture-reader-v1.cjs',cjs)
py = (old/'capture-reader-v5.py').read_text(encoding='utf8')
py = py.replace('from common_reader_v5 import *','from common_body_v1 import *')
py = py.replace('online-completed-causal','online-kernel-causal').replace('-v5','-v1')
py = py.replace("ROOT / 'runs/online-ae-causal-20261008/formula-render-v1-browser.json'",
    "ROOT / 'runs/online-completed-causal-20261008/formula-render-v5-browser.json'")
py = py.replace("'targets-v1.json'","'targets-v2.json'")
py = py.replace("len(r['panels']) == 5 and len(r['modulePanels']) == 4 and len(r['images']) == 10",
    "len(r['panels']) == 6 and len(r['modulePanels']) == 5 and len(r['images']) == 12")
py = py.replace('10 actual original current images','12 actual original current images')
write(RUN/'capture-reader-v1.py',py)
write(RUN/'browser-capture-reuse-v1.json',dict(original_files=raw_index([
    old/'capture-reader-v5.cjs',old/'capture-reader-v5.py']),
    new_files=raw_index([RUN/'capture-reader-v1.cjs',RUN/'capture-reader-v1.py']),
    adaptations=['five actual registry targets, six source/note panels, five catalogue panels and one first viewport =12 images',
      'new owned profile/output names and targets-v2 frozen names',
      'previous actual source guide math count plus ONE source card',
      'shared body guard; retained red-command/mjx-error and overflow/full-header checks'],
    generated_site_unmodified=True,actual_capture_not_yet_run=True))
fixed_integrated()
print('Adapted owned12-image browser capture protocol saved; no browser/render success claim.',flush=True)
