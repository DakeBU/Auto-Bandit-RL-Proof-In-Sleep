"""Resolve the authorized additive MANIFEST prefix to immutable reviewed bytes."""
from common_v2 import *
assert load(RUN/'integrate-reader-v3-01-exit.json')['exit_code']!=0
assert load(RUN/'reader-prefix-binding-diagnostic-v4.json')['mismatches'][0]['path']=='MANIFEST.md'
assert len(load(RUN/'reader-prefix-binding-diagnostic-v4.json')['mismatches'])==1
f=fixed();before=RUN/'manifest-before-affine-entry-v1.txt'
rows=[]
for row in load(RUN/'prior-contract-binding-v1.json')['rows']:
 resolved=before.as_posix() if row['path']=='MANIFEST.md' else row['resolved'];assert sha(resolved)==row['sha256'];rows.append(dict(path=row['path'],sha256=row['sha256'],resolved=resolved))
assert Path('MANIFEST.md').read_bytes().startswith(before.read_bytes())
write(RUN/'prior-contract-binding-reader-overlay-v4.json',dict(status='passed',rows=rows,original_binding_record_unmodified=True,only_new_resolution='Authorized additive historical candidate MANIFEST entry resolves to exact pre-entry raw snapshot; no reviewed bytes rewritten.'))
text=(RUN/'integrate-reader-v3.py').read_text(encoding='utf-8').replace("load(RUN/'prior-contract-binding-v1.json')['rows']","load(RUN/'prior-contract-binding-reader-overlay-v4.json')['rows']")
write(RUN/'integrate-reader-v4.py',text);compile(text,str(RUN/'integrate-reader-v4.py'),'exec');generated('reader-prefix-repair-before-use-v4.json',[RUN/'integrate-reader-v4.py'])
write(RUN/'reader-prefix-repair-v4.json',dict(status='repair-prepared-fresh-integration-required',actual_failed_attempt='integrate-reader-v3-01',cause='Preserved CONTRACT binding pointed to then-current MANIFEST; separately additive candidate entry changed current bytes. Original raw prefix matches exact saved snapshot.',resolution='Additive explicit reader-resolution overlay, old binding/report/receipt unchanged; new v4 verifies all171 raw rows with only MANIFEST redirected to its exact immutable snapshot.',mathematical_repairs=[],original_module_canary_headers_unchanged=True,chapter_complete=False,goal_complete=False))
event('repair',dict(failure='metadata original MANIFEST pointer after authorized candidate append',resolution='verified immutable exact raw pre-entry prefix; additive pointer overlay',frozen_headers=f['headers'],mathematical_repairs=[],source_package_accepted=False),'reader-prefix-v4')
print('All original CONTRACT bytes rechecked; exact MANIFEST prefix resolution explicit, original records unchanged.')
