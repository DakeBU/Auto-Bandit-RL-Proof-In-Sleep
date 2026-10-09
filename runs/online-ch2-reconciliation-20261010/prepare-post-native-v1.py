from publication_guard_v5 import *
fixed()
audit=load(RUN/'post-native-root-audit-v1.json')
assert audit['all_other_FINAL_inputs_unchanged'] and audit['state_exact_expected']
assert (audit['trial']['obligations_before'],audit['trial']['obligations_after'])==(9,0)
site=load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
helpers=rows(RUN/n for n in ['deliver-v1.py','collect-actual-delivery-v1.py','final-evidence-delivery-v1.py'])
write(RUN/'prospective-delivery-helper-bindings-v1.json',dict(rows=helpers,stage=load(RUN/'candidate-stage-plan-v1.json')['stage'],stacked_base=BASE,merge=False,deploy=False,retire=False))
write(RUN/'post-native-packet-v1.md',(RUN/'post-native-packet-proposal-v1.md').read_bytes())
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(row['path']) for row in load(RUN/'FINAL-inputs-v1.json')['rows'])
paths.add(RUN/'trials.jsonl')
write(RUN/'post-native-inputs-v1.json',dict(rows=rows(paths),FINAL_sha256=sha(RUN/'FINAL-review-v1.json'),scope='Actual own9productionproofterminal native acceptance and prospective scoped draftPR;4definitions8FULLcanariesseparateONEsourcefamily;notchapter/Goalcompletion',actual_delivery_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual postnative and exact prospective scoped delivery packet prepared; distinct review pending.',flush=True)
