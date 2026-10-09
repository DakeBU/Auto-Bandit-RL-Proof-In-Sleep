from common import *
fixed()
st=load(CONTRACT/'stabilized-v1.json'); t=st['targets'][0]
assert load(RUN/'first-leaf-public-inspected-v2.json')['actual_exit']==0
assert sha(PUBLIC)==load(RUN/'first-leaf-public-inspected-v2.json')['module_sha256']
assert load(RUN/'native-first-focused-trial-v2.json')['actual_exit']==1
assert not (RUN/'trials.jsonl').exists()
write(RUN/'first-leaf-native-trial-failure-v3.json',dict(actual_failed_receipt_sha256=sha(RUN/'native-first-focused-trial-v2.json'),failure='Native schema rejects kind=proof. Allowed actual kinds plan/attempt/build/review/proposal/compression/handoff/export, from its error and actual implementation.',repair='Use kind=build for actual successful focused build record; do not rerun already successful focused/value/event commands.',production_or_frozen_header_changed=False,prior_native_event_success_retained=True))
capture('native-first-focused-trial-v3',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','actual-shared-cumulative-sum-v1','--lean',PUBLIC.relative_to(ROOT),'--statement-hash',t['statement_sha256'],'--progress-class','compiled-leaf','--verifier-evidence',RUN/'first-leaf-focused-inspected-v1.json','--verifier-evidence',RUN/'first-leaf-public-inspected-v2.json','--notes','Actual focused module Built and full generic public theorem VALUE with actual iterate_one_step parent. Exact frozen header unchanged. Probe v1 ppExpr and native trial kind=proof failures retained; successful v2 public probe/event not rerun; valid native kind=build. Generic proof compiled only: concrete canary/package BODY/integration/root/fullharness/site/source/chapter acceptance pending. Whole Goal ACTIVE.')
changes=[]
snapshot={r['path']:r for r in load(RUN/'pre-stabilization-native-exact-v1.json')['rows']}
for row in load(RUN/'contract-review-inputs-v1.json')['rows']:
    if sha(row['path'])!=row['sha256']:
        assert row['path'] in snapshot and snapshot[row['path']]['sha256']==row['sha256']
        assert hashlib.sha256(base64.b64decode(snapshot[row['path']]['raw_base64'])).hexdigest()==row['sha256']
        changes.append(dict(path=row['path'],before_sha256=row['sha256'],after_sha256=sha(row['path']),before_snapshot='pre-stabilization-native-exact-v1.json',permitted_transition='actual OWN stabilized/proving/focused-compiled events'))
assert len(changes)==2
write(RUN/'first-leaf-historical-binding-resolution-v1.json',dict(changes=changes,all_other_contract_inputs_unchanged=True,source_container_closed=False,whole_Goal_status='ACTIVE'))
write(RUN/'first-leaf-BODY-review-inputs-v1.json',dict(rows=rows(list(CONTRACT.glob('*'))+[PUBLIC]+[p for p in RUN.glob('*') if p.is_file() and p.suffix!='.png' and not p.name.startswith('CLI-help')]),permitted_prospective_next_leaves=['iterate_fixed_sharp','iterate_variable_sharp'],no_terminal_change=True,concrete_canary_and_package_acceptance_pending=True,whole_Goal_status='ACTIVE'))
fixed()
print('Actual valid build trial recorded; historical binding transitions resolved. First-leaf BODY review pending.')
