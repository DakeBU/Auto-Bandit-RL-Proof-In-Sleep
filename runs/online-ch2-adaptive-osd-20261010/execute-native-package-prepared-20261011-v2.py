from native_package_guard_prepared_20261011_v2 import *
parser=argparse.ArgumentParser();parser.add_argument('--plan',type=Path,required=True);parser.add_argument('--final',type=Path,required=True);a=parser.parse_args()
p,f=final_guard(a.plan,a.final);tag=p['tag']
# Durable create-only start: partial execution is never automatically replayed.
write(RUN/('native-package-started-'+tag+'.json'),dict(plan=rows([a.plan]),FINAL=rows([a.final]),state_before=rows([RUN/'lifecycle-state.json']),boundary='No automatic retry. On failure retain all output and obtain a bounded recovery plan.'))
state_expected,events_expected=predict_state(p,a.final)
write(RUN/('native-state-expected-'+tag+'.json'),dict(before=next(r for r in p['mutable_originals'] if r['path']==(RUN/'lifecycle-state.json').as_posix()),expected_after_object=state_expected,expected_two_events_without_timestamps=events_expected,scope='Prospective semantic exact transition derived from frozen state+FINAL; actual RAW hashes only after native execution'))
for kind,payload in [('candidate',payloads(p,a.final)[0])]:
    event('native-package-'+kind+'-'+tag,kind,payload)
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','thirty-frozen-adaptive-osd-proof-contracts-'+tag,'--progress-class','closed-frontier','--reviewer-validated','--obligations-before','30','--obligations-after','0']
for name in p['proof_contracts']:args+=['--new-declaration',name]
args+=['--notes',BOUNDARY,'--verifier-evidence',a.final.as_posix()]
capture('native-package-trial-'+tag,*args)
event('native-package-accepted-'+tag,'accepted',payloads(p,a.final)[1])
for path in DOCS:
    before=base64.b64decode(next(r for r in p['mutable_originals'] if r['path']==path.as_posix())['RAW_base64'])
    assert path.read_bytes()==before
    path.write_bytes(before+render(p['document_suffix_template'],a.final,p['site_head']).encode('utf8'))
contract=dict(package=TASK,status='accepted-local-bounded-package',FINAL=rows([a.final]),native_plan=rows([a.plan]),counts=COUNTS,proof_contracts=p['proof_contracts'],source_binding=p['source_binding'],site_build_head=p['site_head'],scope=BOUNDARY,chapter_accepted=False,Goal_status='ACTIVE',native_transport='retrospective evidence transport, not contemporaneous whole-workflow enforcement',postnative_review='pending',exact_head_delivery_review='pending',contribution_manifest='Frozen candidate snapshot deliberately unchanged; actual gates/acceptance recorded here.')
write(Path(p['new_accepted_contract']),contract)
transition=transition_check(p,a.final)
final_guard(a.plan,a.final,after=True)
write(RUN/('native-package-actual-transition-'+tag+'.json'),dict(plan=rows([a.plan]),FINAL=rows([a.final]),accepted_contract=rows([Path(p['new_accepted_contract'])]),transition=transition,mutable_before=p['mutable_originals'],mutable_after=rows([Path(r['path']) for r in p['mutable_originals']]),source_binding_unchanged=True,source_manifest_reader_coverage_unchanged=True,postnative_review='required',S3_current_inspector='Will reject nonprefix lifecycle-state change until exact narrow postnative transition review and separately versioned inspector. No broad exemption granted.'))
