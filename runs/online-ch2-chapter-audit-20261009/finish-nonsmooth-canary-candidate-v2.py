from lower_common_v1 import *
import re

reviewed(); current=headers(3)
test=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'
c=load(CONTRACT/'nonsmooth-canary-contracts-v2.json')
b=load(RUN/'nonsmooth-canaries-focused-build-v2.json')
out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
assert 'warning: Tests/OnlineNonsmoothExamplesCanary.lean' not in out
for t in c['targets']:
    assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
pub=load(RUN/'nonsmooth-canaries-public-values-v1.json')
stdout=base64.b64decode(pub['stdout_base64']).decode('utf8')
assert pub['actual_exit']==0
assert hashlib.sha256(base64.b64decode(pub['stdout_base64'])).hexdigest()==pub['stdout_sha256']
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout,re.S)
assert [name for name,_ in found]==[t['declaration'] for t in c['targets']]
axioms=[]
for name,record in found:
    values=re.findall(r'[A-Za-z_.]+',record)
    assert set(values)=={'propext','Classical.choice','Quot.sound'}
    axioms.append(dict(declaration=name,axioms=values))
write(RUN/'nonsmooth-graph-receipt-collision-failure-v1.json',dict(
    failed_helper='finish-nonsmooth-canary-candidate-v1.py',helper_actual_exit=1,
    classification='Evidence artifact path collision: successful public value kernel retained; graph exporter created JSON at the same path selected for its command receipt, then create-only receipt writer refused overwrite.',
    public_value_actual_exit=0,preserved_public_value_receipt_sha256=sha(RUN/'nonsmooth-canaries-public-values-v1.json'),
    preserved_exported_graph_sha256=sha(RUN/'nonsmooth-compiled-selected-graph-v1.json'),
    original_export_command_exit_not_durably_recorded=True,
    repair='Fresh deterministic graph export uses distinct data and command receipt paths. Do not repeat successful public-value compilation or overwrite the prior graph/failure/helper.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('nonsmooth-compiled-selected-graph-command-v2','lake','env','lean','--run',RUN/'export-nonsmooth-dependencies-v1.lean',RUN/'nonsmooth-compiled-selected-graph-data-v2.json')
assert (RUN/'nonsmooth-compiled-selected-graph-v1.json').read_bytes()==(RUN/'nonsmooth-compiled-selected-graph-data-v2.json').read_bytes()
graph=load(RUN/'nonsmooth-compiled-selected-graph-data-v2.json')
nodes={n['name']:n for n in graph['nodes']}
required=load(RUN/'nonsmooth-graph-required-value-pairs-v1.json')['pairs']
for a,z in required: assert z in nodes[a]['value_dependencies'],(a,z)
write(RUN/'nonsmooth-compiled-graph-inspected-v1.json',dict(
    selected_nodes=len(graph['nodes']),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),
    required_actual_VALUE_pairs=required,graph_sha256=sha(RUN/'nonsmooth-compiled-selected-graph-data-v2.json'),
    actual_export_command_receipt_sha256=sha(RUN/'nonsmooth-compiled-selected-graph-command-v2.json'),
    actual_export_command_exit=0,preserved_v1_and_fresh_v2_graph_bytes_identical=True,
    boundary='Selected actual proof dependencies, not all-library registry, transitive occurrence graph or theorem/coverage count.'))
fences=[]
for i,(t,p) in enumerate([(t,PRODUCTION) for t in reviewed()['targets']]+[(t,test) for t in c['targets']],1):
    f=RUN/'nonsmooth-native-fences-v1'/('%02d.json'%i)
    capture('nonsmooth-fence-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','statement-fence',
        '--declaration',t['declaration'],'--file',p,'--output',f)
    assert load(f)['statement_hash']==t['statement_hash']
    _,safe=capture('nonsmooth-safe-%02d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','safe-verify',
        '--fence',f,'--lean-file',PRODUCTION,'--lean-file',test)
    report=json.loads(safe)
    assert report['ok'] and report['findings']==[]
    fences.append(dict(declaration=t['declaration'],statement_hash=t['statement_hash'],fence_sha256=sha(f),actual_safe_report=report))
write(RUN/'nonsmooth-canaries-candidate-v1.json',dict(
    phase='Five actual proof bodies compiled at frozen v2 types; distinct canary contract/BODY review pending',
    test_module=test.relative_to(ROOT).as_posix(),test_module_sha256=sha(test),
    production_module_sha256=sha(PRODUCTION),frozen_canary_contract_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v2.json'),
    neutral_reconstruction_sha256=sha(RUN/'nonsmooth-canary-blind-receipt-v2.json'),
    actual_focused_build_sha256=sha(RUN/'nonsmooth-canaries-focused-build-v2.json'),
    actual_public_complete_value_kernel_sha256=sha(RUN/'nonsmooth-canaries-public-values-v1.json'),actual_axioms=axioms,
    native_fences_and_safe_checks=fences,safe_verify_is_compilation=False,
    actual_selected_graph_evidence_sha256=sha(RUN/'nonsmooth-compiled-graph-inspected-v1.json'),
    retained_first_failed_build_sha256=sha(RUN/'nonsmooth-canaries-focused-build-v1.json'),
    retained_artifact_collision_failure_sha256=sha(RUN/'nonsmooth-graph-receipt-collision-failure-v1.json'),
    source_family_count=2,production_proof_count=3,canary_proof_count=5,
    full_root_Tests_harness_reader_registry_site_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('nonsmooth-canaries-candidate-event-v1','candidate',dict(
    leaf='five complementary concrete canaries',actual_kernel='compiled',
    proof_receipt=sha(RUN/'nonsmooth-canaries-candidate-v1.json'),distinct_BODY_review_pending=True,
    chapter_complete=False,goal_complete=False))
reviewed();headers(3)
print('Five exact public-value kernels, standard-only axioms, actual direct VALUE pairs and eight native guards inspected; canary BODY acceptance pending.')
