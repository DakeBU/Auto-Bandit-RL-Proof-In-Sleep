from common_reviewed_v1 import *
reviewed_fixed();assert load(RUN/'all-nine-focused-build-v1-exit.json')['exit_code']==1
write(RUN/'failed-all-nine-public-v1.lean.raw',PUBLIC.read_bytes())
s=PUBLIC.read_text(encoding='utf8')
assert s.count('tendsto_atTop_mono (fun n => by omega) tendsto_id')==2
s=s.replace('tendsto_atTop_mono (fun n => by omega) tendsto_id','tendsto_atTop_mono (fun n => by change n ≤ 2 * (n + 1); omega) tendsto_id',1)
s=s.replace('tendsto_atTop_mono (fun n => by omega) tendsto_id','tendsto_atTop_mono (fun n => by change n ≤ 2 * n + 1; omega) tendsto_id',1)
s=s.replace('  simp [potential, ho]','  simp only [potential, if_neg ho, neg_zero, zero_mul, zero_div]')
for x in load(CONTRACT/'targets-v1.json')['targets']:assert x['header']+' := by' in s
PUBLIC.write_bytes(s.encode('utf8'))
write(RUN/'cofinal-proof-repair-v2.json',dict(failure='all-nine-focused-build-v1',diagnosis='tendsto_id infers f=id and omega treats id n as opaque; the numerical cofinal inequality must expose id reduction. No source/math/terminal issue.',repair='Explicit change to n≤2(n+1) and n≤2n+1 before omega. Make odd remainder rewrite explicit to avoid an unused simp argument.',contract_version=1,all_nine_header_hashes_unchanged=True,source_context_unchanged=True,proof_route_unchanged=True))
native('cofinal-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Cofinal map arithmetic elaboration failed with opaque id n',evidence=(RUN/'cofinal-proof-repair-v2.json').as_posix(),contract_version=1,source_terminal_unchanged=True)))
native('cofinal-proving-event-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(reason='Same reviewed contract; explicit id reduction in proof-local repair',frozen_targets_sha256=sha(CONTRACT/'targets-v1.json'))))
gate('all-nine-focused-build-v2','lake','build','BanditRLProof.OnlineNoRegretSemantics')
write(RUN/'leaf-progress-v2.json',dict(contract_target_count=9,closed_public_targets=[x['name'] for x in load(CONTRACT/'targets-v1.json')['targets']],remaining_contract_targets=[],public_sha256=sha(PUBLIC),new_public_proofs=9,new_public_definitions=3,source_body_review_pending=True,public_canary_and_combined_full_gates_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
reviewed_fixed();print('All nine exact theorem bodies now compile; kernel/canary/body/integrated gates remain')
