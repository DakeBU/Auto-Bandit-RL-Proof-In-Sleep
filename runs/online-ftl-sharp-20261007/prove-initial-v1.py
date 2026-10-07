from common_v1 import *
fixed();r=load(RUN/'source-contract-repair-receipt-v1.json');old=load(RUN/'source-contract-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
assert set(r['repair_verdicts'])=={'M1','E1','E2','M2'} and all(v['verdict']=='satisfied' for v in r['repair_verdicts'].values())
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','remaining_enumeration_repairs']:assert not r.get(k,[]),k
assert r['required_reader_corrections']==old['required_reader_corrections']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v3.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
mapping={x['original_live_path']:x for x in load(RUN/'CONTRACT-reviewed-snapshot-resolution-v3.json')['rows']}
for x in load(RUN/'source-contract-inputs-v2.json')['rows']:
 p=mapping[x['path']]['immutable_snapshot'] if x['path'] in mapping else x['path'];assert sha(p)==x['sha256']
write(CONTRACT/'stabilized-contract-v1.json',dict(stage='stabilized',mathematical_version=1,effective_binding_index=3,effective_ledger=3,source_review_receipt_sha256=sha(RUN/'source-contract-repair-receipt-v1.json'),all_original13_targets_unchanged=True,original_rejected_review_retained=True,required_maintext_source_items=16,mandatory_proof_total=None,required_open_subobligations=['general initialization','causal streaming state producer','W/V model mapping','logarithmic unavoidable lower-bound/source-claim audit'],new_proofs_pending=2,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,repair_receipt=(RUN/'source-contract-repair-receipt-v1.json').as_posix(),all13_targets_unchanged=True,new_source_terminals=2,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower-initial-v1.md','/root staged lowerworker, single route/medium. Dependency-ready initial source1/4 terminal: unfold actual initial predictor1/2 and one-target mean=y0; interval implies y0*(1-y0)>=0; nlinarith closes square inequality. No extra assumption/statement change. Candidate requires real focused build, #check/axioms/exactN06rfl, actual endpoint/midpoint/outside witness, full source guard. Refined terminal waits for this leaf.')
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,leaf=PRE+'meanPredict_initial_stability',ready_dependencies=['actual meanPredict/empiricalMean definitions','Mathlib interval/order/square algebra'],single_lower_route=True,allowed_source_edit='Append exact two reviewed headers only; all original five proofs/one definition untouched',chapter_complete=False,goal_complete=False)))
oldbytes=PUBLIC.read_bytes();end=b'end BanditRL.OnlineLearning\r\n' if oldbytes.endswith(b'\r\n') else b'end BanditRL.OnlineLearning\n';assert oldbytes.endswith(end)
header=load(CONTRACT/'new-public-headers-v1.json')['meanPredict_initial_stability']
body=''' := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
  nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]

'''
PUBLIC.write_bytes(oldbytes[:-len(end)]+('/-- Orabona v10 Theorem 1.3 proof, printed p5: the initial stability term is at most 1/4. -/\n'+header+body).encode('utf-8')+end)
fixed(proving=True)
gate('focused-initial-v1','lake','build','BanditRLProof.OnlineLearningFTL')
scratch=(RUN/'leaves/neutral-closed-props-v1.lean').read_text(encoding='utf-8')
probe='import BanditRLProof.OnlineLearningFTL\n'+scratch+'''
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N06 = propositionOf (@BanditRL.OnlineLearning.meanPredict_initial_stability) := by rfl
#check BanditRL.OnlineLearning.meanPredict_initial_stability
#print axioms BanditRL.OnlineLearning.meanPredict_initial_stability
open BanditRL.OnlineLearning
example : (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 :=
  meanPredict_initial_stability _ (by norm_num)
example : (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4 :=
  meanPredict_initial_stability _ (by norm_num)
example : (meanPredict (fun _ => (1:ℝ)/2) 0 - 1/2)^2 - (empiricalMean (fun _ => (1:ℝ)/2) 1 - 1/2)^2 = 0 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
example : (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 > (1:ℝ)/4 := by
  norm_num [meanPredict, empiricalMean, Finset.sum_range_succ]
'''
write(RUN/'leaves/initial-type-axiom-canary-v1.lean',probe);gate('initial-type-axiom-canary-v1','lake','env','lean',RUN/'leaves/initial-type-axiom-canary-v1.lean')
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
actual=lean_declaration_header(PUBLIC,'meanPredict_initial_stability');write(CONTRACT/'native-initial-header-v1.txt',actual)
full=load(CONTRACT/'new-public-headers-v1.json')['meanPredict_initial_stability']
assert re.sub(r'\s+',' ',actual).strip()==re.sub(r'\s+',' ',full).strip()
write(CONTRACT/'initial-full-guard-v1.json',dict(schema_version=1,declaration='meanPredict_initial_stability',file=PUBLIC.as_posix(),statement=actual,statement_hash=hashlib.sha256(actual.encode()).hexdigest(),source_assumptions=['(hy : y 0 ∈ Set.Icc (0 : ℝ) 1)'],created_at='2026-10-07'))
native('initial-full-statement-fence-v1','statement-fence','--file',PUBLIC,'--declaration','meanPredict_initial_stability','--contract',CONTRACT/'initial-full-guard-v1.json')
native('initial-worker-compiled-trial-v1','trial-log','--task',TASK,'--role','lean-worker','--kind','lean','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-SHARP-INITIAL-V1','--statement-hash',hashlib.sha256(actual.encode()).hexdigest(),'--new-declaration',PRE+'meanPredict_initial_stability','--changed-file',PUBLIC,'--verifier-evidence',RUN/'initial-type-axiom-canary-v1-exit.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual source initial1/4 proof focused build, exactN06rfl/#check/axioms and endpoint/midpoint/outsideinterval canaries passed. One new source-bound prerequisite closed locally; refined terminal/BODY/combined/reader/FINAL/native/PR/chapter/Goal pending.')
write(RUN/'initial-leaf-compiled-v1.json',dict(status='compiled-local source-bound prerequisite',public_name=PRE+'meanPredict_initial_stability',source_anchor='Theorem1.3 proof printed5/PDF17',full_native_header_sha256=hashlib.sha256(actual.encode()).hexdigest(),raw_frozen_header_sha256=sha(CONTRACT/'new-public-headers-v1.json'),actual_guards_types_axioms_endpoint_canaries_passed=True,initial_source_bound_closed_locally=True,refined_source_terminal_pending=True,BODY_review_pending=True,chapter_complete=False,goal_complete=False))
fixed(proving=True);print('Actual new initial1/4 source-bound leaf compiled with full type/axiom/fence/canary; refined endpoint remains next.')
