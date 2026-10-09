from common import *
fixed()
st=load(CONTRACT/'stabilized-v1.json'); t=st['targets'][0]
assert load(RUN/'first-leaf-focused-inspected-v1.json')['compiled']
assert sha(PUBLIC)==load(RUN/'first-leaf-focused-inspected-v1.json')['proof_sha256']
probe='import BanditRLProof.OnlinePrescientBregmanRegret\nimport Lean\n\n'+st['context'].split('noncomputable section',1)[1]
probe='import BanditRLProof.OnlinePrescientBregmanRegret\nimport Lean\nnoncomputable section\n'+st['context'].split('noncomputable section',1)[1]
probe+='\n'+t['exact_header'].replace('theorem '+t['name'],'example',1)+' := by\n  exact iterate_divergence_sum V X hV ψ hd η loss x0 x T hseq hinterior hη hf hs u hu\n'
probe+='\n#check @'+t['declaration']+'\n#print axioms '+t['declaration']+'\nend BanditRL.OnlinePrescientBregman\n\n'
probe+='''open Lean Elab Command
run_cmd do
  let env ← getEnv
  let n := `BanditRL.OnlinePrescientBregman.iterate_divergence_sum
  let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"
  let deps := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
  unless deps.contains `BanditRL.OnlinePrescientBregman.iterate_one_step do
    throwError "Missing actual parent theorem in proof VALUE"
  let j := Json.mkObj [("name",toJson n.toString),("actual_theorem_value",toJson true),
    ("value_dependencies",toJson (deps.map Name.toString)),
    ("type",toJson (← ppExpr info.type).pretty)]
  liftIO <| IO.FS.writeFile "runs/online-ch2-prescient-cumulative-20261009/first-leaf-value-graph-v1.json" j.pretty
  logInfo "ACTUAL-FIRST-LEAF-VALUE-PARENT-CHECKED"
'''
write(RUN/'first-leaf-public-probe-v1.lean',probe)
code,out=capture('first-leaf-public-probe-command-v1','lake','env','lean',RUN/'first-leaf-public-probe-v1.lean',required=False)
assert code==0 and 'ACTUAL-FIRST-LEAF-VALUE-PARENT-CHECKED' in out,(code,out)
assert 'sorryAx' not in out and 'Classical.choice' in out and 'propext' in out and 'Quot.sound' in out
assert load(RUN/'first-leaf-value-graph-v1.json')['actual_theorem_value']
before=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']]
write(RUN/'pre-first-compiled-native-exact-v1.json',dict(rows=before))
event('native-first-focused-compiled-event-v1','focused-compiled',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],module_sha256=sha(PUBLIC),focused_exit=0,value_parent='actual iterate_one_step',public_value_probe_exit=0,canary='pending',package_candidate=False,source_container_closed=False,whole_Goal_status='ACTIVE'))
capture('native-first-focused-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','proof','--status','compiled','--run-id',RUN.name,'--attempt-id','actual-shared-cumulative-sum-v1','--lean',PUBLIC.relative_to(ROOT),'--statement-hash',t['statement_sha256'],'--progress-class','compiled-leaf','--verifier-evidence',RUN/'first-leaf-focused-inspected-v1.json','--verifier-evidence',RUN/'first-leaf-public-probe-command-v1.json','--notes','Actual new focused module Built and complete public theorem VALUE with actual iterate_one_step parent. Exact frozen header unchanged. Generic proof compiled only: concrete canary/package BODY/integration/root/fullharness/site/source/chapter acceptance pending. Whole Goal ACTIVE.')
write(RUN/'first-leaf-BODY-review-inputs-v1.json',dict(rows=rows(list(CONTRACT.glob('*'))+[PUBLIC]+[p for p in RUN.glob('*') if p.is_file() and p.suffix not in ['.png'] and not p.name.startswith('CLI-help')]),permitted_prospective_next_leaves=['iterate_fixed_sharp','iterate_variable_sharp'],no_terminal_change=True, concrete_canary_and_package_acceptance_pending=True,whole_Goal_status='ACTIVE'))
fixed()
print('Full first public application/value/standard-axiom probe passed. Package canaries/gates pending.')
print(out[-1000:])
