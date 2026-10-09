from common import *
import re
fixed()
st=load(CONTRACT/'stabilized-v1.json'); ts=st['targets'][:3]
assert load(RUN/'variable-sharp-focused-inspected-v1.json')['compiled']
assert sha(PUBLIC)==load(RUN/'variable-sharp-focused-inspected-v1.json')['module_sha256']
context=st['context'].split('noncomputable section',1)[1]
probe='import BanditRLProof.OnlinePrescientBregmanRegret\nimport Lean\nnoncomputable section\n'+context+'\n'
args=['V X hV ψ hd η loss x0 x T hseq hinterior hη hf hs u hu','V X hV ψ hd η hη loss x0 x T hseq hinterior hf hs u hu','V X hV ψ hd η loss x0 x T hT hseq hinterior hη hmono hf hs u hu M hbound']
for t,a in zip(ts,args):
    probe+=t['exact_header'].replace('theorem '+t['name'],'example',1)+' := by\n  exact '+t['name']+' '+a+'\n\n#check @'+t['declaration']+'\n#print axioms '+t['declaration']+'\n\n'
probe+='end BanditRL.OnlinePrescientBregman\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let mut nodes : Array Json := #[]\n'
for t in ts:
    probe+='  do\n    let n := `'+t['declaration']+'\n    let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"\n    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)\n    let vd := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)\n    nodes := nodes.push <| Json.mkObj [("name",toJson n.toString),("has_value",toJson true),("type_dependencies",toJson (td.map Name.toString)),("value_dependencies",toJson (vd.map Name.toString))]\n'
probe+='  liftIO <| IO.FS.writeFile "runs/online-ch2-prescient-cumulative-20261009/three-proof-value-graph-v1.json" (toJson nodes).pretty\n  logInfo "THREE-COMPLETE-PUBLIC-VALUES-EXPORTED"\n'
write(RUN/'three-proof-public-probe-v1.lean',probe)
code,out=capture('three-proof-public-probe-command-v1','lake','env','lean',RUN/'three-proof-public-probe-v1.lean',required=False)
assert code==0 and 'THREE-COMPLETE-PUBLIC-VALUES-EXPORTED' in out,(code,out)
axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',out)
assert len(axioms)==3 and all(set(map(str.strip,s.split(',')))=={'propext','Classical.choice','Quot.sound'} for s in axioms)
graph=load(RUN/'three-proof-value-graph-v1.json'); nd={n['name']:n for n in graph}
pairs=[(ts[0]['declaration'],'BanditRL.OnlinePrescientBregman.iterate_one_step'),(ts[1]['declaration'],ts[0]['declaration']),(ts[2]['declaration'],ts[0]['declaration']),(ts[2]['declaration'],'BanditRL.OnlineGradientDescent.weighted_potential_sum')]
for a,b in pairs: assert b in nd[a]['value_dependencies'],(a,b)
for i,t in enumerate(ts):
    assert t['exact_header'] in PUBLIC.read_text(encoding='utf8')
    fence=['first-leaf-fence-v1.json','fixed-sharp-fence-v1.json','variable-sharp-fence-v1.json'][i]
    capture('three-proof-safe-verify-%d-v1'%i,sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/fence)
before=PUBLIC.read_bytes();write(RUN/'three-proof-exact-public-v1.lean',before)
write(RUN/'three-proof-public-inspected-v1.json',dict(actual_exit=code,complete_generic_public_examples=3,actual_public_proof_values=3,axiom_output_lists=3,standard_only_axioms=['propext','Classical.choice','Quot.sound'],required_actual_VALUE_pairs=pairs,module_sha256=sha(PUBLIC),frozen_headers_unchanged=True,concrete_canaries='draft statements only; pending bodies',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'three-proof-obligations-focused-v1.json',dict(terminals=[dict(declaration=t['declaration'],statement_sha256=t['statement_sha256'],status='focused-compiled/public-value-checked; full-gates-pending') for t in ts],pending=[t['declaration'] for t in st['targets'][3:]],chapter_proof_total=None,all8Chapter2forward_containers='REQUIRED/OPEN',whole_Goal_status='ACTIVE'))
write(RUN/'three-proof-BODY-review-inputs-v1.json',dict(rows=rows(list(CONTRACT.glob('*'))+[PUBLIC]+[p for p in RUN.glob('*') if p.is_file() and p.name!='three-proof-BODY-review-inputs-v1.json']),permitted_prospective_next_leaves=['iterate_fixed_regret','iterate_variable_regret'],source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual3generic public values/3standardaxiomlists/4required VALUEparents/frozen guards passed; next2printedproofs await BODY progression review.')
