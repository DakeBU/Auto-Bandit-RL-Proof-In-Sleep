from common import *
import re
fixed()
st=load(CONTRACT/'stabilized-v1.json'); ts=st['targets']
assert load(RUN/'variable-printed-focused-inspected-v1.json')['compiled']
assert sha(PUBLIC)==load(RUN/'variable-printed-focused-inspected-v1.json')['module_sha256']
context=st['context'].split('noncomputable section',1)[1]
probe='import BanditRLProof.OnlinePrescientBregmanRegret\nimport Lean\nnoncomputable section\n'+context+'\n'
args=['V X hV ψ hd η loss x0 x T hseq hinterior hη hf hs u hu','V X hV ψ hd η hη loss x0 x T hseq hinterior hf hs u hu','V X hV ψ hd η loss x0 x T hT hseq hinterior hη hmono hf hs u hu M hbound','V X hV hVX ψ hc hd η hη loss x0 x T hseq hinterior hf hs u hu','V X hV hVX ψ hc hd η loss x0 x T hT hseq hinterior hη hmono hf hs u hu']
for t,a in zip(ts,args):
    probe+=t['exact_header'].replace('theorem '+t['name'],'example',1)+' := by\n  exact '+t['name']+' '+a+'\n\n#check @'+t['declaration']+'\n#print axioms '+t['declaration']+'\n\n'
probe+='end BanditRL.OnlinePrescientBregman\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let mut nodes : Array Json := #[]\n'
for t in ts:
    probe+='  do\n    let n := `'+t['declaration']+'\n    let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"\n    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)\n    let vd := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)\n    nodes := nodes.push <| Json.mkObj [("name",toJson n.toString),("has_value",toJson true),("type_dependencies",toJson (td.map Name.toString)),("value_dependencies",toJson (vd.map Name.toString))]\n'
probe+='  liftIO <| IO.FS.writeFile "runs/online-ch2-prescient-cumulative-20261009/all-five-value-graph-v1.json" (toJson nodes).pretty\n  logInfo "FIVE-COMPLETE-PUBLIC-VALUES-EXPORTED"\n'
write(RUN/'all-five-public-probe-v1.lean',probe)
code,out=capture('all-five-public-probe-command-v1','lake','env','lean',RUN/'all-five-public-probe-v1.lean',required=False)
assert code==0 and 'FIVE-COMPLETE-PUBLIC-VALUES-EXPORTED' in out,(code,out)
axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',out)
assert len(axioms)==5 and all(set(map(str.strip,s.split(',')))=={'propext','Classical.choice','Quot.sound'} for s in axioms)
graph=load(RUN/'all-five-value-graph-v1.json'); nd={n['name']:n for n in graph}
pairs=[(ts[0]['declaration'],'BanditRL.OnlinePrescientBregman.iterate_one_step'),(ts[1]['declaration'],ts[0]['declaration']),(ts[2]['declaration'],ts[0]['declaration']),(ts[2]['declaration'],'BanditRL.OnlineGradientDescent.weighted_potential_sum'),(ts[3]['declaration'],ts[1]['declaration']),(ts[3]['declaration'],'BanditRL.OnlineBregman.divergence_nonneg'),(ts[4]['declaration'],ts[2]['declaration']),(ts[4]['declaration'],'BanditRL.OnlineBregman.divergence_nonneg')]
for a,b in pairs: assert b in nd[a]['value_dependencies'],(a,b)
fences=['first-leaf-fence-v1.json','fixed-sharp-fence-v1.json','variable-sharp-fence-v1.json','fixed-printed-fence-v1.json','variable-printed-fence-v1.json']
for i,(t,fence) in enumerate(zip(ts,fences)):
    assert t['exact_header'] in PUBLIC.read_text(encoding='utf8')
    capture('all-five-safe-verify-%d-v1'%i,sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/fence)
write(RUN/'all-five-exact-public-v1.lean',PUBLIC.read_bytes())
write(RUN/'all-five-public-inspected-v1.json',dict(actual_exit=code,complete_generic_public_examples=5,actual_public_proof_values=5,axiom_output_lists=5,standard_only_axioms=['propext','Classical.choice','Quot.sound'],required_actual_VALUE_pairs=pairs,module_sha256=sha(PUBLIC),frozen_headers_unchanged=True,canaries_and_numeric_tails='pending separate audit',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Five complete generic public VALUES/5standardaxiomlists/8required actualVALUEparents and5frozen guards passed. Not package/source/chapter acceptance.')
