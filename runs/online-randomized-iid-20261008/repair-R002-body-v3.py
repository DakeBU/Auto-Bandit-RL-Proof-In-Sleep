from common_reviewed_v2 import *

headers_fixed(2)
assert load(RUN/'R002-focused-build-v2-exit.json')['exit_code']==1
write(RUN/'R002-failure-repair-v3.json',dict(contract_version=2,failed_body_version=2,repair_body_version=3,
    actual_failure='R002-focused-build-v2-exit.json',classification='local Lean lemma gap',
    detail='measurable_pi_lambda inferred full Nat coordinate index before expected subtype; supplied measurability was wrong typed extraction.',
    repair='Annotate finite strict-past subtype binder in measurable extraction; no terminal/context/assumption change.',
    failed_body_retained='leaves/R002-body-v2.lean', headers_sha256=sha(CONTRACT/'targets-v2.json')))
native('R002-worker-failed-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R002-V2','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--verifier-evidence',RUN/'R002-focused-build-v2-exit.json',
    '--error-signature','tuple extraction Measurable index Nat versus strict-past subtype','--notes','Actual focused compile failed; frozen target unchanged, no compiled promotion.')
native('R002-repair-event-v3','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
    json.dumps(dict(leaf='R002',contract_version=2,body_version=3,target_changed=False,
        actual_failure='R002-focused-build-v2-exit.json',repair='finite subtype annotation')))
text=PUBLIC.read_text(encoding='utf8')
old='(measurable_pi_lambda _ (fun i => measurable_pi_apply i)).prodMk (measurable_pi_apply t)'
new='(measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) =>\n        measurable_pi_apply (i : ℕ))).prodMk (measurable_pi_apply t)'
assert text.count(old)==1
PUBLIC.write_bytes(text.replace(old,new,1).encode('utf8'))
write(RUN/'leaves'/'R002-body-v3.lean',PUBLIC.read_bytes())
headers_fixed(2)
native('R002-proving-resume-v3','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
    json.dumps(dict(leaf='R002',body_version=3,contract_version=2,exact_target_unchanged=True)))
gate('R002-focused-build-v3','lake','build','BanditRLProof.OnlineGuessingRandomizedIID')
row=load(CONTRACT/'targets-v2.json')['rows'][1]
native('R002-fence-v3','statement-fence','--declaration',row['name'],'--file',PUBLIC,'--output',RUN/'R002-fence-v3.json')
native('R002-safe-verify-v3','safe-verify','--fence',RUN/'R002-fence-v3.json','--lean-file',PUBLIC)
native('R002-worker-compiled-v3','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R002-V3','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--new-declaration',row['name'],
    '--verifier-evidence',RUN/'R002-focused-build-v3-exit.json','--progress-class','compiled-leaf',
    '--obligations-before','6','--obligations-after','5','--notes','Actual strict-past tuple/current independence and whole-process seed extraction compiled; v2 failed body preserved; exact v2 terminal unchanged.')
write(RUN/'R002-progress-v3.json',dict(closed=['R001','R002'],remaining=['R003','R004','R005','R006','R007'],
    contract_version=2,failed_body_v2_preserved=True,package_accepted=False,chapter_complete=False,goal_complete=False))
source=(RUN/'prove-causal-chain-v2.py').read_text(encoding='utf8').replace('from common_reviewed_v2 import *\n','',1)
start=source.index("write(RUN/'causal-body-candidates-v2.json'")
end=source.index('for i,row in enumerate(targets[1:],2):',start)
source=source[:start]+source[end:]
source=source.replace('for i,row in enumerate(targets[1:],2):','for i,row in enumerate(targets[2:],3):',1)
exec(compile(source,str(RUN/'prove-causal-chain-v2.py'),'exec'),globals())
