from common_reviewed_v2 import *

headers_fixed(4)
assert load(RUN/'R004-focused-build-v2-exit.json')['exit_code']==1
write(RUN/'R004-failure-repair-v3.json',dict(contract_version=2,failed_body_version=2,repair_body_version=3,
    actual_failure='R004-focused-build-v2-exit.json',classification='local Lean lemma gap',
    detail='Explicit F:MeasurableSpace Ω binder shadows the ambient instance during body elaboration; R002 application synthesized F rather than original μ domain structure.',
    repair='Name original inaccessible instances and restore ambient local instance in proof. Restricted measurability premise stays exactly Measurable[F] P.',
    failed_body_retained='leaves/R004-body-v2.lean',terminal_changed=False))
native('R004-worker-failed-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R004-V2','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--verifier-evidence',RUN/'R004-focused-build-v2-exit.json',
    '--error-signature','explicit subfield F shadows ambient measurable instance','--notes','Actual v2 body failed; exact frozen measurable-information terminal unchanged.')
native('R004-repair-event-v3','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
    json.dumps(dict(leaf='R004',contract_version=2,body_version=3,target_changed=False,
        repair='restore original ambient instance, restricted premise unchanged')))
targets=load(CONTRACT/'targets-v2.json')['rows'];row=targets[3]
text=PUBLIC.read_text(encoding='utf8');old=row['header']+' := by\n'
assert text.count(old)==1
PUBLIC.write_bytes(text.replace(old,old+'  rename_i mΩ mSeed hμ\n  letI : MeasurableSpace Ω := mΩ\n',1).encode('utf8'))
write(RUN/'leaves'/'R004-body-v3.lean',PUBLIC.read_bytes())
headers_fixed(4)
native('R004-proving-resume-v3','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
    json.dumps(dict(leaf='R004',body_version=3,contract_version=2,target_unchanged=True)))
gate('R004-focused-build-v3','lake','build','BanditRLProof.OnlineGuessingRandomizedIID')
native('R004-fence-v3','statement-fence','--declaration',row['name'],'--file',PUBLIC,'--output',RUN/'R004-fence-v3.json')
native('R004-safe-verify-v3','safe-verify','--fence',RUN/'R004-fence-v3.json','--lean-file',PUBLIC)
native('R004-worker-compiled-v3','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','PRIVATE-R004-V3','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v2.json'),'--new-declaration',row['name'],
    '--verifier-evidence',RUN/'R004-focused-build-v3-exit.json','--progress-class','compiled-leaf',
    '--obligations-before','4','--obligations-after','3','--notes','Actual subordinate-information independence compiled; original ambient instance restored, no hypothesis/result edit; v2 failure retained.')
write(RUN/'R004-progress-v3.json',dict(closed=['R001','R002','R003','R004'],remaining=['R005','R006','R007'],
    contract_version=2,failed_body_v2_preserved=True,package_accepted=False,chapter_complete=False,goal_complete=False))
source=(RUN/'prove-causal-chain-v2.py').read_text(encoding='utf8').replace('from common_reviewed_v2 import *\n','',1)
start=source.index("write(RUN/'causal-body-candidates-v2.json'")
end=source.index('for i,row in enumerate(targets[1:],2):',start)
source=source[:start]+source[end:]
source=source.replace('for i,row in enumerate(targets[1:],2):','for i,row in enumerate(targets[4:],5):',1)
exec(compile(source,str(RUN/'prove-causal-chain-v2.py'),'exec'),globals())
