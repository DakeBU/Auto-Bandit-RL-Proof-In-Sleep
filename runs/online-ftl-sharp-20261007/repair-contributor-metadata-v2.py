from common_v1 import *
fixed(proving=True,integrated=True);assert load(RUN/'contributor-exact-v1-exit.json')['exit_code']==1
raw=(RUN/'contributor-exact-v1.log').read_text(encoding='utf-8')
for k in ['teaching_route','results_ledger','roadmap']:assert 'progress_updates.'+k+' must start with' in raw,k
p=Path('research-wiki/contribution-contracts/online-ftl-sharp-20261007.json');write(RUN/'snapshots/contributor-before-prefix-repair-v1.raw',p.read_bytes());c=load(p)
for k in ['teaching_route','results_ledger']:c['progress_updates'][k]='updated: '+c['progress_updates'][k]
c['progress_updates']['roadmap']='no-change-with-reason: '+c['progress_updates']['roadmap']
p.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'contributor-metadata-repair-v2.json',dict(failed_exit_sha256=sha(RUN/'contributor-exact-v1-exit.json'),failed_log_sha256=sha(RUN/'contributor-exact-v1.log'),cause='Actual schema requires three progress prose fields to start with updated: or no-change-with-reason:',repair='Add required status prefixes only; semantics, four actual production paths, all source/reader/formulas/public/test bodies unchanged.',statement_contract_version=1,original_failure_retained=True,actual_recheck_pending=True))
assert sha(PUBLIC)==load(RUN/'body-bindings-v1.json')['public_sha256'] and sha(CANARY)==load(RUN/'body-bindings-v1.json')['canary_sha256']
native('contributor-failed-diagnostic-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed','--run-id',RUN.name,'--attempt-id','FTL-SHARP-CONTRIBUTOR-SCHEMA-V1','--verifier-evidence',RUN/'contributor-exact-v1-exit.json','--harness','hierarchical','--progress-class','diagnostic','--error-signature','three progress field schema prefixes absent; no mathematical failure','--notes','Retain actual failed contributor gate; prefix-only metadata repair, public source/tests/reader unchanged; actual fullharness/contributor/site checks pending.')
