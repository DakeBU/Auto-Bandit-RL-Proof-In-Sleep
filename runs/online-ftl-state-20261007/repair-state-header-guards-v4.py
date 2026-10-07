from common_v1 import *
fixed(proving=True);assert load(RUN/'safe-ftlPredict_prefix-v1-exit.json')['exit_code']==1
headers=load(CONTRACT/'new-public-headers-v1.json');n='ftlPredict_prefix'
old=load(RUN/'native-public-fences'/(n+'-v1.json'))
write(RUN/'state-header-guard-repair-v4.json',dict(failed_exit_sha256=sha(RUN/'safe-ftlPredict_prefix-v1-exit.json'),failed_log_sha256=sha(RUN/'safe-ftlPredict_prefix-v1.log'),cause='Literal binder guard (y : Realstream) does not occur in the grouped binder (y z : Realstream)',repair='Guard the complete exact frozen supported theorem header rather than guessing binder fragments; source fidelity remains a distinct reviewed gate',all_production_statements_and_bodies_unchanged=True,focused_prefix_proof_already_compiled=True,original_failed_fence_retained=True))
native('fence-'+n+'-v2','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--source-assumption',headers[n],'--output',RUN/'native-public-fences'/(n+'-v2.json'))
f=load(RUN/'native-public-fences'/(n+'-v2.json'));assert f['statement_hash']==old['statement_hash']
native('safe-'+n+'-v2','safe-verify','--fence',RUN/'native-public-fences'/(n+'-v2.json'),'--lean-file',PUBLIC)
native('trial-'+n+'-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-'+n+'-V1','--statement-hash',f['statement_hash'],'--changed-file',PUBLIC,'--new-declaration',PRE+n,'--lean',PUBLIC,'--verifier-evidence',RUN/('focused-'+n+'-v1-exit.json'),'--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual generalpredictor prefix theorem compiled at frozen header. Grouped-binder literal guard failure retained, complete exactheader guard passed without theorem/proof changes; source semantic review separate.')
text=(RUN/'continue-state-v3.py').read_text(encoding='utf-8')
bad="'--source-assumption','(y : ℕ → ℝ)'";assert text.count(bad)==1
text=text.replace(bad,"'--source-assumption',headers[n]")
needle='for n,body in bodies.items():\n';assert text.count(needle)==1
replacement=needle+" if n=='ftlPredict_prefix':\n  f=load(RUN/'native-public-fences/ftlPredict_prefix-v2.json');rows.append(dict(name=PRE+n,statement_hash=f['statement_hash'],focused_exit=0,safe_exit=0));continue\n"
write(RUN/'continue-state-v4.py',text.replace(needle,replacement))
fixed(proving=True)
