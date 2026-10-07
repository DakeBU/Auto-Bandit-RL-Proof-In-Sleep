from common_v1 import *
fixed(proving=True)
assert load(RUN/'initial-worker-compiled-trial-v2-exit.json')['exit_code']==1
actual=load(RUN/'native-initial-full-fence-v2.json')
write(RUN/'initial-trial-repair-v3.json',dict(failed_gate_sha256=sha(RUN/'initial-worker-compiled-trial-v2-exit.json'),cause='Actual CLI role enum lower, not lean-worker',repair='Use actual existing lower/build/compiled schema',source_body_and_statement_unchanged=True))
native('initial-worker-compiled-trial-v3','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-SHARP-INITIAL-V3','--statement-hash',actual['statement_hash'],'--new-declaration',PRE+'meanPredict_initial_stability','--changed-file',PUBLIC,'--verifier-evidence',RUN/'initial-type-axiom-canary-v1-exit.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual focused build and exactN06rfl/#check/axioms/endpoint/midpoint/outside witnesses passed. Failed fence and role invocations retained; capture/hash/safe-verify passed. Refined/BODY/combined/site/FINAL/PR/chapter/Goal pending.')
write(RUN/'initial-leaf-compiled-v2.json',dict(status='compiled-local source-bound prerequisite',public_name=PRE+'meanPredict_initial_stability',source_anchor='Theorem1.3 proof printed5/PDF17',full_native_header_sha256=actual['statement_hash'],actual_guards_types_axioms_endpoint_canaries_passed=True,initial_source_bound_closed_locally=True,refined_source_terminal_pending=True,BODY_review_pending=True,chapter_complete=False,goal_complete=False))
fixed(proving=True)
