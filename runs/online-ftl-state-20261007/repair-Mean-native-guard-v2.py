from common_v1 import *
fixed(proving=True)
assert load(RUN/'Mean-succ-safe-v1-exit.json')['exit_code']==1
old=load(RUN/'native-public-fences/empiricalMean_succ-v1.json')
assert old['statement']==load(CONTRACT/'stabilized-native-proof-headers-v1.json')['empiricalMean_succ']
write(RUN/'Mean-native-guard-repair-v2.json',dict(failed_safe_exit_sha256=sha(RUN/'Mean-succ-safe-v1-exit.json'),failed_safe_log_sha256=sha(RUN/'Mean-succ-safe-v1.log'),cause='safe-verify source_assumptions are literal normalized header substrings; passed source prose was not a header fragment',repair='Versioned fence guards actual y/t binders; full statement hash remains exact. Source semantics separately reviewed; no comment injection or weakened assumptions.',statement_and_proof_unchanged=True,focused_build_and_named_kernel_already_passed=True,original_failed_fence_retained=True))
native('Mean-succ-fence-v2','statement-fence','--declaration',PRE+'empiricalMean_succ','--file',MEAN,'--source-assumption','(y : ℕ → ℝ)','--source-assumption','(t : ℕ)','--output',RUN/'native-public-fences/empiricalMean_succ-v2.json')
f=load(RUN/'native-public-fences/empiricalMean_succ-v2.json');assert f['statement_hash']==old['statement_hash']
native('Mean-succ-safe-v2','safe-verify','--fence',RUN/'native-public-fences/empiricalMean_succ-v2.json','--lean-file',MEAN)
native('Mean-succ-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-MEAN-SUCC-V1','--statement-hash',f['statement_hash'],'--changed-file',MEAN,'--new-declaration',PRE+'empiricalMean_succ','--lean',MEAN,'--verifier-evidence',RUN/'Mean-succ-named-v1-exit.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual alltime finite-sum recurrence compiled; original safe invocation with prose guard rejected. Literal header guard repair preserves exact statement/body, independent semantic contract. Producer terminal pending.')
write(RUN/'mean-succ-leaf-compiled-v1.json',dict(status='compiled-leaf',name=PRE+'empiricalMean_succ',statement_hash=f['statement_hash'],public_module_sha256=sha(MEAN),focused_build_exit=0,named_kernel_exit=0,native_safe_exit=0,original_failed_guard_retained=True,terminal=PRE+'ftlState_eq_predict',terminal_status='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
text=(RUN/'prove-state-v1.py').read_text(encoding='utf-8')
bad='Frozen CONTRACT general-initial FTL causal state refinement; see source contract for exact initial/prefix/real-arithmetic boundary.'
assert text.count(bad)==1
write(RUN/'prove-state-v2.py',text.replace(bad,'(y : ℕ → ℝ)'))
fixed(proving=True)
