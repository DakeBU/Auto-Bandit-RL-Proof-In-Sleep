from leaf_tools_v2 import *
headers_fixed(3)
native('S003-failed-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','SUCCESS-S003-V1','--harness','hierarchical',
    '--verifier-evidence',RUN/'S003-focused-build-v1-exit.json','--progress-class','diagnostic',
    '--error-signature','Pi function subtraction not pointwise-normalized for integral_sub rewrite',
    '--notes','Actual failed proof rewrite; no hypothesis/terminal change, no integrability gap. Normalize Pi.sub_apply only; raw prior full body/log retained.')
native('proof-repair-event-S003-v2','lifecycle-event','--session',TASK,'--event','repair',
    '--payload-json',json.dumps(dict(leaf='S003',failure='representation mismatch at integral_sub',
        proof_only=True,target_changed=False,raw_failure_sha256=sha(RUN/'S003-focused-build-v1.log'))))
prior=PUBLIC.read_text(encoding='utf8')
assert prior.count('  rw [integral_sub hPI hCI] at hi')==1
PUBLIC.write_bytes(prior.replace('  rw [integral_sub hPI hCI] at hi',
    '  simp only [Pi.sub_apply] at hi\n  rw [integral_sub hPI hCI] at hi').encode('utf8'))
write(RUN/'leaves'/'S003-body-v2.lean',PUBLIC.read_bytes())
headers_fixed(3)
gate('S003-focused-build-v2','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(2,'v2','Actual no-independence upper producer integrates Theorem1.3 against population mean after empirical minimum comparison; all integrability derived from a.s.support. Proof-only Pi subtraction normalization repair.')
