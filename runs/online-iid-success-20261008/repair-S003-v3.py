from leaf_tools_v2 import *
headers_fixed(3)
native('S003-failed-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','SUCCESS-S003-V2','--harness','hierarchical',
    '--verifier-evidence',RUN/'S003-focused-build-v2-exit.json','--progress-class','diagnostic',
    '--error-signature','Nonexistent sq_zero simplification lemma; actual residual T*0^2',
    '--notes','First Pi rewrite now resolved. New failure is a guessed simplification name, not an extra assumption or false target. Use standard zero-power simp normalization at population comparator; retain all failures.')
write(RUN/'S003-repair-diagnosis-v3.json',dict(
    v1_failure='Pi function subtraction rewrite representation mismatch; resolved in v2',
    v2_failure='Unknown sq_zero; actual comparator decomposition residual T*0^2',
    source_or_hypothesis_gap=False,proof_only=True,target_changed=False,
    mathematical_route_unchanged='pathwise empirical minimum comparison, a.s.support L2, integration'))
prior=PUBLIC.read_text(encoding='utf8')
assert prior.count('simpa only [m, sub_self, sq_zero, mul_zero, add_zero] using')==1
PUBLIC.write_bytes(prior.replace('simpa only [m, sub_self, sq_zero, mul_zero, add_zero] using',
    'simpa [m] using').encode('utf8'))
write(RUN/'leaves'/'S003-body-v3.lean',PUBLIC.read_bytes())
headers_fixed(3)
gate('S003-focused-build-v3','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
finish_leaf(2,'v3','Actual no-independence4log upper producer with derived a.s.support integrability, empirical minimum-to-population comparator pathwise comparison, and literal expected-fixed benchmark. Two proof-only API/representation repairs retained; terminal unchanged.')
