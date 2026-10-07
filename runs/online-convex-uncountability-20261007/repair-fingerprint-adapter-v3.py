"""Correct the caught auxiliary hash-domain mismatch, preserve all original failures."""
from common_v2 import *
fixed(False,True)
assert load(RUN/'repair-canary-v2-01-exit.json')['exit_code']==1
assert load(RUN/'public-canary-focused-v2-01-exit.json')['exit_code']==1
p=RUN/'repair-canary-v2.py';text=p.read_text(encoding='utf-8').replace('from common_v1 import *','from common_v2 import *')
write(RUN/'repair-canary-v3.py',text)
p=RUN/'prepare-review-v3.py';text=p.read_text(encoding='utf-8').replace('from common_v1 import *','from common_v2 import *')
text=text.replace("mode.lower()+'-v3-reviewed-'","mode.lower()+'-v4-reviewed-'")
for stem in ['inputs','native-snapshot-bindings','packet','review','receipt']:
 text=text.replace("stem+'-"+stem+'-v3',"stem+'-"+stem+'-v4').replace('{stem}-'+stem+'-v3','{stem}-'+stem+'-v4')
write(RUN/'prepare-review-v4.py',text)
write(RUN/'fingerprint-adapter-repair-v3.json',dict(failed_attempt='repair-canary-v2-01',error='Auxiliary fixed(body=True) compared the native whitespace-normalized extracted header hash with the raw multiline freeze hash.',repair='Versioned common_v2 independently checks actual raw multiline headers against raw frozen fingerprints AND actual native-normalized headers against the separate native freeze; no source/theorem-header edits.',actual_current_raw_and_native_checks_passed=True,failed_helper_preserved=True,unintended_repeat_focused_attempt='public-canary-focused-v2-01',repeat_reason='Parent orchestration launched a dependent rebuild before inspecting failed repair helper result. No code mutation occurred, same canary failure repeated; this is not a new proof route.',repeat_and_initial_focused_failures_preserved=True,mathematical_targets_unchanged=True,effective_canary_repair='repair-canary-v3.py',effective_BODY_FINAL_review_generator='prepare-review-v4.py',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('failed-focused-repeat-v2','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--run-id',RUN.name,'--attempt-id','UNCOUNTABLE-BODY-V2-UNCHANGED-REPEAT','--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_uncountable_nondifferentiability'],'--verifier-evidence',RUN/'public-canary-focused-v2-01.log','--harness','hierarchical','--progress-class','no-progress','--error-signature','Unchanged canary repeated after auxiliary hash-domain precheck rejected repair','--notes','Actual failed fingerprint adapter prevented all code mutations; parent mistakenly launched dependent rebuild without checking failure. Raw and native headers remain exact; preserve both failures, corrected versioned guard before real canary annotation repair.')
event('repair',dict(reason='raw-vs-native hash domain and dependent-command sequencing audit',repair=(RUN/'fingerprint-adapter-repair-v3.json').as_posix(),targets_unchanged=True),attempt='guard-v3')
print('Actual raw/native header checks pass separately; original auxiliary failure/repeated focused failure preserved.')
