from publication_guard_v1 import *
publication_fixed()
plan=load(NATIVE_PLAN);before=originals()
for p,b in before.items():assert p.read_bytes()==b,p
write(RUN/'pre-native-current-recheck-v1.json',dict(originals_sha256=plan['originals_sha256'],FINAL_sha256=sha(FINAL),all_mutable_current_RAW_equal_frozen_originals=True,scope='No mutation has occurred.'))
candidate,accepted=payloads()
event('native-candidate-event-v1','candidate',candidate)
notes=plan['trial_notes_template'].replace('{FINAL_SHA}',sha(FINAL))
capture('native-acceptance-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','one-frozen-integral-comparison-proof-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','1','--obligations-after','0','--new-declaration',plan['terminal']['declaration'],'--notes',notes,'--verifier-evidence',FINAL)
event('native-acceptance-event-v1','accepted',accepted)
replacements,suffix=templates()
c=copy.deepcopy(json.loads(before[CONTRIBUTION].decode('utf8')))
for (a,b),v in replacements.items():c[a][b]=v
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
for rel in plan['document_paths']:
    p=ROOT/rel;p.write_bytes(before[p]+suffix.encode('utf8'))
write(RUN/'memory-digest-accepted-v1.md','# Accepted bounded prerequisite\n\nTask: `'+TASK+'`\n\n'+plan['boundary']+'\n\nOne frozen production proof1->0 only; two FULL canaries separately reviewed;0definitions; no complete source container/chapter denominator. FINAL '+sha(FINAL)+'. Actual root9116/Tests9292/fullharness472tests7skips; first failed harness and whitespace/browser repairs retained. Clean local site '+load(RUN/'registry-inspected-v1.json')['source_commit']+'; all11054oldnodes+one shared theorem=11055. Four full original desktop pixels personally reviewed by root+distinctFINAL. Postnative/delivery pending.\n')
output=ROOT/'tmp'/(TASK+'-accepted-frontier-v1.json');assert not output.exists()
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; only one bounded integral comparison prerequisite accepted','--leaf',TASK,'--kind','review','--statement',plan['boundary'],'--file',FINAL,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:integral-comparison-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',output,'--shadow-status','pending')
write(RUN/'accepted-frontier-native-RAW-v1.json',dict(path=output.as_posix(),sha256=sha(output),raw_base64=base64.b64encode(output.read_bytes()).decode('ascii'),scope='Actual native CRLF output retained in ignored tmp and exact base64; OWN copy explicitly parsed LF, not unchanged RAW.'))
write(RUN/'accepted-frontier-v1.json',load(output))
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate'] and shadow['trial_rows']==5
publication_fixed(after_native=True)
_,trial,events=native_transition_check()
write(RUN/'post-native-root-audit-v1.json',dict(FINAL_sha256=sha(FINAL),trial=trial,events=events,state_exact_expected=True,originals_sha256=plan['originals_sha256'],contribution_fields=list(plan['manifest_replacements_template']),document_suffix=suffix,all_other_FINAL_inputs_RAW_unchanged=True,own_journal_and_global_SGB_unchanged=True,shadow=shadow,root_self_audit_only=True,distinct_post_native_review='pending',chapter_complete=False,whole_Goal='active'))
for label,base in [('post-native-contributor-stack-v1',BASE),('post-native-contributor-main-v1','origin/main')]:
    _,out=capture(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    assert 'Contributor contract: N/A' not in out and MODULE.relative_to(ROOT).as_posix() in out
capture('post-native-stage-v1','git','add',*load(PLAN)['stage'])
changed,bindings=exact_cached_scope()
capture('post-native-full-BASE-whitespace-v1','git','diff','--cached',BASE,'--check')
write(RUN/'post-native-scope-inspected-v1.json',dict(changed_paths=changed,all_staged_blobs=bindings,actual_full_BASE_whitespace_exit=0,both_nonempty_contributor_bases=True,distinct_post_native_review_pending=True,chapter_complete=False,whole_Goal='active'))
publication_fixed(after_native=True)
print('Actual scoped native candidate/accepted and1->0 proof closure audited; distinct postnative/delivery pending.',flush=True)
