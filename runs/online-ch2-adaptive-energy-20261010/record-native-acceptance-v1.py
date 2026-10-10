from native_acceptance_guard_v1 import *

final_fixed()
p=load(NATIVE_PLAN)
candidate,accepted=payloads()
event('native-candidate-event-v1','candidate',candidate)
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,
    '--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,
    '--attempt-id','three-frozen-energy-propositions-v1','--progress-class','closed-frontier',
    '--reviewer-validated','--obligations-before','3','--obligations-after','0']
for name in p['declarations']:args.extend(['--new-declaration',name])
args.extend(['--notes',render(p['trial_notes_template']),'--verifier-evidence',FINAL.as_posix()])
capture('native-acceptance-trial-v1',*args)
event('native-acceptance-event-v1','accepted',accepted)
for path,raw in expected_metadata().items():path.write_bytes(raw)
write(RUN/'memory-digest-accepted-v1.md','# Accepted bounded energy prerequisite\n\nTask: `'+TASK+'`\n\n'+p['boundary']+'\n\nThree exact frozen production proposition obligations3->0, ONEsourcefamily/0definitions/2FULLcanaries. FINAL '+sha(FINAL)+'. Actual root9117/Tests9294/fullharness472tests7skips. Clean site '+load(RUN/'registry-inspected-v1.json')['source_commit']+';11055oldobjects+3canonicalproofnodes=11058,16cards/19MathJax/6originals. Postnative/draftPRpending.\n')
output=ROOT/'tmp'/(TASK+'-accepted-frontier-v1.json');assert not output.exists()
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
    'frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; bounded energy prerequisite only',
    '--leaf',TASK,'--kind','review','--statement',p['boundary'],'--file',FINAL,
    '--source-status','source-reviewed','--leaf-status','accepted',
    '--dependency','review:energy-prerequisite-FINAL:accepted','--trials',RUN/'trials.jsonl',
    '--output',output,'--shadow-status','pending')
write(RUN/'accepted-frontier-native-RAW-v1.json',dict(path=output.as_posix(),sha256=sha(output),
    RAW_base64=base64.b64encode(output.read_bytes()).decode('ascii'),
    scope='Actual native original ignoredtmp and exactbase64; separate OWN copy is explicitly parsed LF.'))
write(RUN/'accepted-frontier-v1.json',load(output))
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
    'frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md',
    '--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert not shadow['mismatches'] and not shadow['would_mutate'] and shadow['trial_rows']==4
final_fixed(after=True)
trial,events=transition_check()
write(RUN/'post-native-root-audit-v1.json',dict(FINAL_sha256=sha(FINAL),trial=trial,events=events,
    exactly8mutable_paths=True,all_other_FINAL_RAW_unchanged=True,shadow=shadow,
    source_families=1,frozen_production_propositions_closed=3,definitions=0,
    root_self_audit_only=True,distinct_post_native_review='pending',chapter_complete=False,whole_Goal='active'))
for label,base in [('post-native-contributor-stack-v1',BASE),('post-native-contributor-main-v1','origin/main')]:
    _,out=capture(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    assert 'Contributor contract: N/A' not in out and 'BanditRLProof/OnlineAdaptiveEnergy.lean' in out
capture('post-native-fullBASE-whitespace-v1','git','diff','--check',BASE)
final_fixed(after=True)
print('Actual scoped native3frozenpropositions->0/ONEsourcefamily acceptance; postnative/delivery pending.',flush=True)
