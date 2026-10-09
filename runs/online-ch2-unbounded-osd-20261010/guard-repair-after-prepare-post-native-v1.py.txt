from publication_guard_v2 import *
fixed()
parent=ROOT/'runs/online-ch2-prescient-source-20261010'
replacements=[
 ('online-ch2-prescient-source-delivery','online-ch2-unbounded-osd-delivery'),
 ('codex/research-online-ch2-prescient-cumulative','codex/research-online-ch2-prescient-source'),
 ('parent-PR212','parent-PR213'),("'view','212'","'view','213'"),
 ('parentPR212 exact547137ea02c59c24424e2fb448174875845fadb4','parentPR213 exact'+BASE),
 ('547137ea02c59c24424e2fb448174875845fadb4',BASE),
 ('prescient source proof','unbounded OSD proof'),('prescient source draft','unbounded OSD draft'),('prescient source PR','unbounded OSD PR'),
 ('Sixsourcevalidrunproofs6->0/twofullcanaries','Elevenfrozenproofterminals11->0/fourdefinitions/twofull7/9canaries'),
 ('Universal attainment/automatic interior preservation not claimed;all8forwardcontainers REQUIREDOPEN pending dedicated reconciliation','Notminimaxagainst-all-learners;all8forwardcontainers REQUIREDOPEN pending dedicated reconciliation'),
 ('conditional source package only;Chapter2/wholeGoal remain open','bounded source package only;Chapter2/wholeGoal remain open'),
 ('not fullsource/chapter/Goal','not Chapter2/Chapter5/wholeGoal'),
 ('ActualfileURI14pixels','ActualfileURI32pixels'),
 ('Historical source/canary/API/native-metadata repair evidence immutable.','Historical source/canary/API/wrapper repair evidence immutable.'),
]
for name in ['deliver-v1.py','collect-actual-delivery-v1.py','final-evidence-delivery-v1.py']:
    text=(parent/name).read_text(encoding='utf8')
    for old,new in replacements:text=text.replace(old,new)
    compile(text,name,'exec');write(RUN/name,text)
audit=load(RUN/'post-native-root-audit-v1.json')
assert audit['all_other_FINAL_inputs_unchanged'] and audit['state_exact_expected']
assert (audit['trial']['obligations_before'],audit['trial']['obligations_after'])==(11,0)
site=load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
write(RUN/'post-native-packet-v1.md','''# Bounded Theorem5.4 dependency native acceptance and prospective draft PR

Inspect accepted FINAL/exact prospective native helper and actual native command/preflight/trial/event/state/rootaudit. Recompute pre-native exactRAW: one appended accepted trial11->0 ONLY11frozenproofterminals, fourdefinitionsseparate; one accepted sessionevent/correctsequence,parent,state; ownjournalunchanged. Exactly4approvedcontributiontextfields and2ownobligation/indexsuffixes changed. EveryotherFINALinput remainsRAWunchanged, source/Test/root/readers/contracts/pins/globalbaseline untouched. 11proofs+4definitions are not15source results orchapterdenominator. All8Chapter2forwardcontainersrequiredOPENpendingdedicatedreconciliation,Chapter2partial/null,Ch3-16unenumerated/null,whole16GoalACTIVE.32originals root+distinctFINALreviewed;localfiledesktoponly;11026completeoldregistryobjects+15canonicalproduction=11041,13sourcecards. CleanSITEv1 appliesonlytoboundcandidatecommit, notmetadata/deliveryhead.

Review exactprospective deliver-v1.py/collect-actual-delivery-v1.py/final-evidence-delivery-v1.py and PRplan/body. Stageonlycandidate-stage-plan-v1,retainRAWCRLFsnapshots/fullBASEwhitespace,twononemptycontributorgates,nonforcepush/draftPRstackedOPENunmergedPR213 exactBASE. Callerchecks favorablepostnative/report/inputmanifest andALLRAWbeforeexecution. No merge/deploy/retirement/globalcredentialchange/main/live. Officialattachment andseparateactualdeliveryreviewrequired. FinaltailonlyNEWOWNRUNevidence/review+RAWsnapshot;terminalobservationsignoredtoselfreferenceavoidance. No source/math/reader/nativeinputmutation.

Create-onlypost-native-review-v1.md/json withverdict/native_verdict/metadata_verdict/prospective_publication_prose_verdict/delivery_helper_verdict/required_repairs/report+SHA/input_manifest+SHA/FINAL_sha256/RAWbeforeafter andhelperhashbindings. DistinctreusedstagedAstra/medium,nohuman/external/absolute-blind/runtimeattestation. No publication/inputedits.
'''.replace('PR213 exactBASE','PR213 exact'+BASE)+'\nBound clean local site source '+site+'.\n')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(row['path']) for row in load(RUN/'FINAL-inputs-v1.json')['rows'])
paths.add(RUN/'trials.jsonl')
write(RUN/'post-native-inputs-v1.json',dict(rows=rows(paths),FINAL_sha256=sha(RUN/'FINAL-review-v1.json'),scope='Actual own11proofterminal native acceptance and prospective scoped draftPR; not chapter/Goal completion',actual_delivery_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual postnative and exact prospective scoped delivery packet prepared; distinct review pending.',flush=True)
