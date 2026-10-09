from publication_guard_v1 import *
fixed()
parent=ROOT/'runs/online-ch2-prescient-cumulative-20261009'
replacements=[
 ('publication_guard_v4','publication_guard_v1'),
 ('online-ch2-prescient-cumulative-delivery','online-ch2-prescient-source-delivery'),
 ('candidate-stage-plan-v4.json','candidate-stage-plan-v1.json'),
 ('codex/research-online-ch2-prescient-causal','codex/research-online-ch2-prescient-cumulative'),
 ('parent-PR211','parent-PR212'),
 ("'view','211'","'view','212'"),
 ('clean-candidate-site-binding-v2.json','clean-candidate-site-binding-v1.json'),
 ('prescient cumulative proof','prescient source proof'),
 ('prescient cumulative draft','prescient source draft'),
 ('prescient causal PR','prescient source PR'),
 ('parentPR211 exact24de0231aa067f141251aac5c20deb58e448ea66','parentPR212 exact547137ea02c59c24424e2fb448174875845fadb4'),
 ('Fiveconditionalproofs5->0/twofullcanaries','Sixsourcevalidrunproofs6->0/twofullcanaries'),
 ('Full sourceX/interiorgenerator/loss premise transport andvalidrunwrapper/all8forwards REQUIREDOPEN','Universal attainment/automatic interior preservation not claimed;all8forwardcontainers REQUIREDOPEN pending dedicated reconciliation'),
 ('general source/Chapter2/wholeGoal remain open','conditional source package only;Chapter2/wholeGoal remain open'),
 ('ActualfileURI12pixels','ActualfileURI14pixels'),
 ('CleanSITEv2','CleanSITEv1'),
 ('Clean repairedSITEv2','CleanSITEv1'),
]
for name in ['deliver-v1.py','collect-actual-delivery-v1.py','final-evidence-delivery-v1.py']:
    text=(parent/name).read_text(encoding='utf8')
    for old,new in replacements:text=text.replace(old,new)
    # The inherited collector's prose is historical boilerplate, not a scope assertion.
    text=text.replace('Priorreaderambiguity/exact13fieldrepair/failurehistoryimmutable.',
                      'Historical source/canary/API/native-metadata repair evidence immutable.')
    text=text.replace('Priorreaderambiguity/exact13fieldrepair/failurehistoryimmutable.',
                      'Historical source/canary/API/native-metadata repair evidence immutable.')
    compile(text,name,'exec')
    write(RUN/name,text)
audit=load(RUN/'post-native-root-audit-v1.json')
assert audit['all_other_FINAL_inputs_unchanged'] and audit['state_exact_expected']
assert audit['trial']['obligations_before']==6 and audit['trial']['obligations_after']==0
write(RUN/'post-native-packet-v1.md', '''# Actual bounded source-transport native acceptance and prospective draft PR

Distinct staged review, requested GPT-6 Astra / medium. Inspect actual execute-native-v2.py/native-v2-command and record-native-acceptance-v2.py plus accepted FINAL and native-metadata-repair-review-v2. Recompute exact before bytes from pre-native-exact-bytes-v1.json, one new accepted trial, one appended session event, correct sequence/parent/state, unchanged own journal and global baseline. Native 6->0 applies ONLY the six frozen production proofs; full 8/6-conjunct Test canaries are separate. Six Lean terminals are not six printed results or a chapter denominator. All eight forward containers required/open; Chapter2 partial/null, later chapters unenumerated/null, whole16Goal ACTIVE.

Only four approved contribution fields and two own document suffixes changed, plus own trial/session/state. Verify every other FINAL input remains exact RAW; current inputs before/after. No math/Test/root/readers/contracts/pins/source or existing global registry changes. Preserve accepted historical FINAL and the v2 addendum, source and canary failures. All14 original pixels already root+distinct personally reviewed; local file desktop only. Clean SITE source commit is 7be6929fb3a5ea8306fce0ebf41f3aec03fa3179, not later metadata head. Registry 11020 old complete objects preserved plus6 canonical proofs, no Test/perBook duplicates.

Review prospective deliver-v1.py, collect-actual-delivery-v1.py, final-evidence-delivery-v1.py and exact PR-plan/body. Scoped stage through candidate-stage-plan-v1 only, preserve RAW/CRLF snapshots, full BASE whitespace check, two nonvacuous contributor checks, nonforce push, draft PR stacked on OPEN unmerged PR212 exact547137ea02c59c24424e2fb448174875845fadb4. No merge/deploy/retirement/main/live claim. Caller checks favorable postnative receipt and immutable input manifest before execution; official app attachment and actual-delivery distinct review follow. The final commit contains only new own RUN evidence/review and RAW snapshots to avoid self-reference loops; terminal observations retained ignored. No global credential edits.

Create only post-native-review-v1.md/json: verdict/native_verdict/metadata_verdict/prospective_publication_prose_verdict/delivery_helper_verdict/required_repairs/report/report_sha256/input_manifest_sha256/FINAL_sha256/raw_input_checks. No publication or edits to reviewed inputs. Related staged actor history disclosed; no human/external/absolute-blind/runtime attestation.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(row['path']) for row in load(RUN/'FINAL-inputs-v1.json')['rows'])
paths.add(RUN/'trials.jsonl')
write(RUN/'post-native-inputs-v1.json',dict(rows=rows(paths),FINAL_sha256=sha(RUN/'FINAL-review-v1.json'),native_addendum_sha256=sha(RUN/'native-metadata-repair-review-v2.json'),scope='Actual own six-proof native acceptance; prospective scoped delivery',actual_delivery_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual postnative packet and prospective scoped delivery helpers prepared; distinct review pending.')
