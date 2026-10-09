from common_v1 import *
import re
fixed()
assert sha(RUN/'source-contract-receipt-correction-v4.json')=='ea1d3ccb42831139b84cce6877a02bdc66cd92917eea18c20ac91b48ef7af9b2'
c=load(RUN/'source-contract-receipt-correction-v4.json')
assert c['verdict']=='accepted'
for row in c['raw_input_checks']:
    assert row['before_sha256']==row['after_sha256']
    assert sha(row['path'])==row['after_sha256']
log=(RUN/'general-init-four-public-values-v1.log').read_text('utf8')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(found)==4
axioms=[]
for name,raw in found:
    used=sorted({x.strip() for x in raw.split(',') if x.strip()})
    assert set(used)<={'propext','Classical.choice','Quot.sound'},(name,used)
    axioms.append(dict(name=name,actual_axioms=used))
write(RUN/'general-init-axiom-audit-v2.json',dict(actual_log_sha256=sha(RUN/'general-init-four-public-values-v1.log'),parser='all four complete bracket groups including multiline; earlier v1 line-only parser was incomplete, actual outputs rechecked',rows=axioms,standard_only=True,no_extra_axioms=True))
mutable=[RUN/'trials.jsonl',RUN/'own-artifact-journal.md',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']
snaps=[]
for n,p in enumerate(mutable):
    s=RUN/'snapshots'/('before-proof-candidate-v1-%02d.raw'%n);write(s,p.read_bytes())
    snaps.append(dict(path=p.as_posix(),before=s.as_posix(),before_sha256=sha(s)))
def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
labels=['G001-focused-v1','G001-focused-v2','G001-focused-v3','G002-focused-v1','G003-focused-v1','G004-focused-v1','G004-focused-v2']
for label in labels:
    evidence=RUN/'leaves'/(label+'-attempt.json');e=load(evidence)
    native('trial-'+label+'-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled' if e['actual_exit']==0 else 'failed','--run-id',RUN.name,'--attempt-id',label.upper(),'--progress-class','leaf-closure' if e['actual_exit']==0 else 'diagnostic','--notes','Actual focused command/body snapshot recorded, exact frozen headers unchanged. Syntax/tactic failures retained; compiled only, distinct BODY/public canary/chapter gates pending.','--verifier-evidence',str(evidence),'--verifier-evidence',str(RUN/(label+'-exit.json')))
native('candidate-native-general-init-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(scope='four actual bodies candidate only',readiness=sha(RUN/'general-init-public-readiness-v1.json'),axiom_audit=sha(RUN/'general-init-axiom-audit-v2.json'),proof_module=sha(ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'),pending='distinct BODY, chapter canary roundtrip/bodies and full gates',chapter_complete=False,goal_complete=False)))
for row in snaps:row['after_sha256']=sha(row['path'])
write(RUN/'proof-candidate-own-mutation-receipt-v1.json',dict(before_bindings=snaps,approved_scope_sha256=sha(CONTRACT/'future-mutation-scope-draft-v3.json'),actual_native_commands=8,all_actual_exit_zero=True,global_old_baseline_unchanged=True,chapter_complete=False,goal_complete=False))
source=load(RUN/'source-contract-review-inputs-v3.json')
paths=[Path(row['path']) for row in source['rows']]
paths += list(CONTRACT.glob('public-G*-fence-v1.json'))
paths += [ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean',CONTRACT/'general-initialization-targets-stabilized-v3.json',CONTRACT/'stabilization-decision-v3.json']
paths += [RUN/p for p in ['source-contract-review-v3.md','source-contract-receipt-v3.json','source-contract-review-correction-v4.md','source-contract-receipt-correction-v4.json','stabilized-own-mutation-receipt-v3.json','proof-candidate-own-mutation-receipt-v1.json','general-init-public-readiness-v1.json','general-init-axiom-audit-v2.json','compiled-general-init-readiness-graph-v1.json','general-init-four-public-values-v1.lean','general-init-four-public-values-v1.log','general-init-four-public-values-v1-exit.json','export-general-init-readiness-v1.lean','export-general-init-readiness-v1.log','export-general-init-readiness-v1-exit.json']]
paths += list((RUN/'leaves').glob('*')) + list((RUN/'snapshots').glob('*stabilized-v3*')) + list((RUN/'snapshots').glob('*proof-candidate-v1*'))
paths += [RUN/(label+suffix) for label in labels for suffix in ['.log','-exit.json']]
paths += [RUN/(prefix+t+suffix) for t in ['G001','G002','G003','G004'] for prefix in ['fence-','safe-'] for suffix in ['-v1.log','-v1-exit.json']]
packet=RUN/'general-init-BODY-packet-v1.md'
write(packet,'''# Four actual initialized-FTL bodies: distinct BODY review

CONTRACT/INVENTORY v3 stabilized exact source17/4target repair only; correction-v4 explicitly withdraws the reviewer's false negative initialized-FTL example/nonnegativity exclusion. Preserve v3 originals and apply this correction in any verdict. Original16/current50 source judgments and fixed inputs remain historical, unchanged mathematical types/bodies. Read actual four public theorem bodies, whole-type proof witnesses/axioms, compiler VALUE graph and native fences. G001 is actual first-round loss cancellation with same infimum; G002 uses real unit initialization bound quarter+correction<=1 and same half-tail; G003 obtains an actual derived5+4log analytic upper and vanishing limit with comparator-to-produced-minimum transport; G004 combines actual half TRUE-best average0 and fixed correction/T. Same ftlPredict/recursive state/strictpast semantics, no supplied performance or future/horizon-selected algorithm oracle. All4 frozen statement hashes remain unchanged. Four endpoints are one newly required source object, not four printed results; its mathematical package may become BODY-ready, whole chapter still pending.

The original196 source-review index is immutable; approved OWN native/task appends after review are represented by exact before snapshots and separate mutation receipts. Current BODY index hashes the current OWN rows explicitly. Verify both immutable snapshots match original bindings and current rows match approved append receipts, never falsely claim old mutable rows stayed unchanged. Old production/pins/root/Test/reader/global baseline is unchanged; sole new canonical module has precisely4publictheorems,2permitted imports and0privatehelpers/newdefinitions. Focused attempts G001v1/v2 failed thenv3 compiled; G002v1/G003v1 compiled; G004v1 failed redundantfinal tactic thenv2 compiled. Complete logs/snapshots retained, no statement weakened. Four value witnesses and4standard axioms actual0; multiline brackets independently parsed in axiom-v2. 77selected compiler nodes/7111coalesced direct TYPE_VALUE edges,9actual requiredVALUE pairs: not full transitive graph/source counts. Safe-verify is separate from compilation.

Reviewer must independently inspect source semantics/seven slots and actual proof bodies/values, propose accepted|accepted-with-explicit-delta|rejected BODY-only verdict and remaining required repairs. Freeze module/body hash while reviewed. No chapter canary body/import/reader edits yet; separately roundtripped meaningful wholechapter canaries, actual shared root/Tests/full harness, nonemptytwo-basecontributor, ownshadow, same registry, site/DOM/personalpixels, FINAL/native/post-native/delivery remain mandatory R1-R10. No chapter/Goalacceptance, native acceptance, merge/deploy. Reused distinct automated actor/Astramedium requested/no runtime/human/external/absolute-blind attestation.

Write ONLY general-init-BODY-review-v1.md and general-init-BODY-receipt-v1.json. Bind actual input index/packet/module/frozen4/source/correction/readiness/completeRAWbeforeafter; actual source views reused with precise hashes or fresh personally seen originals stated truthfully. No input/native/proof/site/Git action. Exact existing approved scope unchanged; any required new proof/body/target change must enter bounded repair rather than silently weaken terminal.
''')
paths.append(packet)
index=rows(paths)
write(RUN/'general-init-BODY-inputs-v1.json',dict(rows=index,fixed_input_count=len(index),new_public_bodies=4,source_audit_objects=17,proof_total=None,chapter_complete=False,goal_complete=False))
fixed()
print('Four current public bodies BODY packet:',len(index),'RAW inputs;7actual attempts/8OWN native commands retained.',flush=True)
