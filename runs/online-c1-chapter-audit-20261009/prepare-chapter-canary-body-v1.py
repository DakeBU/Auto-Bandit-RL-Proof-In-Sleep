from common_proving_v2 import *
fixed()
assert load(RUN/'chapter-canary-public-readiness-v1.json')['native_fence_and_safe_pairs']==27
mutable=[RUN/'trials.jsonl',RUN/'own-artifact-journal.md',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']
snaps=[]
for n,p in enumerate(mutable):
    s=RUN/'snapshots'/('before-canary-candidate-v1-%02d.raw'%n);write(s,p.read_bytes())
    snaps.append(dict(path=p.as_posix(),before=s.as_posix(),before_sha256=sha(s)))
def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
for label in ['chapter-canary-focused-v1','chapter-canary-focused-v2']:
    evidence=RUN/'leaves'/(label+'-attempt.json');e=load(evidence)
    native('trial-'+label+'-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled' if e['actual_exit']==0 else 'failed','--run-id',RUN.name,'--attempt-id',label.upper(),'--progress-class','compiled-leaf' if e['actual_exit']==0 else 'diagnostic','--notes','Exact27 canary headers unchanged. v1 actual Nat.cast_one type mismatch; v2 proof-body-only simplification compiled. Real public producers/wholevalues/standardaxioms/directVALUE/fences checked separately. Tests root/chapter acceptance pending.','--verifier-evidence',str(evidence),'--verifier-evidence',str(RUN/(label+'-exit.json')))
native('candidate-native-chapter-canaries-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(scope='27 actual canary proofs only',readiness=sha(RUN/'chapter-canary-public-readiness-v1.json'),Test_sha256=sha(ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'),frozen=sha(CONTRACT/'chapter-canary-targets-stabilized-v1.json'),pending='distinct CANARY BODY before exact Tests append; fullchapter/publication gates remain',chapter_complete=False,goal_complete=False)))
for row in snaps:row['after_sha256']=sha(row['path'])
write(RUN/'canary-candidate-own-mutation-receipt-v1.json',dict(before_bindings=snaps,actual_native_commands=3,all_actual_exit_zero=True,global_baseline_guard='common_proving_v2 exact approved ROOT append only',chapter_complete=False,goal_complete=False))
write(RUN/'30_lower-chapter-canaries-candidate-v1.md','''# Actual 27 chapter canary proofs

Two real focused attempts: v1 failed one Nat.cast_one conversion at C021; v2 compiled all27, exact27 frozen headers unchanged. Actual complete public values,27 standard-only axiom groups,27native fences/safe checks and compiler direct VALUE parents verified. C001/C003/C004/C010/C017 use actual produced minimum; C004/C007/C008 use new generic initial FTL proofs; C019 calls Lemma1.2; C020 source refined/log bound; C021 same-stream stability; C012-15/C022-23 actual IID/kernel fixtures; C024 same actual bounded FTL obstruction; C025 general lower fixture; C026 general upstream harmonic producer. Nonzero variance, nonhalf initialization, T0 boundary, unequal benchmarks/current reveal and failure of ordinary comparator limits are substantive probes. These Test results do not count as new printed results or generic source denominator. Mathematical production advancement remains the four frozen actual initialized-FTL proofs for one additional source-required family. Distinct CANARY BODY, exact Tests append, full shared gates/readers/registry/site/FINAL/native/delivery pending. Source audit objects17, unknown proof total null; Goal ACTIVE.
''')
packet=RUN/'chapter-canary-BODY-packet-v1.md'
write(packet,'''# Distinct CANARY BODY review

Review actual Tests/OnlineLearningChapterAuditCanary.lean: exact8 approved imports,2 probe definitions,27 unchanged frozen headers and27 real theorem values; two necessary private unit-membership helpers only. CONTRACT receipt v1/neutral v2 reconstruction remain exact. v1 focused failure at C021 was Nat.cast_one type mismatch, repaired in proof body only; v2 compiler reports actual successful9114jobs. Full public whole-type value witnesses27/complete multiline axiom bracket audit27 standard-only/native fences and safe27pairs/compiler VALUE graph106selectednodes and required direct producers are separate evidence. Test theorem names/count are not canonical source results or proof denominator. No performance premises or true-minimum/IID/kernel/recurrent algorithm oracles were inserted. Numerical assertions and source producer calls both matter; verify actual VALUES rather than concluding from command exit0 alone.

Source17 inventory original16verbatim+required anyinitial family. Four canonical initialized-FTL bodies remain exactly BODY-accepted RAW, root exactappend compiled. Legal initialized FTL numeric rising0,1 regret+1/2 and negativecorrection-1/4; reviewer's old negative-regret example was withdrawn in sourcecorrection-v4; copied stale proposed G004 tense also corrected. Ordinary pinned literal source no-regret, upperepsilon predicate, bestaverage0, same bounded actualFTL limit obstruction and conditional iff remain distinct; no false universal ordinary-limit theorem. Generic50/54 and IID/AE/completed/kernel semantic deltas still apply;27 probes are complementary evidence, not generic Chapter1 proof by enumeration.

Input current RAW index includes all old372 current rows and current own proof/native outputs. Original372 mutable OWN session/trial rows now have approved stabilized/candidate append snapshots and receipts; old currentROOT exactappend before that index unchanged. Resolve historical original bindings with exact snapshots, never claim original mutable RAW stayed live-identical. Baseline2496 immutable files/old Test/pins/source/registry/globalSGB checked with common_proving_v2, sole approved ROOT append only; Tests root still unmodified. No readers edited, generated site untouched. Scope ONLY this actual Test BODY verdict; not full source/chapter/Goal acceptance.

Write ONLY chapter-canary-BODY-review-v1.md and chapter-canary-BODY-receipt-v1.json. Reuse your personally viewed original source pixels with exact hashes and disclose staged actor history; inspect actual bodies/types/proofVALUE/axioms/fences/source reconstruction/seven slots and all indexed RAW beforeafter. Verdict accepted|accepted-with-explicit-delta|rejected and blocking repairs. Keep same exact approved root/Test append and reader R1-R10 future scope; Tests append permitted only after accepted BODY/readiness. No proof/native/Git/reader/site mutation. Subsequent fullroot/Tests/harness/nonempty2basecontributor/ownshadow/sameregistry/site/DOM/personallyviewedpixels/FINAL/native/postnative/delivery required; entire Goal ACTIVE. Requested Astra medium, no human/external/absolute-blind or runtime attestation.
''')
paths=[Path(r['path']) for r in load(RUN/'chapter-canary-CONTRACT-inputs-v1.json')['rows']]
paths += [p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [p for p in CONTRACT.rglob('*') if p.is_file()]
paths += [ROOT/'Tests/OnlineLearningChapterAuditCanary.lean']
index=rows(paths)
write(RUN/'chapter-canary-BODY-inputs-v1.json',dict(rows=index,fixed_input_count=len(index),actual_canary_values=27,canonical_new_proofs=4,source_audit_objects=17,proof_total=None,chapter_complete=False,goal_complete=False))
fixed()
print('CANARY BODY currentRAW packet ready:',len(index),'inputs; no Tests integration/chapter acceptance.',flush=True)
