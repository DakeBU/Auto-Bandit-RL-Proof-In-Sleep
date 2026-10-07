from common_v1 import *
fixed()
decoder=load(RUN/'blind-decoder-receipt-v1.json')
assert decoder['actor']['task']=='/root/osd_blind'
assert decoder['input']['sha256_raw_bytes']==sha(RUN/'blind-packet-v1.md') and decoder['report']['sha256_raw_bytes']==sha(RUN/'blind-decoder-v1.md')
write(RUN/'source-visual-read-v1.json',dict(actor='/root',image=(RUN/'source-pdf16-v1.png').as_posix(),sha256=sha(RUN/'source-pdf16-v1.png'),actual_tool='view_image',viewed=True,observed='Source Lemma1.2 states Euclidean V, arbitrary V-domain real losses, assumed positive-prefix argmin; same current-prefix/final leader sums. Source proof explicitly uses finalleader feasibility. Theorem1.3 below is separate and not accepted here.'))
packet='''# Anti-anchored CONTRACT review: current Be-the-Leader package v1

Requested GPT-6 Astra/medium, no escalation/runtime attestation. Required distinct /root/source_reviewer actor; disclose reused prior review history, not blind/human/external. Search for mismatches rather than endorsing the formalizer.

Read source-card/contract/conversion/signature/DAG, full original PUBLIC and frozen public raw/native headers, seven frozen planned test headers, actual neutral reconstruction and exact type probe, ALL fixed rows in source-contract-inputs-v1.json. Rehash each raw row; cached PDF SHA must match source card, read Chapter1 PDF13-19 texts and actual VIEW source-pdf16-v1.png. Root's view receipt is separate from your own actual image reading. Public proof already historical, seven new named tests are targets without bodies; do not claim new source results/candidate proof acceptance.

For each N01-N08 give seven-slot assessment, source or validation-test status, exact acceptance/delta/repair. Main source comparison: V subset real Euclidean in source vs arbitrary X in Lean; domain-restricted real losses vs supplied ambient function; finite supplied feasible positive-prefix argmins vs existence construction; each n positive<=T; all u in V; current-prefix (includes present loss) vs strict-past causal FTL; source ell_(t+1)=Lean loss t and x*_n=leader n; T0 vacuous extension, T1 same side. Induction uses both positive-prefix membership and minimization. No convexity/compactness/probability/algorithm existence assumed or produced; no regret/logarithmic/no-regret theorem asserted here.

Planned tests must genuinely produce changing feasible Bool leaders and prefix argmins, strict -2<0, T0/T1 boundaries, and two concrete failure witnesses separately without optimality or feasibility. Frozen tests are meaningful validation, not new book results/duplicate public wrappers. Test missing-membership witness still produces ALL prefix minimization against singleton{false} but finalleader outside, inequality reversed. Source source-card page also contains Theorem1.3: it remains a future current package.

Retained initial neutral v1 layout failure, v2 exact closed-type/public rfl PASS; no mathematical statement changed. Source public/frozen old contracts/pins/inventory/oldcanary/globalSGB unchanged. New test module/one exact Tests-root import ONLY after CONTRACT acceptance and stabilization/proving. Later one-card/one-note source-qualified shared-reader correction, BODY/current combined/registry/actual pixels/FINAL/nativeaccepted/PR gates are distinct. Historical Chapter1 accepted-local status does not grant current chapter gate. Eight OTHER required Chapter1 semantic/contributor migrations, Chapter2 null/incomplete, Chapters3-16 unenumerated/appendix dependencies/wholeGoal ACTIVE. No public source mathematical closure recounted; new named tests only. Current exact OPEN PR186 881a1f57a2a018b16418e8ea62b869be5861d33e; no main/live/merge.

Write ONLY source-contract-review-v1.md and source-contract-receipt-v1.json in this RUN. Receipt actor.task=/root/source_reviewer; verdict accepted/rejected/accepted-with-explicit-delta; report path/report_sha256; reviewed_files [{path,sha256}] includes EACH frozen input row and exact report; fixed_input_count; source_pdf_sha256; required_mathematical_repairs/required_repairs/required_metadata_repairs arrays; required_reader_corrections array with stable IDs (R1 etc), exact text and evidence requirements for future BODY/reader/FINAL. Seven slots per N01-N08. Allow staged reader obligations without calling current candidate/FINAL/native accepted. All staged distinctions and zero-new-public/source closures explicit. Return compact real hashes.
'''
write(RUN/'source-contract-packet-v1.md',packet)
paths=[]
f=fixed()
mutable={'Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'}
paths.extend(p for p in f['fixed_files'] if p not in mutable)
paths.extend(p.as_posix() for p in sorted(RUN.rglob('*')) if p.is_file())
paths.extend(p.as_posix() for p in sorted(CONTRACT.rglob('*')) if p.is_file())
paths.extend(['tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md'])
paths=list(dict.fromkeys(paths));rows=[dict(path=p,sha256=sha(p)) for p in paths]
write(RUN/'source-contract-inputs-v1.json',dict(stage='CONTRACT',rows=rows,fixed_input_count=len(rows),original_before_reader_and_Tests_root_snapshots_bound=True,source_public_fixed=True,seven_canary_targets_frozen=True,canary_bodies_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual CONTRACT fixed rows',len(rows),'distinct review pending.')
