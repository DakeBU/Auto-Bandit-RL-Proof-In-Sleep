from common_reader_v8 import *
import base64
fixed()
assert load(RUN/'delivery-post-native-state-v1.json')['actual_remote_head']=='14567d019c31f8f307ac5ab765144ae7d71f1ea1'
assert sha(RUN/'FINAL-receipt-v1.json')=='7f0ade24d0d121dcd4d9d7d91a5c73478b5b5d011c6433ec5242e418b02abf50'
assert sha(RUN/'FINAL-review-v1.md')=='b10f8558fc3560a27d6c0f781f41613239cad886309ca5e638a78efb319ed593'
snapshots={}
for p in (RUN/'snapshots').rglob('*'):
 if p.is_file():snapshots.setdefault(sha(p),[]).append(p)
historical=[];unchanged=0
for r in load(RUN/'FINAL-inputs-v2.json')['rows']:
 current=sha(r['path'])
 if current==r['sha256']:unchanged+=1;continue
 assert r['sha256'] in snapshots,r['path']
 snapshot=snapshots[r['sha256']][0]
 historical.append(dict(path=r['path'],FINAL_sha256=r['sha256'],exact_before_snapshot=snapshot.as_posix(),current_sha256=current))
write(RUN/'post-native-FINAL-historical-resolution-v1.json',dict(FINAL_input_count=1128,unchanged_live_count=unchanged,changed_with_exact_before_snapshot=historical,original_review_and_receipt_unchanged=True,changes_require_field_suffix_adjudication=True))
scope=[RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]
p=subprocess.run(['git','add','--',*scope],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'post-native-review-stage-v1.json',dict(actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii')));assert p.returncode==0
exceptions=load(RUN/'post-native-RAW-exception-addendum-v5.json')['exact_RAW_exceptions']
allowed={Path(r['path']).relative_to(ROOT).as_posix() for r in exceptions}
command=['git','diff','--cached',BASE,'--check'];p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
observed={s.split(':',1)[0] for s in p.stdout.decode('utf8').splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
assert observed==allowed and p.returncode==2,(observed-allowed,allowed-observed,p.returncode)
for r in exceptions:assert sha(r['path'])==r['sha256']
write(RUN/'post-native-review-full-diff-v1.json',dict(command=command,actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii'),exact_exceptions=exceptions,unexcluded_clean=False))
p=subprocess.run(command+['--','.',*[':(exclude)'+f for f in sorted(allowed)]],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'post-native-review-scoped-diff-v1.json',dict(actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii')));assert p.returncode==0
packet='''# Distinct Chapter1 post-native and published-delivery review

Reuse your source FINAL analysis only with the exact report/receipt/code/source/body/canary fingerprints and disclose reuse. This is separate adjudication of actual post-FINAL changes and published delivery, NOT another formalizer self-review. GPT6Astra/medium; distinct model reviewer, no human/external/runtime attestation. Hash every RAW row in post-native-inputs-v1.json before and after. Write ONLY post-native-review-v1.md and post-native-receipt-v1.json.

Source FINAL accepted-with-explicit-delta all17sourceobjects/seven slots/R1-R10; four new general-initial proofs one source family; 54genericcontracts/27canaries/null proof-total not a denominator. Exact source, old50/current4PUBLIC/Test27 types/values, roots and pins remain unchanged. Actual combined root9105/Tests9270/fullharness472tests7skip plus exporter and wholevalues/axioms/fences/directVALUE remain applicable by exact input hashes. Do not recast command0 as compiled. The ordinary finite comparator-limit source wording/counterexample/reviewed correction remains explicit and is not a proof of the false universal inference or author endorsement. Separate source acceptance versus chapter gate versus wholeGoal versus main/live.

Inspect FINAL historical resolution: all changed current bindings must resolve to exact before snapshots, not a false claim all1128 liveunchanged. Post-FINAL snapshots/field-suffix-audit-v2 permit only OWN task/obligations/conversion, contribution verification and semantic statuses, OWN native trials/session/state/retrieval/memory plus C1-only readers/coverage and new versioned17ledger. Exact prior native prefixes and unrelated baseline records are retained. Actual19trials=13old+5failures+1distinct-review record; session accepted sequence7 is source17integration, NOT chapter gate. Ownshadow passed; no globalSGB/frontier/trials/memory/index changes. Current tasks replace stale bootstrap status with explicit actual evidence; old raw versions remain. Original16sourceintent preserved. Current ledger chapter-one-post-native-v5 is chapterfalse/accepted-source-objects0/prooftotalnull, all17sourceacceptedwithdelta. One known_gaps/open_gaps schema mistake was caught and fixed before any site attempt; inspect both snapshot and audit, no deletion of other fields.

Current neutral reader status names the versioned ledger and explicit source correction without prematurely asserting chapteracceptance. Audit the exact changed fields and old417highlights/20oldcards/alloldroutes/otherBookrows/history preservation. SITE4 was built clean from actual14567d019c31f8f307ac5ab765144ae7d71f1ea1 with applicable unchangedLean gate, source_dirtyfalse/lean_verifiedtrue; site/check/registry actual0. Complete10977oldregistryrecords unchanged plus4publictheorems=10981; no Test/private/productiondef nodes added. Both NONEMPTY contributor bases actual0 cover production. Current neutral reader content and site provenance are separate from older accepted candidate SITE3.

Personally view all TEN CURRENT ORIGINAL v3 files listed formula-render-v3.json using view_image. Root review does not substitute yours; four module images match prior v2 hashes but are current captured outputs. Browser actualNode0 AND wrapper0, exclusivewxoutput names, no overwrite; generatedHTML unchanged guard,24mathcontainers/noerrors/geometry. Inspect current DOM/browserreport/registry/formulas/statustext, all four complete wrapped catalogue types. Only desktop1440; tall tool display resized disclosed. No mobile/live/allviewports claim. Historicalfailedwrapper1/recovery0 and old restored v1 evidence remain immutable; no reclassification of failure as success.

Actual PR203 exists OPEN/draft/UNMERGED on current branch, remoteexact14567d019c31f8f307ac5ab765144ae7d71f1ea1, stackbasePR202 OPENdraftunmerged exacta03f304522ed30ee34d43b38bd67deffbbf3b08f. Inspect published API body equals PR-BODY-post-native-v2.md, exactpushcommand0, officialappattachment toolresult. Canonicalmain/origin clean6847 unchanged; not merged/deployed/live. gh activeaccount command-scoped helper fixed old403 withoutglobalcredentialmutation. CurrentHEAD proof/readers/source are published; newly generated local evidence/report files will require bounded final metadata commit/push, not yet claim published. CI is not asserted passed. Actual local Lean/harness/site evidence is separately sufficient for scoped local verification. Review all current helper/prose/indexed files introduced postFINAL by scope, not a blanket approval of unknownfuturecontent.

Cumulative actualfull2 EXACT14 SHA-bound RAW exceptions:12logs+2frozendecoderEOF. SourceFINAL accepted13; the NEW successful-push RAWlog delivery-candidate-push-v2.log requires your explicit new adjudication. New diagnostics/pushstdout stored as base64JSON to avoid further exceptions. Scopedactual0; no code/Test/reader/contract/helper exception. Do not claim unexcludedclean.

Return accepted|accepted-with-explicit-delta|rejected; separate native/status-reader/publication/delivery judgments, exact current10pixelsha/actualview, historicalbinding/field-suffix/full14exceptions verdict and requiredrepairs. If favorable, state bounded final metadata permissions sufficient to record Chapter1 accepted-local-with-explicit-source-correction only after current actual native/shadow/site/source/publication/delivery evidence: new chapter-one-accepted-v6 ledger (all17sourceobjects accepted with original16/correction/prooftotalnull), C1-only coverage accepted/status/receipt fields, OWN task/obligations/conversion/contribution semantic/verification/progress status, OWN memory/retrieval/frontier/native FINAL record if applicable. Current three website JSON files need NO further mutation. Roots/Test/code/source/oldrecords/otherchapters/globalfrontier/pins remain forbidden. Require snapshots/fielddiffs/scoped-contributor and ownshadow where applicable, exact final commit/push/publishedbody verification, worktree retained. Specify whether final bounded metadata delivery needs a short further distinct actual-head check. A chapter flag must not imply all16Goal complete; C2partial/C3-16unenumerated/necessaryappendices still required. No merge/deploy authorization.
'''
write(RUN/'post-native-review-packet-v1.md',packet)
write(RUN/'memory-digest-post-native-v1.md','Current Chapter1 source17 FINAL accepted-with-explicit-delta; native source transition and ownshadow actualpassed; clean SITE4/registry/bothNONEMPTYbases/currentbrowserNode0wrapper0/root10pixels actual. DraftPR203 remote14567 bodyv2/appattached stackPR202a03f OPENunmerged. Separatepostnative/current10distinctpixels/deliveryreview pending. Exact14RAWexceptions full2/scoped0; nullproofdenominator; currentchapterfalse/wholeGoalACTIVE/mainliveunchanged. Finalmetadata/evidencepublication remains pending. Worktree activepreserved; code/pins/privatepaper/frozen/globalSGB/oldrecords unchanged except exact reviewed root/Test appends and bounded C1reader fields.')
paths={Path(r['path']) for r in load(RUN/'FINAL-inputs-v2.json')['rows']}
paths.update(p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update([SITE/'chapters/online-foundations/index.html',SITE/'books/registry.json',SITE/'site-manifest.json'])
paths.update(SITE/p for p in load(RUN/'registry-v4.json')['module_HTML_sha256'])
assert all(p.is_file() for p in paths)
write(RUN/'post-native-inputs-v1.json',dict(phase='distinct Chapter1 post-native/current-status-reader/published-delivery review',rows=rows(paths),source_objects=17,generic_contracts=54,canaries=27,proof_total=None,chapter_complete=False,whole_Goal_active=True))
fixed();print('Post-native review packet ready:',len(paths),'current RAW rows;',len(historical),'historical bindings resolved; full2 exact14/scoped0.')
