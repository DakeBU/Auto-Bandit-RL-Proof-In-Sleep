from publication_guard_v1 import *
publication_fixed(after_native=True)
audit=load(RUN/'post-native-root-audit-v1.json');assert audit['state_exact_expected'] and audit['all_other_FINAL_inputs_RAW_unchanged']
scope=load(RUN/'post-native-scope-inspected-v1.json');assert scope['actual_full_BASE_whitespace_exit']==0 and scope['both_nonempty_contributor_bases']
write(RUN/'post-native-packet-v1.md','''# Distinct postnative review

Review actual final native metadata transition, not merely its plan or wrapper exit. Read complete FINAL decision/report/input manifest, both native helpers, original RAW snapshot/native plan and post-native-root-audit. Independently call publication_guard_v1.publication_fixed(after_native=True) and native_transition_check. All34991oldbaselineRAW/sixapprovedAFTER/production/Test/root/pins/frozen headers remain unchanged. Every FINAL input outside the EXACT eight mutable OWN paths remains RAW unchanged. Eight paths are manifest SIX textfields, four documents exactsuffix, trials appendONE accepted review with production1->0 only, events appendTWO stable-ID candidate+accepted and exact state next+2/currententry/currentleaf. Native candidate is explicitly retrospective transport of earlier actual candidate evidence; do not claim real-time enforcement. Journal/attrs/globalSGB immutable. Original snapshots must match historical FINAL input hashes, not self-asserted new originals.

ONE production proof/sourcelemma,zero definitions,two FULLpubliccanaries and three selected inequality VALUE calls are separate quantities. No sourcecontainer/Chapter2/adaptiveOSD/Chapter4/wholeGoal closure. Standard axioms and actualroot9116Tests9292/fullretry472tests7skips remain applicable with exact source/pin hashes; metadata checks do not rerun Lean. Original failed harness, whitespace and browser launch/catalog failures remain. CleanlocalSITE6c935087 versus later evidenceHEAD preserved,11054completeoldnodes+one=11055,15cards18MathJax/four successfuloriginaldesktopimages already personally root+FINAL reviewed. No embedded proofBODY in catalog; pinned source proof link verified. No new pixel-view claim needed if original bindings unchanged.

Check actual native command receipts, five OWN trialrows with onlylastreview accepted, originalfourattempts unchanged, candidate/accepted parent/sequence/payload/ID exact, trial reviewer_validated=true/1->0onlyonefrozenproductionterminal and FULLcanaries separate. OWN frontier real native RAW retained ignoredtmp/base64 plus explicitly parsedLFcopy; actual shadowzero mismatches/would_mutate=false. Both actual postnative contributor gates NONEMPTY and mention module; fullBASE ordinary whitespace/cachedscope/blobRAW checks pass. No global shared frontier/currentpointer rewrite.

Output ONLY post-native-review-v1.md/json with verdict/post_native_verdict,required_repairs,report/report_sha256,input_manifest/input_manifest_sha256, exact transition/immutable/current gate judgments and delivery-pending boundary. Recheck all postnative current input RAW before/after; no helper execution or file mutation except these review outputs. No commit/push/PR creation authorization from this review unless a later exact delivery plan/helper is separately reviewed. User already authorized scoped commits/nonforcepush/draftPR overall; this internal evidence gate does not request user approval again. No merge/deploy/main/live/retirement/Goalcomplete. Reused distinct automated actor/history limits disclosed.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([MODULE,TEST,CONTRIBUTION,PDF])
paths.update(ROOT/p for p in OLD_ALLOWED)
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index'])
paths.update(Path(r['path']) for r in load(FINAL_INPUTS)['rows'])
publication_fixed(after_native=True)
write(RUN/'post-native-inputs-v1.json',dict(rows=rows(paths),FINAL_sha256=sha(FINAL),bounded_production_proof_counter=[1,0],public_canaries_separate=2,source_family_count=1,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal='active'))
print('Actual postnative packet prepared; distinct review and delivery pending.',flush=True)
