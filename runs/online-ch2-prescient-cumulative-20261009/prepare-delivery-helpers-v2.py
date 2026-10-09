from common import *
prior=ROOT/'runs/online-ch2-prescient-causal-20261009'
bound=('Five frozen conditional same-run cumulative proofs: actual consecutive Option outputs produce the common divergence sum; fixed and positive nonincreasing played steps yield sharp bounds retaining negative terminal and movement terms; strict generator convexity certifies terminal nonnegativity for the printed forms. Two complete16/22conjunct public canaries use actual distinct losses/nonquadratic generator and genuinely decreasing steps; four independently selected numeric proof branches retain the corresponding new production theorem. Full source X/interior generator and source loss hypothesis transport plus source valid-run wrapper remain REQUIRED/OPEN. All8Chapter2forwards OPEN, Chapter2partial/denominatornull, wholeChapters1-16GoalACTIVE. Not full Algorithm15.8/Theorem15.30/Chapter6/15/Chapter2 acceptance or source erratum. No merge/deploy/main/live/CI/retirement.')
body='''Derives cumulative prescient Bregman regret from the same actual partial recursion. The common summation bound allows arbitrary positive played steps and zero rounds. Fixed and nonincreasing-step sharp bounds retain the negative terminal divergence and movement terms; the printed forms drop only the terminal term after proving its nonnegativity. No desired one-step regret inequality is assumed.

Two complete public canaries use restricted nonsmooth/affine losses, a nonquadratic generator, actual states 1/2 -> 0 -> 1/2, and a genuinely decreasing schedule. Four separately selected numeric proof branches retain their specific new production theorem. The previous-state maximum is checked at a comparator where it differs from the initial divergence.

Validation: focused and combined Lean root/Tests builds, public VALUE probes, frozen statements, standard-only axiom audit, full harness (472 tests, 7 existing skips), scoped frontier shadow, and two contributor bases. A clean local site build/check preserves all 11,015 old registry records and adds five production nodes. Root and distinct staged automated review inspect twelve actual desktop originals. The reader scope ambiguity and exact prose-only repair, earlier failures and RAW history remain in the evidence. The site build applies to its bound candidate commit; no fresh site build at the later evidence commit is claimed.

Stacked on OPEN draft unmerged PR #211, exact 24de0231aa067f141251aac5c20deb58e448ea66, branch codex/research-online-ch2-prescient-causal. These five conditional interfaces advance a required Chapter2 forward dependency. Full source-domain/generator/loss hypothesis transport and a valid source-run wrapper remain required/open; all eight Chapter2 forward containers remain open. Chapter2 and the Chapters1-16 Goal are incomplete. No full Algorithm15.8/Theorem15.30, Chapter6/15 acceptance, merge, deployment or main/live update. Functor audit: none-found-with-reason.

Evidence: docs/contracts/online-ch2-prescient-cumulative-v1; runs/online-ch2-prescient-cumulative-20261009/FINAL-review-v1.md and bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-CUMULATIVE-20261009.json.
'''
s=(prior/'record-acceptance-v1.py').read_text(encoding='utf8')
s=s.replace('assert len(names) == 8','assert len(names) == 5')
needle="targets = load(CONTRACT / 'stabilized-v1.json')['targets']"
assert s.count(needle)==1
s=s.replace(needle,needle+"\nfor t in targets:\n    t['statement_hash']=next(load(f)['statement_hash'] for f in CONTRACT.glob('*fence-v1.json') if load(f).get('declaration')==t['declaration'])")
a=s.index('bound = ');b=s.index('args = ',a)
s=s[:a]+'bound = '+repr(bound)+'\n'+'''write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL '+sha(final)+'. Seven complete public VALUEs/standard-only axiom lists,7frozenheaders/nativefences;7selectednodes/1885coalesced directTYPE_VALUE presences/8production+5canaryVALUEpairs/fourselectedEq.mprnumericbranches. Actual combinedroot/Tests/fullharness in full-harness-inspected-v1; exact math/pins unchanged after applicable gate. Clean repaired SITEv2 source '+load(RUN/'clean-candidate-site-binding-v2.json')['actual_head']+';11015oldregistryrecords+5production=11020. Actual local-file desktop14formulas/12root+distinctoriginals, notHTTP/live/mobile. Original reader ambiguity/13fieldapprovedrepair and preparation resolver missing-field failure retained. Compiler/native/semantic/site gates separate; postnative/delivery pending.\n')
write(RUN/'current-obligations-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],raw_UTF8_header_sha256=t['statement_sha256'],native_normalized_statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],public_canaries=2,new_definitions=0,generated_Test_auxiliaries=0,FINAL_sha256=sha(final),source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Root records distinct source_reviewer FINAL '+sha(final)+'. Counter5->0 ONLY five frozen derived proofs, not source/chapter coverage. Postnative/delivery pending.'
'''+s[b:]
for old,new in [("'eight-frozen-prescient-causal-proofs-v1'","'five-frozen-prescient-cumulative-proofs-v1'"),("'--obligations-before', '8'","'--obligations-before', '5'"),('bounded_obligations_before=8','bounded_obligations_before=5'),('== (8, 0)','== (5, 0)'),('Persistent Orabona Chapters1-16; ONLY eight prescient causal derived proofs accepted','Persistent Orabona Chapters1-16; ONLY five conditional prescient cumulative proofs accepted'),('review:bounded-prescient-causal-FINAL:accepted','review:bounded-prescient-cumulative-FINAL:accepted')]:
    assert old in s,old;s=s.replace(old,new)
a=s.index("c['semantic_roundtrip']['remaining_semantic_delta'] =");b=s.index('CONTRIBUTION.write_bytes',a)
s=s[:a]+'''c['semantic_roundtrip']['remaining_semantic_delta']=bound+' Distinct staged CONTRACT/BODY/canary/reader-repair and boundedFINAL '+sha(final)+'; reused related actor history disclosed, no human/external/absolute-blind/runtimeattestation. OWNpostnative/deliverypending.'
c['verification']['independent_review']='Distinct boundedFINAL '+sha(final)+'. Five conditional proofs/two complete public canaries; actual combined gates/sharedregistry/repaired12original localfile pixels reviewed. Full source/Chapter2/Goal OPEN. OWNpostnative/concrete deliverypending. RequestedAstra-medium/stagedrelatedactors, no human/external/runtimeattestation.'
c['graph_contribution']['visual_review']='Selected7public/7totalnodes,1885coalesced directTYPE_VALUE presences/8production+5canaryVALUEpairs/four individuallyselected Eq.mpr numericbranches. All11015complete oldregistryobjects unchanged+5production=11020. Actual localfile desktop1440/14formulas/zeroerrors/12originals personallyviewed byroot anddistinctFINAL; foldedLean/built-inwrap. NotHTTP/live/allviewports/perBookduplicates/fulltransitive/sourcecount.'
'''+s[b:]
a=s.index("suffix = ");b=s.index('for p in docs:',a)
s=s[:a]+"suffix='\\nBounded FINAL accepted: '+bound+' FINAL SHA '+sha(final)+'. OWNnative5->0 only these five proofs. Combined gates/fullharness and repairedSITEv2/sharedregistry/localfile12pixels reviewed. Postnative/draftPRpending; historical pending entries retain stage meaning.\\n'\n"+s[b:]
a=s.index("write(RUN / 'PR-body-v1.md',");b=s.index('fixed()\nprint(',a)
s=s[:a]+"write(RUN/'PR-body-v1.md',"+repr(body)+")\nwrite(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove same-run prescient cumulative regret',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base='codex/research-online-ch2-prescient-causal',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))\n"+s[b:]
write(RUN/'record-acceptance-v1.py',s)
def adapt(n):
    s=(prior/n).read_text(encoding='utf8')
    for old,new in [('codex/research-online-ch2-extended-proximal','codex/research-online-ch2-prescient-causal'),('online-ch2-prescient-causal-delivery','online-ch2-prescient-cumulative-delivery'),('PR210','PR211'),('PR #210','PR #211'),("'210'","'211'"),('41f1fb26915b3bf7f84035393080991c38aeba64',BASE),('clean-candidate-site-binding-v3.json','clean-candidate-site-binding-v2.json'),('prescient causal proof','prescient cumulative proof')]:
        s=s.replace(old,new)
    return s
s=adapt('deliver-v1.py')
s=s.replace("rows([RUN/'exact-RAW-line-ending-snapshots-v1.json'])","rows(RUN.glob('exact-RAW-line-ending-snapshots-v*.json'))")
write(RUN/'deliver-v1.py',s)
s=adapt('collect-actual-delivery-v1.py')
s=s.replace("load(RUN/'official-PR-attachment-v1.json')['actual_result']['isError']","load(RUN/'official-PR-attachment-v1.json')['actual_result'].get('isError',False)")
a=s.index("write(RUN/'actual-delivery-packet-v1.md'");b=s.index('paths={p for d',a)
packet='''# Actual prescient cumulative draft PR delivery

Independently inspect actual durable receipts: deliveredhead=remote=OPENdraftunmergedPRhead, exacttitle/body/base/head, parentPR211 exact24de0231aa067f141251aac5c20deb58e448ea66. Two current nonempty contributor gates/scoped staging/fullpackagewhitespace0/noexceptions/RAWCRLFsnapshots. Official successful attachment is durably bound. Independently hash all inputsbeforeafter, permitted FINAL/postnative transitions only. CleanSITEv2 applies onlyto itsboundsourcecommit, not laterdeliveryhead. ActualfileURI12pixels notHTTP/live/mobile. Priorreaderambiguity/exact13fieldrepair/failurehistoryimmutable.

Review final-evidence-delivery-v1.py: onlyNEWOWNRUNactualdelivery/reviewevidence+RAWsnapshot committed/pushed; ignoredterminalobservationsverifynewremote/PRhead withunchangedtitle/body/base/draft/unmerged. No selfreferenceevidenceloop or existingmath/reader/nativeinputmutation, merge/deploy/retirement/globalcredentials. Fiveconditionalproofs5->0/twofullcanaries, not fullsource/chapter/Goal. Full sourceX/interiorgenerator/loss premise transport andvalidrunwrapper/all8forwards REQUIREDOPEN, whole16GoalACTIVE.

Create-only actual-delivery-review-v1.md/json withverdict/actual_delivery_verdict/prospective_evidence_only_commit_verdict/required_repairs/report/inputSHAs/independentRAWbeforeafter/actualhead/PR/officialattachmentbindings. DistinctreusedstagedrequestedAstra-medium, nohuman/external/runtimeattestation. Do notpublis/editinputs.
'''
s=s[:a]+"write(RUN/'actual-delivery-packet-v1.md',"+repr(packet)+')\n'+s[b:]
write(RUN/'collect-actual-delivery-v1.py',s)
write(RUN/'final-evidence-delivery-v1.py',adapt('final-evidence-delivery-v1.py'))
for n in ['record-acceptance-v1.py','deliver-v1.py','collect-actual-delivery-v1.py','final-evidence-delivery-v1.py']:
    compile((RUN/n).read_text(encoding='utf8'),n,'exec')
print('Prospective exact bounded acceptance/delivery helpers ready; no acceptance/push/PR executed.')
