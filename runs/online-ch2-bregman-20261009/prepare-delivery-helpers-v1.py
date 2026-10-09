from publication_guard_v1 import *
fixed()
old=ROOT/'runs/online-ch2-proximal-20261009'
mapping={
    'publication_guard_v2':'publication_guard_v1',
    'online-ch2-proximal-20261009':'online-ch2-bregman-20261009',
    'online-ch2-proximal-v1':'online-ch2-bregman-v1',
    'ONLINE-CH2-PROXIMAL-20261009':'ONLINE-CH2-BREGMAN-20261009',
    'online-ch2-proximal-delivery':'online-ch2-bregman-delivery',
    '3a81dd6ae283fce90b849d928c18094f37b6d3b7':'69aeeeaf58364177a06bbc10329ea328c3c13b3c',
    '29086b6f3a033f6536054f4d9a06ae0e9b2f8a91':'71f2219fa1648094eba8aa17b50e443258f436cb',
    'codex/research-online-ch2-prescient':'codex/research-online-ch2-proximal',
    'PR205':'PR208','PR #205':'PR #208',"'205'":"'208'",
    '9108':'9109','9276':'9278','10995':'10996','1420':'1619',
    'publication-status-review-v2.json':'RAW-format-review-v1.json',
    'approved_RAW_EOF_exceptions':'approved_RAW_exceptions',
    'received decoder EOF':'received decoder LaTex trailing-space',
    'immutable EOF':'immutable LaTex trailing-space',
    '4originals':'14originals','4original':'14original',
    '4source-guide':'11source-guide','10source-guide':'11source-guide',
    'DOM10formulas':'DOM11formulas','graph4nodes':'graph8nodes','selected4nodes':'selected8nodes',
    '6required VALUE':'8required VALUE','6requiredVALUE':'8requiredVALUE',
    '10996old+1':'10996old+6','10996old+1node':'10996old+6nodes',
    '10996complete prior records+1':'10996complete prior records+6',
    'Counter1->0':'Counter5->0','counter1->0':'counter5->0','acceptance1->0':'acceptance5->0',
    'helper1->0':'helpers5->0','Counter1->0':'Counter5->0',
    ': new blank line at EOF.':': TRAILING_PLACEHOLDER.',
    ': trailing whitespace.':': new blank line at EOF.',
    ': TRAILING_PLACEHOLDER.':': trailing whitespace.',
}
def adapted(name):
    s=(old/name).read_text(encoding='utf8')
    for a,b in mapping.items():s=s.replace(a,b)
    return s
s=adapted('record-acceptance-v1.py')
s=s.replace('assert len(names)==1','assert len(names)==5')
s=s.replace("public_canaries=3","public_canaries=2,canonical_definitions=1")
s=s.replace("'--obligations-before','1'","'--obligations-before','5'")
s=s.replace('bounded_obligations_before=1','bounded_obligations_before=5')
s=s.replace("==(1,0)","==(5,0)")
s=s.replace('Counter1->0 ONLY one exact derived helper','Counter5->0 ONLY five exact derived proofs; canonical definition separate')
s=s.replace('one-frozen-real-comparison-v1','five-frozen-Bregman-proofs-v1')
start=s.index("bound='");end=s.index('\nwrite(',start)
s=s[:start]+"bound='Canonical actual-fderiv Bregman definition, five exact derived Bregman algebra/nonnegativity/gradient/proximal proofs and two nonsmooth nonquadratic/boundary Test families. Actual supplied minimum derives comparison retaining both negative residuals; old point may lie outside V, both psi derivative hypotheses explicit. Full source X/interior/local-extension/EReal finite-domain supports/convexity/minimum bridges, actual attained current-loss recursion/interiority and sharp same-run fixed/variable telescopes remain REQUIRED/OPEN, including main-text fixed-step exercise. All8 Chapter2 forwards OPEN, Chapter2 incomplete, proof denominatornull, whole16GoalACTIVE. No merge/deploy/main/live/CI/retirement.'"+s[end:]
start=s.index("write(RUN/'memory-digest-accepted-v1.md'");end=s.index("\nwrite(CONTRACT",start)
s=s[:start]+"write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\\n\\n'+bound+'\\n\\nDistinct bounded FINAL '+sha(final)+'. Root9109/Tests9278/fullharness472tests7existing skips/exporter/checkpassed, first current full attempt0. Seven normalized frozen proof headers plus canonical definition, seven fullpublicVALUEs/fourteenstandard-onlyaxiomoutputs. Selected8nodes/1619coalesced direct TYPE_VALUE presences/8requiredVALUEpairs; both separately selected final numeric branches retain proximal helper. Clean SITEv1/check/registry10996completeold+6newproduction at69aeeeaf58364177a06bbc10329ea328c3c13b3c. Two nonempty contributor bases. Actual local-file desktop11formulas/zeroerrors/geometry/14originals inspected by root and distinctFINAL. No HTTP/live/later-head-site claim. Compiler/API/collision failures, raw-header/native hashes and two immutable SHA-bound received LaTex trailing-space exceptions retained: full2/scoped0. Native/postnative/delivery separate.\\n')"+s[end:]
s=s.replace("Counter1->0 ONLY one exact derived helper, not printed source/chapter coverage.","Counter5->0 ONLY five frozen derived proofs, canonical definition separate, not printed source/chapter coverage.")
s=s.replace('Counter1->0','Counter5->0').replace('Counter5->0 ONLY one exact derived helper','Counter5->0 ONLY five exact derived proofs')
s=s.replace('ONLY one derived real convex-minimizer comparison accepted','ONLY five derived Bregman dependency proofs and one canonical definition accepted')
s=s.replace('review:bounded-real-comparison-FINAL:accepted','review:bounded-Bregman-FINAL:accepted')
start=s.index("c['graph_contribution']['visual_review']=");end=s.index('\nCONTRIBUTION.write_bytes',start)
s=s[:start]+'''c['graph_contribution']['visual_review']='Selected8nodes/1619direct TYPE_VALUE presences/8requiredVALUEpairs and two individually selected final numeric helper branches inspected. Complete registry10996old+6production nodes; actual local-file1440px desktop14originals personally inspected by root and distinctFINAL. No Test/per-Book duplication/HTTP/all-viewports claim.'
c['verification']['bandit_check']='Actual root9109/Tests9278/full harness exit0,472tests7existing skips/exporter/checkpassed first current full attempt; sources tracked beforehand, no rule/test/pin weakening.'
c['verification']['site_build']='Actual clean isolated SITEv1 exit0 at69aeeeaf58364177a06bbc10329ea328c3c13b3c, applicable unchanged proof/root/pins fullgate. No later evidence-head fresh build/deploy claim.'
c['verification']['site_check']='Actual SITEv1/check/registry exit0,10996complete prior records+6source-qualified production nodes. Local-file browser11source-guide formulas/zeroerrors/strict desktopgeometry/14originals root and distinctFINAL inspected;4exactgeneratedfiles unchanged. Prior HTTP service rejection preserved, no retry/HTTP/live claim.'
c['verification']['independent_review']='Distinct staged CONTRACT/BODY/canary/reader/RAW and boundedFINAL accepted-with-explicit-delta '+sha(final)+'. Five derived proofs/one canonical definition/two canary families only; full source/Chapter2 incomplete. Two SHA-bound immutable received LaTex trailing spaces, full2/scoped0; failures retained. OWNpostnative/actualdelivery pending. Requested Astra/medium automated actors with reused related history; no human/external/absolute-blind/runtime attestation.'
'''.rstrip()+s[end:]
start=s.index("suffix='");end=s.index('\nfor p in docs:',start)
s=s[:start]+"suffix='\\nBoundedFINAL update: canonical Bregman definition plus five exact dependency proofs and two actual nonsmooth Test families accepted-with-explicit-delta; FINAL SHA '+sha(final)+'. CombinedLean/fullharness/cleanSITEv1/sharedregistry/localfile14pixels passed. OWNnative5->0 ONLY five frozen derived proof obligations, definition separate; postnative/draftPR pending. Fullsource/all8Ch2forwards REQUIRED/OPEN, chapterdenominatornull, wholeGoalACTIVE. Historical pending entries retain stage meaning. No main/live/merge/deploy/retirement/HTTPclaim.\\n'"+s[end:]
start=s.index("write(RUN/'PR-body-v1.md'");end=s.index("\nwrite(RUN/'PR-plan-v1.json'",start)
s=s[:start]+'''write(RUN/'PR-body-v1.md',"""Adds one canonical Bregman divergence using the actual Frechet derivative and five reusable proofs: self identity, source-oriented three-point identity, convex nonnegativity, gradient conversion and a nonsmooth proximal comparison derived from an actual supplied minimum. The comparison retains both negative residuals, allows the old point outside V and does not differentiate the loss. Two public test families prove their own minima: a nonquadratic regularizer with absolute loss and an interval boundary minimum with an outside initial point. Both final numerical proof branches retain the public helper.

Validation: focused builds, full public VALUE/kernel and standard-only axiom audits, seven frozen proof headers plus canonical definition, eight required compiled VALUE pairs and both separately selected numeric tails. Combined root9109/Tests9278 and full harness472tests with7existing skips/exporter/checkpassed, first current full attempt0. Two nonempty contributor bases and clean isolated site/check/shared registry passed at69aeeeaf58364177a06bbc10329ea328c3c13b3c:10996complete prior records preserved plus6shared production nodes. Fourteen actual local-file desktop originals, formulas and geometry inspected by root and a distinct staged automated FINAL reviewer. No HTTP/live/later-head-site claim. Full whitespace reports exactly two immutable SHA-bound received decoder LaTex trailing spaces; scoped check passes excluding only these reports.

Stacked on OPEN unmerged PR #208, exact base71f2219fa1648094eba8aa17b50e443258f436cb, branch codex/research-online-ch2-proximal. This is a necessary Chapter2 prescient dependency, not complete Algorithm15.8/Theorem15.30 or Chapter6/15 acceptance. Source X/interior/local-extension validity, finite-domain extended-real/subgradient/convexity/minimum bridges, actual attained current-loss recursion/interiority and sharp same-run fixed/variable terminals including the main-text fixed-step exercise remain REQUIRED/OPEN. All8 Chapter2 forwards remain open, Chapter2 partial, Chapters1–16 Goal ACTIVE. No merge/main/live/CI/deploy/retirement claim. Functor audit: none-found-with-reason.

Evidence: docs/contracts/online-ch2-bregman-v1; runs/online-ch2-bregman-20261009/FINAL-review-v1.md and SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-BREGMAN-20261009.json. Native and concrete delivery records receive separate inspection.
""")'''+s[end:]
s=s.replace('[Online Learning Ch2] Prove nonsmooth convex proximal minimizer comparison','[Online Learning Ch2] Prove canonical Bregman proximal comparison')
write(RUN/'record-acceptance-v1.py',s)
for name in ['deliver-v1.py','prepare-post-native-inputs-v1.py']:
    s=adapted(name)
    s=s.replace('one derived real comparison','five Bregman dependency proofs and one canonical definition').replace('one derived real comparison','five frozen derived proofs').replace('one derived real comparison','five derived proofs')
    s=s.replace('exact two SHA-bound received decoder EOF exceptions','exact two SHA-bound immutable received decoder LaTex trailing-space exceptions')
    s=s.replace('Record accepted proximal comparison verification and reader evidence','Record accepted Bregman proof verification and reader evidence')
    write(RUN/name,s)
print('Prospective own acceptance/postnative/delivery helpers ready; not executed before distinct reviews.')
