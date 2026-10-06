"""Record only an actual app-attached scoped draft; legacyqueue0 never closes Chapter2."""
from common_v2 import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['head']['ref']=='codex/research-online-lipschitz-migration' and pr['base']['ref']=='codex/research-online-affine-subgradient-migration'
assert load(RUN/'base-PR175-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-final-v1-01','committed-raw-audit-v1-01']:passed(label)
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','final-reader-receipt-v1.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v1.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json','formula-visual-review-v1.json','formula-render-v1.json']
counts={k:a[k] for k in ['source_formal_results','source_definitions','retained_public_proofs','retained_definitions','new_public_proofs','new_definitions','new_test_proofs','new_registry_nodes']}
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=175,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],legacy_queue=0,legacy_zero_not_chapter_completion=True,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for next required source/contract after DIRECTclean/localremoteREST/allcurrentrunraw audit.',final_head_boundary='Final metadata head checked DIRECT without recursive self-head artifact.',**counts))
write(RUN/'delivery-v1.md',f'''# Bounded Definition2.29/Theorem2.30 delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, appattached/unmerged. Branch {pr['head']['ref']}; exact PR175 base{BASE}; creationhead{pr['head']['sha']}; applicable clean local site source{reg['source_commit']}. Final metadata head checked DIRECT afterwards. Canonicalmain/live unchanged.

ONE retained owned finite-value/allpairs definition/ONE full interior iff proof, ZERO new mathematical/TEST/registry nodes. {a['explicit_delta']}

Current distinct CONTRACT/convention/BODY/FINAL/native acceptance, actualbody/whole18canaryproof6TESTdefs2abbrevs/28kernel2guards/ready2nodes260refs4pairs/selected28nodes1819refs14pairs/currentcombinedrootTests/fullharness/exactbasecontributor/scoped/history/sharedregistry/site/actualthreePNGpixelchecks pass. All10811IDsURLs/twocanonicalhighlightscuratedsourcecards/threenotation preserved. Actual preparation import/readercomment failures and pre-use renderer corrections retained/versioned, no mathematical/header/oldreceipt mutation. NNRealincl0 sourceconvention separatelyaccepted-with-explicit-delta; negativeL0Dobstruction visible, no unrestrictedrealL equivalence. NineOTHERChapter1mainrelativecontract gaps unwaived.

Legacyqueue0 is not Chapter2 mandatorytotal/completion. Adjacent2D abs(x1) nondifferentiability/Lemma2.31/OSD/linearization/Example2.32/unitanalysis/remainingChapter1/2maintext/nineChapter1gaps/necessaryappendices REQUIRED; Chapter2totalnull/incomplete,3-16unenumerated,totalGoalACTIVE. No merge/deploy/mainlive/retirement. Checkoutretained; DIRECTfinalclean/head/rawaudit before next scopedtask.
''')
fixed(True);print('Actual bounded Lipschitz draftPR',pr['number'],'delivered; GoalACTIVE/finalDIRECTpending.')
