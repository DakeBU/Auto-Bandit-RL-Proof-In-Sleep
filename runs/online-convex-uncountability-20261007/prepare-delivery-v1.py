"""Record an actual app-attached draft, never chapter or whole-Goal completion."""
from common_v2 import *
pr=load(RUN/'created-PR-v1.json');a=load(RUN/'accepted-decision-v1.json');reg=load(RUN/'registry-v2.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert pr['head']['ref']=='codex/research-online-convex-uncountability' and pr['base']['ref']=='codex/research-online-convex-nondifferentiability'
assert load(RUN/'base-PR177-creation-fresh-v1.json')['head']['sha']==BASE
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed' and not load(RUN/'app-attach-v1.json').get('isError',False)
for label in ['create-pr-v1-01','push-creation-v1-01','contributor-final-v1-01','scoped-diff-final-v1-01','committed-raw-audit-v1-01']:passed(label)
paths=['accepted-decision-v1.json','accepted-binding-audit-v1.json','accepted-reader-discharge-v1.json','final-reader-receipt-v4.json','native-acceptance-overlay-v1.json','integrated-gates-overlay-v1.json','registry-v2.json','committed-raw-audit-v1.json','created-PR-v1.json','pr-payload-v1.json','pr-payload-before-API-v1.json','app-attach-v1.json','pixel-review-v1.json','formula-render-v1.json']
write(RUN/'delivery-obligations-overlay-v1.json',dict(status='scoped-accepted-draft-PR-delivered',PR=pr['html_url'],number=pr['number'],creation_head=pr['head']['sha'],source_site_commit=reg['source_commit'],branch=pr['head']['ref'],exact_base_PR=177,exact_base_head=BASE,creation_state='OPEN-DRAFT-unmerged',app_attached=True,rows=[dict(path=(RUN/p).as_posix(),sha256=sha(RUN/p)) for p in paths],source_maintext_obligations=1,source_numbered_results=0,new_public_proofs=2,new_definitions=0,new_canary_proofs=4,new_registry_nodes=2,Chapter1_complete=False,chapter2_mandatory_total=None,chapter2_complete=False,goal_complete=False,merged=False,live=False,main_updated=False,remaining_required=a['remaining_required'],worktree='E:/ABRL/worktrees/research-online-book',worktree_disposition='Retained for the next required Lemma2.31/causal OSD public audit after DIRECT clean/localremoteREST/all-current-run-raw verification.',final_head_boundary='Final metadata head checked DIRECT without recursive self-head artifact.'))
write(RUN/'delivery-v1.md',f'''# Required source cardinality consequence delivered

OPEN draft PR{pr['number']}: {pr['html_url']}, app-attached and unmerged. Branch {pr['head']['ref']}; exact PR177 base {BASE}; creation head {pr['head']['sha']}; applicable clean local site source {reg['source_commit']}. Final metadata head checked DIRECT afterwards. This task has not updated canonical main/live.

Orabona v10, printed19/PDF31, required unnumbered paragraph after Theorem2.30/end2.2.1 immediately before2.2.2. Two public proofs, zero definitions: the same nondegenerate CLOSED source segment is uncountable; the same globally convex real2 function has an uncountable actual AMBIENT Frechet nondifferentiability locus. Four genuine canaries include an arbitrary countable exception-set consumer of the final theorem. No new numbered theorem, exact continuum cardinal equality, measure-zero/a.e or algorithm claim.

Distinct complete-context CONTRACT3/BODY4/FINAL4 and native acceptance pass; actual context/adapter/canary/hash guard/site-schema/raw-HTML failures retained with separately checked repairs and unchanged mathematical targets. Bounded new-leaf review inputs reference exact prior accepted dependencies; no recursive all-history acceptance claim. Root9091/Tests9238 jobs include cached jobs; current-reader full harness466 tests/7 existing skips pass. Six named standard-kernel-only audits, two frozen guards; selected6 proofnodes/624 references/10 required actual valuepairs. Exact-base contributor/scoped/task-shadow/local clean Lean-verified site/shared registry/five actual image reviews pass. Shared registry preserves10815 old IDs/URLs and adds2 nodes (10817 total). Nine OTHERChapter1 main-relative contributor gaps remain required/unwaived.

{a['remaining_required']} No merge, deployment, main/live update or retirement. Checkout retained to continue the persistent Goal after DIRECT final audit.
''')
fixed(True,True);print('Actual bounded cardinality draftPR',pr['number'],'delivered; whole GoalACTIVE/final DIRECT pending.')
