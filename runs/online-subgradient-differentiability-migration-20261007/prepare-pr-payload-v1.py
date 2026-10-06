"""Prepare a reviewable draft PR only after the exact source package is accepted."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
a=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
body=f'''Orabona v10 Theorem 2.22 requires genuine ambient differentiability of an extended-real function, the full singleton-subdifferential equivalence, and the gradient identity. A smooth `toReal` cast alone loses the infinite values and is insufficient. This package source-qualifies the existing eleven proof refinements and complete local-real-germ definition, preserves every statement/proof body, and publishes three diagnostic tests demonstrating that distinction. Both source directions derive properness and interior from convexity and a finite point; no stronger terminal premise is added.

The actual reverse proof uses a nonzero domain normal, local support bounds, compactness, selected support convergence and the two-inequality little-o argument. The forward proof uses actual finite-neighborhood affine contact, first-order support and derivative uniqueness. Every agreeing differentiable real representative has the same gradient. Finite-dimensional real inner-product scope, derived completeness and zero-dimensional cases are documented. These are eleven refinements of ONE printed result, with zero new production mathematical nodes.

Validation: fresh sequential post-comment root9089/Tests9234 jobs; full harness466tests/7existing skips; nine genuine canary proofs; twenty named standard kernel-foundation audits; eleven native statement guards; exact stacked contributor and scoped whitespace checks; historical raw bindings; site build/check. Cached jobs are included. The selected actual graph has21nodes/3026direct references, not a fullgraph export. Shared registry preservesALL10811old IDsURLs, addszero nodes, and linksall12 retained declarations. Four original curated reader links remain; all declarations are available on the complete module page.

The first site build failed because the curated-route field allows at mostfour entries. Reader metadata restored the originalfour, while all twelve canonical links and the full definition remain. Generator/checker and Lean contracts were unchanged; subsequent full harness/site gates passed. The initial TEST API-name error and its frozen-header proof-script repair, plus preparation failures, remain in raw evidence. Distinct automated CONTRACT/BODY/FINAL reviews accepted with explicit deltas, requested Astra/medium; no independent human/external/runtime-model attestation claim. FINAL report SHA: `{a['final_review_report_sha256']}`.

Evidence: `runs/{run.name}/accepted-decision-v1.json`, `integrated-gates-overlay-v1.json`, `final-reader-receipt-v1.json`, `reader-route-site-repair-v2.json`, `registry-v1.json`; contract: `docs/contracts/online-subgradient-differentiability-migration-v1/`. Clean applicable local site source `{reg['source_commit']}`; later delivery metadata head is separately checked.

Stacked on OPEN draftPR168 exacthead`4cf116c2ee42caa37e5a956ebbbfddfb0bc046f2`, unmerged. Only Theorem2.22 package is delivered; legacy7->6 ONLYthis module. Theorem2.23 and remaining Chapter1/2 obligations, including nine other main-relative legacy contracts, remain required. Chapter2 mandatory total remainsnull/incomplete, future3-16unenumerated, whole-book GoalACTIVE. No merge/deployment/main/live update or worktree retirement.
'''
payload=dict(title='Orabona 2.22: preserve the real germ and singleton equivalence',head='codex/research-online-subgradient-differentiability-migration',base='codex/research-online-subgradient-interior-migration',draft=True,body=body)
p=run/'pr-payload-v1.json';assert not p.exists();p.write_bytes((json.dumps(payload,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
q=run/'pr-payload-before-API-v1.json';assert not q.exists();q.write_bytes((json.dumps(dict(path=p.as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),prepared_before_API=True,actual_newlines=True,requested_action='draft creation only, unmerged'),indent=2)+'\n').encode('utf-8'))
print('Concrete accepted-package draft payload frozen; push and fresh exact-parent/duplicate checks still required.')
