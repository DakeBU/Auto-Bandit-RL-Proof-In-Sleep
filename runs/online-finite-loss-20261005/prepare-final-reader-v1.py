"""Freeze final reader/package inputs after actual integrated/site gates."""
from pathlib import Path
import hashlib,json,re
run=Path(__file__).parent;site=Path('tmp/online-finite-loss-site-v2')
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
gates=['root-v1-01','Tests-v1-01','full-harness-v2-01','contributor-exact-v3-01','scoped-diff-v2-01',
    'site-build-v2','site-check-v2','registry-v2-01','browser-v2-01','history-bindings-v2-01',
    'named-axioms-v1-01','candidate-frontier-shadow-v1']
for n in gates:assert load(run/(n+'-exit.json'))['exit_code']==0,n
raw=(run/'full-harness-v2-01.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
reg=load(run/'registry-v2.json');assert reg['new_registry_nodes']==2 and reg['preserved_base_node_ids_and_urls']==10804
manifest=load(site/'site-manifest.json');assert manifest['source_dirty'] is False and manifest['lean_verified'] is True
write('final-reader-packet-v1.md','''Distinct final SOURCE/READER/PACKAGE review requested GPT-6 Astra / medium. Seek mismatch, independently rehash every final-reader-inputs-v1.json row and resolve current/prior review-history raw bindings via history-binding-audit-v2.json and preserved snapshot chains. Two genuine new public proofs/eight canaries only. Source unnumbered necessary finite-loss condition refined explicitly to iff; arbitrary carrier generalization. Finite-real witnesses exclude both infinities, no noBottom premise on primary criterion. Separate below-top effective-domain equality keeps global hbot; ordinary bottom-dominant EReal addition retained, NOT upperAdd. Membership alone never sufficient for infinite original f. Public bottom/empty-set domain counterexample and top-inside/nonconstant-finite/finite-outside/empty-V tests meaningful. Distinct contract and body review accepted-with-explicit-delta, not prior final package acceptance.

Current shared root9088/Tests9230/full466tests7existing skips passed; ten named standard3 axioms/two native guards/frozen headers unchanged. Fresh scoped actual compiled-environment graph2nodes121edges/three project proof-value pairs, NOT full graph/canary export. Same shared library/root/toolchain/registry. Source-qualified Book source card and two highlights added only to online-convex; all other structured Book subtrees preserved. Original four representative teaching-route links retained. Sitev2 clean source613e5cb209ffd19dc0a0f41ffa1044a7a19ad8ea is earlier than later evidence/metadata HEAD; do not confuse source commit with final delivery head. Canonical generated website/_site never edited. Two unique frozen canonical node hashes/OnlineLearning membership match; every10804oldID/URL preserved. Actual isolated Edge first viewport observed; no unobserved lower-pixel claim. Exact stacked base OPENdraft PR156 f6daaa68927398df9fd8b756f3ac2dd28247c1e7; five changed production surfaces/one contribution contract passed. Main-relative check still FAIL16 legacy contract migrations; no direct main/live readiness.

Failures literal and preserved: (1) original private empty tactic parser errors, probev2 skip gives only two intentional unsolved goals, never compiled proof; (2) first focused canary negative coercion rewrite failed, proof-only repair preserves all eight headers; (3) body preparationv1 parser failed to strip newlines from standard multiline axiom output, v2 fixes only parser and checks existing artifacts rather than overwriting; (4) first full harness failed440tests/7skips because new production source was untracked, commit source then actual rerun passed466/7, no test disabling or frozen anonymous edits; (5) first contributor exact failed because test files wrongly listed among protected production surfaces, separate preserved manifest snapshot and schema repair remove those two affected_files entries only, tests still present; (6) full git whitespace fails on raw command logs, scoped gate checks all other code/JSON/docs with exactly enumerated raw output/original snapshots exceptions; (7) sitev1 build rejected six teaching links (max4), restore original four links without removing new source/highlights/canonical nodes, clean sitev2 actual pass. Current source/body fixed raw inputs immutable; prior accepted OGD/FTL/convex reports/receipts unchanged, exact original five shared surfaces preserved and explicit snapshots resolve drift. No math terminal weakening.

Contribution manifest describes earlier candidate fields; integrated-gates-overlay-v2 and eventual additive accepted overlay carry later evidence without changing frozen prior phase records. No single runtime enforces all paper prompts/files/roles; native CLI gates and conventions distinct. Whole Chapters1-16 Goal active/unbudgeted; Chapter2 totalnull/incomplete, legacy remaining19 unchanged by this new proof package, all future required chapters/appendix dependencies still mandatory. Standalone exercises optional, formal main results with exercise proofs mandatory. Close only the precise finite-loss consequence plus its separate domain helper, not all draft18auditgroups or Chapter2. PR delivery follows immutable package decision; no merge/deploy/retirement/model upgrade/human/external/independently attested runtime claim.

Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json here: actor.task=/root/source_reviewer, verdict accepted|rejected|accepted-with-explicit-delta, required_repairs, seven slots, per-reader/noBottom/refinement audit, actual gate/repair/snapshot/registry audit, reviewed_files exactSHA and report path/SHA, remaining mandatory obligations. Do not edit inputs.''')
surfaces=['BanditRLProof/OnlineConstraintFiniteLoss.lean','Tests/OnlineConstraintFiniteLossCanary.lean','BanditRLProof.lean','Tests.lean',
    'website/content/books.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
    'research-wiki/contribution-contracts/online-finite-loss-20261005.json','lean-toolchain','lakefile.lean','lake-manifest.json',
    'runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json']
paths=set(surfaces);paths.update(row['path'] for row in load(run/'body-review-inputs-v1.json')['rows'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update((site/p).as_posix() for p in ['site-manifest.json','books/registry.json','chapters/online-convex/index.html'])
paths.add('tmp/online-finite-loss-reader-v2.png')
for c in reg['checks']:paths.add((site/c['url'].lstrip('/')).as_posix())
# Registry URLs may identify a directory; bind the actual generated reader file.
paths={str(Path(p)/'index.html') if Path(p).is_dir() else p for p in paths}
for p in paths:assert Path(p).is_file(),p
write('final-reader-inputs-v1.json',dict(scope='two new finite-loss/domain endpoints only',canonical_surfaces=surfaces,
    site_commit=manifest['source_commit'],new_proofs=2,canary_proofs=8,mandatory_chapter_total=None,chapter_complete=False,goal_complete=False,
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Final reader/package fixed inputs:',len(paths),'raw rows; exact clean site',manifest['source_commit'])
