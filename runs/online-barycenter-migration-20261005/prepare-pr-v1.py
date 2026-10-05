"""Prepare a reviewable draft PR only after actual bounded package acceptance."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
accepted=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert not accepted['parent_accepted'] and not accepted['goal_complete']
body='''The existing convex-barycenter reader reused kernel-lift notes for both supporting helpers and left their differing public typeclass requirements implicit. This change gives each retained result its actual scope, specifies AE equality of functional values, explains non-strict support using ambient interior, and keeps the barycenter conclusion as membership in the original potentially nonclosed set.

The three declaration headers and all original proof bytes remain fixed. The barycenter body genuinely constructs an AE proper-kernel representative, proves integrability and mean0, and strictly descends finite rank. No closedness, full ambient interior, finite support or desired-terminal oracle is added. Only a leading dependency comment and the existing `online-barycenter` reader subtree change in production; no new proof code, production definitions or registry nodes.

This is a necessary library dependency of Orabona v10 Theorem2.9, printedp11/PDF23, not three printed results or acceptance of Jensen. The affine-minorant negative-part producer and source Jensen remain separate obligations. Chapter2's mandatory total remains incomplete/null, and the Chapters1-16 Goal stays active.

Validation:

- Fresh focused/public-body elaboration and unchanged full probability canary: halfdirac1+halfdirac3, distinct vectors in a lower-dimensional nonclosed ray, actual mean(2,0) in that ray;14named standard3-or-none axiom audits including `law_probability`,3native guards.
- Combined root9088jobs, Tests9230jobs and full harness466tests/7existing skips passed. Root and Tests executions overlapped on unchanged Lean code; no sequential-build claim. Distinct automated contract, blind reconstruction and source/body/final reader roles are recorded, with no human/external/runtime-model attestation.
- Actual scoped compiled graph3nodes/544direct type/value edges, not a full/canary export. Clean lean-verified local site at SOURCE_COMMIT, shared3frozen canonical nodes and all10806old IDs/URLs retained; site checks and actual viewed first-browser-viewport passed.

Stacked on OPEN draft#160 at exact `b2b70fa8cf10095ba681eb1ff3e635c98ca2bc56`, not main. Exact stacked contributor gate passed for4production paths/1manifest; main-relative diagnostics still lack12other legacy contracts. Raw whitespace diagnostics on preserved logs remain failed; scoped code/JSON/scripts/docs passed with explicitly enumerated raw exceptions. Earlier accepted receipts remain bound through exact original-byte snapshots. No merge, deployment or worktree retirement occurred.

Evidence: `runs/online-barycenter-migration-20261005/accepted-decision-v1.json`, `integrated-gates-overlay-v1.json`, `final-reader-receipt-v1.json`, `accepted-binding-audit-v1.json`; exact contracts in `docs/contracts/online-barycenter-migration-v1`.
'''.replace('SOURCE_COMMIT','`'+reg['source_commit']+'`')
p=run/'pr-body-v1.md';assert not p.exists()
with p.open('w',encoding='utf-8',newline='\n') as f:f.write(body)
payload=dict(title='Revalidate nonclosed convex barycenter and qualify helper scopes',head='codex/research-online-barycenter-migration',base='codex/research-online-expectation-migration',draft=True,body=body)
p=run/'pr-payload-v1.json';assert not p.exists()
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(payload,f,ensure_ascii=False,indent=2);f.write('\n')
print('Scoped accepted barycenter draft PR body and structured payload prepared; no remote mutation.')
