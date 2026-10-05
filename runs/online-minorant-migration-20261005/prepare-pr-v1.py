"""Prepare a bounded draft PR only after actual final acceptance."""
from pathlib import Path
import json
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
accepted=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert not accepted['parent_accepted'] and not accepted['goal_complete']
body='''The existing affine-minorant reader left the finite-neighbourhood producer, the different support/minorant conclusions and actual typeclass scopes implicit. This change makes those scopes explicit, corrects the interior helper's direct dependency, and explains how the general theorem handles a nonclosed lower-dimensional domain.

Four original declaration headers and proof bytes are retained. The finite-neighbourhood helper produces global no-bottom and a negative vertical coefficient before division; the general theorem actually constructs intrinsic affine-span interior, restricts to its direction space, extends the linear map and corrects the intercept. No closedness, lsc, full ambient interior, measurable-loss or loss-differentiability premise is introduced. The first two results touch the loss at the chosen point; the last two supply only a global bound. Output slopes may be zero. All four actual types use finite-dimensional real normed spaces without supplied Borel/measure/probability/CompleteSpace/inner-product classes. Historical Borel prose is retained as stale evidence.

Only a leading dependency comment and the existing `online-minorant` reader subtree change in production. Two teaching links are curated representatives of four public results. No new proof code, production definitions or registry nodes. This is a necessary dependency of Orabona v10 Theorem2.9, printedp11/PDF23, not four printed source results or acceptance of Jensen. The source negative-part producer/Jensen probability-loss canaries remain separate; Chapter2's mandatory total stays null/incomplete and the Chapters1-16 Goal stays active.

Validation:

- Fresh focused/public-body elaboration; unchanged whole geometric canary with six proofs/one definition, coordinate loss on a nonclosed lower-dimensional ray and top outside. Eleven named standard-three-or-none axiom audits and four native guards. This is not a probability Jensen-loss canary.
- Combined root9088jobs and Tests9230jobs ran sequentially and passed; full harness466tests/seven existing skips passed. Distinct automated blind reconstruction and source/contract/body/final reader roles recorded, without human/external/runtime-model attestation.
- Actual scoped compiled graph: four nodes/896 direct type/value edges, including definition references; not full/canary export. Clean lean-verified local site at SOURCE_COMMIT; four frozen canonical nodes in the same shared registry and all10806previous IDs/URLs retained. Site checks and the viewed first browser viewport passed.

Stacked on OPEN draft#161 at exact `f68646457a12de93ee6cb8d585a4162f9f0a112c`, not main. Exact stacked contributor gate passed for four production paths/one manifest; main-relative diagnostics still lack12other legacy contracts. Raw whitespace diagnostics on preserved logs remain failed; scoped code/JSON/scripts/docs passed with enumerated raw exceptions. Earlier accepted receipts are bound through exact original-byte snapshots. No mathematical target repairs or test edits, merge, deployment or worktree retirement.

Evidence: `runs/online-minorant-migration-20261005/accepted-decision-v1.json`, `integrated-gates-overlay-v1.json`, `final-reader-receipt-v1.json`, `accepted-binding-audit-v1.json`; frozen contracts in `docs/contracts/online-minorant-migration-v1`.
'''.replace('SOURCE_COMMIT','`'+reg['source_commit']+'`')
for name,value in [('pr-body-v1.md',body),('pr-payload-v1.json',dict(title='Revalidate affine minorant producer and qualify support scopes',head='codex/research-online-minorant-migration',base='codex/research-online-barycenter-migration',draft=True,body=body))]:
 p=run/name;assert not p.exists()
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(value,str):f.write(value)
  else:json.dump(value,f,ensure_ascii=False,indent=2);f.write('\n')
print('Accepted scoped minorant draft PR body and structured payload prepared; remote not modified.')
