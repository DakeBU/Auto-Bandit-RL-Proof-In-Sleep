"""Prepare scoped reviewable draft PR after actual package acceptance."""
from pathlib import Path
import json,hashlib,ast
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'native-acceptance-overlay-v1.json')['status']=='passed'
assert load(run/'committed-raw-audit-v1.json')['status']=='passed'
accepted=load(run/'accepted-decision-v1.json');reg=load(run/'registry-v1.json')
assert accepted['source_package_accepted'] and not accepted['goal_complete']
body='''The closed/proper source packet distinguishes real-threshold sublevel closedness from finite-value feasibility. This revalidates Definitions2.16/2.18, Examples2.17/2.19 and the required unnumbered closedness/lower-semicontinuity equivalence on printed16/PDF28 of frozen Orabona v10.

Source Euclidean and stated Hausdorff sufficient scope specialize the stronger arbitrary-topological Lean result. Real cuts and both infinite function values are preserved: the bottom strict superlevel is derived from the union of real strict superlevels and the top superlevel is empty. No convexity, properness, no-bottom or closed-epigraph substitute is assumed. The same canonical zero-on-V/top-outside indicator is reused. Its direct cuts and genuine finite witnesses prove two independent indicator equivalences; the three proofs have no mutual theorem-to-theorem value edges. SourceProper itself has no topology binder, while the actual proper-indicator iff retains TopologicalSpace E. Empty ambient/set and full-set nonemptiness boundaries remain explicit.

Four numbered anchors comprise two definitions and two examples; one unnumbered equivalence is mandatory. Three retained proofs/two complete definitions, zero new mathematical code or registry nodes. Only a leading ordinary ignored source comment and the selected closed/proper reader subtree change; exact original module bytes remain as suffix, all proof/definition tokens, three native headers, whole six-proof canary and root/Tests fixed. Seven separately reviewed reader qualifications are applied.

Validation:

- Fresh focused build, actual public bodies, whole six genuine canaries, eleven unique named axiom checks (standard-three-or-none/no sorryAx, including bottom_closed), and three separate native guards passed. Distinct automated CONTRACT/BODY/FINAL decisions recorded, requested Astra/medium; no human/external/runtime-model attestation.
- Sequential combined root9089jobs/Tests9232jobs and full harness466tests/seven existing skips passed. Fresh invocations include cached jobs, not a clean rebuild of every job.
- Actual scoped compiled graph5nodes/213direct type/value references includes two definitions, not a full/canary export. Clean lean-verified local site at SOURCE_COMMIT: five unique canonical scoped nodes/all10809oldIDsURLs/zero new nodes, site checks and actual viewed first browser viewport passed.
- Exact stacked contributor/history/task-only frontier and shadow/scoped CRLF-aware whitespace passed. Default raw diagnostics retained; real trailing-blank checks/enumerated raw exceptions/current-run * -text/raw committed audit kept. Preparation UTF8-AST and unused-helper name corrections/read-only command mistakes remain recorded; no mathematics or tests weakened. Global reference-index rewrite was not run in this bounded reuse window.

Stacked on OPEN draft#165 exactf989706461cb466bc290261f4845f113621e807d, not main. Main-relative diagnostics still lack nine other legacy production contracts. Only OnlineClosedProper migration is accepted, legacy10→9 with zero new-proof gain. Chapter1 migration/Chapter2 mandatory total remain incomplete/null; Chapters1–16 Goal stays active. No merge, deployment, main/live update or worktree retirement.

Evidence: runs/online-closed-proper-migration-20261006/{accepted-decision-v1.json,integrated-gates-overlay-v1.json,final-reader-receipt-v1.json,accepted-binding-audit-v1.json}; frozen contracts: docs/contracts/online-closed-proper-migration-v1.
'''.replace('SOURCE_COMMIT','`'+reg['source_commit']+'`')
for name,value in [('pr-body-v1.md',body),('pr-payload-v1.json',dict(title='Revalidate real-cut closedness and proper indicator source contracts',head='codex/research-online-closed-proper-migration',base='codex/research-online-huber-migration',draft=True,body=body))]:
 p=run/name;assert not p.exists()
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(value,str):f.write(value)
  else:json.dump(value,f,ensure_ascii=False,indent=2);f.write('\n')
src=Path('runs/online-huber-migration-20261006/create-pr-v1.py')
s=src.read_text(encoding='utf-8').replace('base-PR164-fresh-v1','base-PR165-fresh-v1').replace("repo+'/pulls/164'","repo+'/pulls/165'").replace('52f628a7ae699887069c5a621d301901718ed772','f989706461cb466bc290261f4845f113621e807d')
s=s.replace('codex/research-online-huber-migration','codex/research-online-closed-proper-migration').replace('codex%2Fresearch-online-huber-migration','codex%2Fresearch-online-closed-proper-migration').replace('codex/research-online-guessing-migration','codex/research-online-huber-migration')
ast.parse(s);p=run/'create-pr-v1.py';assert not p.exists();p.write_bytes(s.encode('utf-8'))
out=run/'PR-helper-before-use-v1.json';assert not out.exists();out.write_bytes((json.dumps(dict(path=p.as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=src.as_posix(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),before_first_use=True),indent=2)+'\n').encode())
print('Accepted closed/proper draft body/payload/APIhelper prepared; remote untouched.')
