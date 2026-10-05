"""Freeze anti-anchored contract inputs after a restricted-input decoder."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert not (run/'contract-source-inputs-v1.json').exists()
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind)
assert sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
f=load(run/'draft-freeze-v1.json')
for p,h in dict(f['modules'],**f['canaries']).items():assert sha(p)==h,p
packet='''Required distinct source CONTRACT review, requested GPT-6 Astra / medium. Read contract-source-inputs-v1.json and independently rehash every raw row. Seek mismatch rather than confirm root. Scope four retained production files:22 actual proof bodies/five definitions. Audit each native header/scoped context and neutral reconstruction against Orabona v10 printed9-10/PDF21-22. This is not22 printed theorems or new proofs; body/build/package acceptance follows separately.

Required numbered anchors: Def2.2/Def2.3/Thm2.4/Examples2.5/2.6, including norm proof left as exercise. Required unnumbered domain/indicator consequences and four closure bullets are part of main text. Preserve real epigraph heights, both infinities in general convexity/domain, noBottom only in Thm2.4/toReal bridges/ordinary indicator addition, convex domain premise, strict interior weights/domain points. Real module/normed/inner-product generality is explicit generalization of finite-dimensional Euclidean source; finite coercion bridges and local helpers are refinements, not new printed assertions. No zero-collapsed infinity. Empty domains/sets/family included. Affine map arbitrary, supremum unrestricted, monotone convex composition explicitly real-valued f/g and global Monotone g.

General sums use upperAdd=-(-a+-b) with top-dominant mixed infinities and EReal zero-times-infinity=0. Orabona does NOT print this convention. Freshly hashed primary Rockafellar Conjugate Duality printed6/PDF17 supports the explicit interpretation; reject any suggestion Orabona stated it literally. Audit finite/top laws, finite-height witness equivalence, positive-scalar comparison, zero/positive split and full nonnegative coefficients. Existing spike canary refutes ordinary EReal addition closure and covers improper/disjoint-domain/zero/finite-weight cases; fresh compilation still pending. Indicator addition uses ordinary + with noBottom and does not silently become general sums.

Actual shared compiled graph reused for readiness27 nodes/2078 edges/13 required proof-value pairs; not a new export/current package gate/canary graph. All public module/canary bytes unchanged at this stage, original exact snapshots preserved.22 native fences bind actual assumptions; fence generation is NOT compilation or safe-verify. Legacy same-model reviews remain historical and cannot be relabeled independent.

Current selected Book readers supplied for mismatch audit before forthcoming scoped integration. In particular theorem2.4 plain says finite-domain conditions, which could be misread as finite cardinality; monotone composition highlight says no finite-value hypotheses introduced despite explicitly REAL-valued inputs. Foundation indicator card says closure operations remain separate required obligations even though all four have existing bodies. Identify necessary corrections rather than accepting stale reader claims. Current readers/notes have not been migrated/accepted yet. Old accepted OGD/FTL artifacts and raw bindings must remain immutable if shared readers later change; task-local supersession snapshots required.

Whole Chapters1-16 Goal active; Chapter2 total exact main-text obligation count still under source audit, mandatory_total=null. This bounded contract does not enumerate/accept the whole chapter. Standalone problems optional, formal main results exercise proofs mandatory; no Chapter3 proof writing/main/live/merge/deploy/model upgrade.

Return accepted|rejected|accepted-with-explicit-delta, seven-slot/per-target verdicts for all22 exact public names plus definition-context audit, required mathematical repairs and required future reader corrections separately. Write ONLY source-contract-review-v1.md/source-contract-receipt-v1.json here, exact reviewed_files raw SHA inventory and report path/SHA, distinct actor/scope/evidence limits. Source CONTRACT verdict now, not old-body or integration acceptance; no input edits/human or external review/runtime model attestation.'''
write('source-review-packet-v1.md',packet)
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-convex-migration-v1').rglob('*') if p.is_file())
for old in ['online-convex-extended-v2','online-convex-examples-v1','online-convex-closures-v1','online-convex-sums-v1']:
    paths.update(p.as_posix() for p in (Path('docs/contracts')/old).rglob('*') if p.is_file())
for old in ['online-convex-20260914','online-convex-examples-20260914','online-convex-closures-20260914','online-convex-sums-20260914']:
    for name in ['00_context.md','04_reviewer.md','acceptance-decision.md']:
        p=Path('runs')/old/name
        assert p.is_file(),p
        paths.add(p.as_posix())
paths.update(f['modules']);paths.update(f['canaries'])
paths.update(['../research-online-ogd/tmp/pdfs/orabona-v10.pdf','tmp/rockafellar-conjugate-duality.pdf',
    'tmp/online-ogd-migration-full-graph.json','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
    'BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json',
    'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
    'docs/hierarchical_harness.md','docs/lifecycle_and_proof_frontier_hardening.md','runs/active_frontier.json',
    'tasks/ONLINE-CONVEX-MIGRATION-20261005.md','conversion-windows/ONLINE-CONVEX-MIGRATION-20261005.md',
    'proof-obligations/ONLINE-CONVEX-MIGRATION-20261005.md','website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
    'runs/online-ch2-enumeration-20261005/source-navigation-draft-v1.json','runs/online-ch2-enumeration-20261005/unnumbered-source-audit-draft-v2.json',
    'runs/online-ftl-migration-20261005/accepted-decision-v1.json'])
paths.discard((run/'contract-source-inputs-v1.json').as_posix())
for p in paths:assert Path(p).is_file(),p
write('contract-source-inputs-v1.json',dict(scope='retained convex22 headers/5 definitions; source CONTRACT only',body_package_accepted=False,
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Source CONTRACT inputs frozen:',len(paths),'raw rows; stabilization/proving remains pending.')
