"""Freeze actual final package inputs only after the separate graph gate completes."""
from pathlib import Path
import hashlib,json

run=Path(__file__).parent
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def write(name,value):
    with (run/name).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(value,str):f.write(value+'\n')
        else:json.dump(value,f,indent=2);f.write('\n')
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json']:
    d=json.loads((run/name).read_text(encoding='utf-8'))
    assert d['verdict']=='accepted-with-explicit-delta'
    for row in d['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']
    assert sha(d['report'])==d['report_sha256']
for gate in ['root-01','Tests-01','full-harness-02','contributor-exact-base-01',
             'proof-graph-compact-01','graph-verify-01','site-final02-build',
             'site-final02-check','registry-final02','browser-final02']:
    assert json.loads((run/(gate+'-exit.json')).read_text())['exit_code']==0,gate
packet="""Required distinct source reviewer, GPT-6 Astra / medium. Final package/source-reader review only; no chapter/book acceptance. Search for mismatch rather than confirming root. Rehash final-reader-inputs.json exact raw rows and original source173/body317 receipts, preserved unchanged. Check all22 native frozen headers, four context definitions/alias,30 actual canary proofs,62 named actual axiom records. Actual finite-history conjugacy is an induction on the existing causal SupportPolicy history; inspect current/past loss transformation and selection after observation. Coordinate y=x/c, f'(y)=f(cy), g'=cg, eta'=eta/c^2, whole-space only, loss unit unchanged. No independent canonical choice equivariance, arbitrary constrained-domain transport, loss-unit transport or future-informed learner claimed. Structural identities allow arbitrary eta and EReal values; finite sharp regret producer requires positive eta, proper full-space supports and actual played legality. It retains the negative endpoint, reuses actual policy regret_fixed, and is not a desired-bound consumer. Abstract additive unit exponents differ from numerical trajectory; real-gradient chain is proved. Actual c1000 affine example has corrected eta1/1e6, good=-1/1000 versus unchanged-eta bad=-1000 and physical -1 versus -1e6, not a universal worse-regret claim. c0 cancellation excluded, c1/T0/T1 and source1/sqrt0 boundary are explicit.

Inspect separate public/focused/root9086/Tests9226/full02 466tests7existing skips, applicable contributor8 production paths/one contract,22 fences,26 actual exported graph nodes/21 actual proof-value pairs. Preserve full01 untracked-module failure, body05 beta rewrite failure and GBK-print fallout after captured child output, canary01/02, invalid native kind proof, mistaken exporter --help actual stackoverflow, compact repair, author-book-map quote syntax and site01 six-entry route rejection. Scoped diff excludes ONLY this task raw compiler .log whitespace; full diff failed, no proof/schema/JSON exceptions. Global SGB remains untouched. Native task-local statuses are distinct from runtime Goal.

Official site-final02 source_commit70c63cac7efa59d2a892b563d8affee4266be610 source_dirty=false lean_verified=true;26 unique canonical nodes/native hashes,10764 old IDs/URLs preserved. Two source cards are unnumbered Section2.2 argument/example, not22 printed theorems; generic source-card label is interpreted with exact captions and notes. Review primary printed21-22/PDF33-34 against cached exactv10 extract, body references and page warning. Four-entry teaching route repair only changes navigation; original six-entry mapping snapshot and failure remain. Root actually viewed screenshot first viewport; read lower HTML separately, no lowerfold pixelclaim. Single shared registry; no per-Book library. Chapter2 source inventory/older26 production migration remain mandatory; laterchapters unenumerated countsnull, wholeGoalactive. No main/live/merged/human/external review claim. Create only final-reader-review.md and final-reader-receipt.json here with verdict, seven semantic slots, required repairs, remaining gaps and exact raw input/support inventory plus report SHA. Do not edit inputs or other files."""
write('final-reader-packet.md',packet)
surfaces=['BanditRLProof.lean','BanditRLProof/OnlineUnitScaling.lean','Tests.lean',
          'Tests/OnlineUnitScalingCanary.lean','docs/contracts/online-book-v1/coverage.json',
          'docs/contracts/online-book-v1/source-inventory.json',
          'research-wiki/contribution-contracts/ONLINE-UNIT-SCALING-20261004.json',
          'website/content/books.json','website/content/chapters.json','website/content/readings.json',
          'website/content/highlights.json','website/scripts/build_site.py','website/scripts/check_site.py',
          'website/static/lean-graph.js']
paths=set(surfaces)
for receipt in ['source-contract-receipt-v1.json','public-body-receipt-v1.json']:
    d=json.loads((run/receipt).read_text(encoding='utf-8'))
    paths.update(x['path'] for x in d['reviewed_files'])
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file() and p.name not in
             {'final-reader-inputs.json','final-reader-review.md','final-reader-receipt.json'})
paths.update(p.as_posix() for p in Path('docs/contracts/online-unit-scaling-v1').rglob('*') if p.is_file())
site=Path('tmp/online-unit-scaling-site-final02')
paths.update((site/n).as_posix() for n in ['site-manifest.json','books/registry.json',
                                         'chapters/online-unit-scaling/index.html'])
paths.add('tmp/online-unit-scaling-reader-final02.png')
paths.add('runs/active_frontier.json')
for p in paths:assert Path(p).is_file(),p
write('final-reader-inputs.json',dict(scope='C2 unit argument and actual causal transport only; chapter/book incomplete',
    canonical_surfaces=surfaces,site_commit='70c63cac7efa59d2a892b563d8affee4266be610',
    site_source_clean=True,public_proofs=22,public_registry_nodes=26,canary_theorems=30,
    actual_axiom_names=62,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print(json.dumps(dict(status='frozen-final-reader',rows=len(paths),canonical_surfaces=len(surfaces))))
