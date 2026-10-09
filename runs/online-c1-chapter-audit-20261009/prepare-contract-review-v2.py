from common_v1 import *
fixed()
prior=[Path(r["path"]) for r in load(RUN/"prior-dependency-decisions-v1.json")["rows"]]
paths=list(CONTRACT.glob('*.json'))+list(CONTRACT.glob('*.md'))+list(CONTRACT.glob('*.lean.txt'))
paths+= [RUN/name for name in ['00_context.md','10_director-draft-v1.md','20_architect-draft-v1.md','blind-inputs-v1.json','blind-inputs-v2.json','neutral-review-packet-v1.md','neutral-review-packet-v2.md','blind-reconstruction-v1.md','blind-receipt-v1.json','blind-reconstruction-v2.md','blind-receipt-v2.json','neutral-layout-checks-v2.json','compiled-readiness-v1.json','compiled-readiness-graph-v1.json','named-public-readiness-v1.log','named-public-readiness-v1-exit.json','focused-existing-public-v1.log','focused-existing-public-v1-exit.json','export-readiness-graph-v1-exit.json','required-readiness-value-pairs-v2.json','prior-dependency-decisions-v1.json','root-source-pixel-review-v1.json','source-contract-review-packet-v1.md','readiness-pair-failure-v1.md','readiness-pair-repair-failure-v2.md']]
paths+= list(RUN.glob('source-pdf*-v1.png'))+list(RUN.glob('source-pdf*-text-v1.txt'))+prior
paths+=[Path(t['path']) for t in load(CONTRACT/'targets-v1.json')['targets']]
paths+=[Path(t['path']) for t in load(CONTRACT/'definition-context-v1.json')['definitions']]
paths+=[PDF,ROOT/'.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Defs.lean',ROOT/'BanditRLProof/OnlineLearningRegret.lean',ROOT/'Tests/OnlineLearningRegretDomainsCanary.lean',ROOT/'docs/contracts/online-book-v1/coverage.json',ROOT/'docs/contracts/online-book-v1/source-inventory.json',ROOT/'docs/contracts/online-ftl-obstruction-v1/chapter-one-source-ledger-accepted-v1.json',ROOT/'website/content/chapters.json',ROOT/'website/content/readings.json',ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json']
assert all(p.is_file() for p in paths)
indexed=rows(paths)
write(RUN/'source-contract-review-inputs-v1.json',dict(rows=indexed,fixed_input_count=len(indexed),scope='current fullC1 draft source-inventory/signature readiness and future-mutation-contract review ONLY',chapter_accepted=False,goal_complete=False))
fixed();print('Current contract/inventory review RAW inputs:',len(indexed),'50 unchanged named public statements; source count review pending.')
